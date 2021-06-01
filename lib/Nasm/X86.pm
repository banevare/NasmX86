#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I. -I/home/phil/perl/cpan/AsmC/lib/
#-------------------------------------------------------------------------------
# Generate X86 assembler code using Perl as a macro pre-processor.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation
package Nasm::X86;
our $VERSION = "20210528";
use warnings FATAL => qw(all);
use strict;
use Carp qw(confess cluck);
use Data::Dump qw(dump);
use Data::Table::Text qw(confirmHasCommandLineCommand currentDirectory fff fileMd5Sum fileSize findFiles firstNChars formatTable fpe fpf genHash lll owf pad readFile stringsAreNotEqual stringMd5Sum temporaryFile);
use Asm::C qw(:all);
use feature qw(say current_sub);

my %rodata;                                                                     # Read only data already written
my %rodatas;                                                                    # Read only string already written
my %subroutines;                                                                # Subroutines generated
my @rodata;                                                                     # Read only data
my @data;                                                                       # Data
my @bss;                                                                        # Block started by symbol
my @text;                                                                       # Code
my @extern;                                                                     # External symbols imports for linking with C libraries
my @link;                                                                       # Specify libraries which to link against in the final assembly stage
my $interpreter = q(-I /usr/lib64/ld-linux-x86-64.so.2);                        # The ld command needs an interpreter if we are linking with C.

my $stdin  = 0;                                                                 # File descriptor for standard input
my $stdout = 1;                                                                 # File descriptor for standard output
my $stderr = 2;                                                                 # File descriptor for standard error

my %Registers;                                                                  # The names of all the registers
my %RegisterContaining;                                                         # The largest register containing a register

BEGIN{
  my %r = (    map {$_=>[ 8,  '8'  ]}  qw(al bl cl dl r8b r9b r10b r11b r12b r13b r14b r15b r8l r9l r10l r11l r12l r13l r14l r15l sil dil spl bpl ah bh ch dh));
     %r = (%r, map {$_=>[16,  's'  ]}  qw(cs ds es fs gs ss));
     %r = (%r, map {$_=>[16,  '16' ]}  qw(ax bx cx dx r8w r9w r10w r11w r12w r13w r14w r15w si di sp bp));
     %r = (%r, map {$_=>[32,  '32a']}  qw(eax  ebx ecx edx esi edi esp ebp));
     %r = (%r, map {$_=>[32,  '32b']}  qw(r8d r9d r10d r11d r12d r13d r14d r15d));
     %r = (%r, map {$_=>[80,  'f'  ]}  qw(st0 st1 st2 st3 st4 st5 st6 st7));
     %r = (%r, map {$_=>[64,  '64' ]}  qw(rax rbx rcx rdx r8 r9 r10 r11 r12 r13 r14 r15 rsi rdi rsp rbp rip rflags));
     %r = (%r, map {$_=>[64,  '64m']}  qw(mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7));
     %r = (%r, map {$_=>[128, '128']}  qw(xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm30 xmm31));
     %r = (%r, map {$_=>[256, '256']}  qw(ymm0 ymm1 ymm2 ymm3 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm30 ymm31));
     %r = (%r, map {$_=>[512, '512']}  qw(zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm30 zmm31));
     %r = (%r, map {$_=>[64,  'm'  ]}  qw(k0 k1 k2 k3 k4 k5 k6 k7));

  %Registers = %r;                                                              # Register names

  my sub registerContaining($@)
   {my ($r, @r) = @_;                                                           # Register, contents
    $RegisterContaining{$r} = $r;                                               # A register contains itself
    $RegisterContaining{$_} = $r for @r;                                        # Registers contained by a register
   }

  registerContaining("k$_")                                            for 0..7;
  registerContaining("zmm$_",   "ymm$_", "xmm$_")                      for 0..31;
  registerContaining("r${_}x", "e${_}x", "${_}x",  "${_}l",  "${_}h")  for qw(a b c d);
  registerContaining("r${_}",  "r${_}l", "r${_}w", "r${_}b", "r${_}d") for 8..15;
  registerContaining("r${_}p", "e${_}p", "${_}p",  "${_}pl")           for qw(s b);
  registerContaining("r${_}i", "e${_}i", "${_}i", "${_}il")            for qw(s d);
  my @i0 = qw(popfq pushfq rdtsc ret syscall);                                  # Zero operand instructions

  my @i1 = split /\s+/, <<END;                                                  # Single operand instructions
bswap call dec idiv  inc jmp ja jae jb jbe jc jcxz je jecxz jg jge jl jle
jna jnae jnb jnbe jnc jne jng jnge jnl jnle jno jnp jns jnz jo jp jpe jpo jrcxz
js jz neg not seta setae setb setbe setc sete setg setge setl setle setna setnae
setnb setnbe setnc setne setng setnge setnl setno setnp setns setnz seto setp
setpe setpo sets setz pop push
END

  my @i2 =  split /\s+/, <<END;                                                 # Double operand instructions
add and bt btc btr bts
cmova cmovae cmovb cmovbe cmovc cmove cmovg cmovge cmovl cmovle
cmovna cmovnae cmovnb cmp
imul
kmov knot kortest ktest lea lzcnt mov movdqa
or popcnt shl shr sub test tzcnt
vcvtudq2pd vcvtuqq2pd vcvtudq2ps vmovdqu vmovdqu32 vmovdqu64 vmovdqu8
vpcompressd vpcompressq vpexpandd vpexpandq vpxorq xchg xor
vmovd vmovq
mulpd
pslldq psrldq
vsqrtpd
vmovdqa32 vmovdqa64
END
# print STDERR join ' ', sort @i2; exit;

  my @i2qdwb =  split /\s+/, <<END;                                             # Double operand instructions which have qdwb versions
vpbroadcast
END

  my @i3 =  split /\s+/, <<END;                                                 # Triple operand instructions
bzhi
kadd kand kandn kor kshiftl kshiftr kunpck kxnor kxor

vdpps
vprolq
vgetmantps
vaddd
vmulpd vaddpd
END

  my @i3qdwb =  split /\s+/, <<END;                                             # Triple operand instructions which have qdwb versions
pinsr pextr vpinsr vpextr vpadd vpsub vpmull
END

  my @i4 =  split /\s+/, <<END;                                                 # Quadruple operand instructions
END

  my @i4qdwb =  split /\s+/, <<END;                                             # Quadruple operand instructions which have qdwb versions
vpcmpu
END

  if (1)                                                                        # Add variants to mask instructions
   {my @k2  = grep {m/\Ak/} @i2; @i2  = grep {!m/\Ak/} @i2;
    my @k3  = grep {m/\Ak/} @i3; @i3  = grep {!m/\Ak/} @i3;
    for my $s(qw(b w d q))
     {push @i2, $_.$s for grep {m/\Ak/} @k2;
      push @i3, $_.$s for grep {m/\Ak/} @k3;
     }
   }

  if (1)                                                                        # Add qdwb versions of instructions
   {for my $o(@i2qdwb)
     {push @i2, $o.$_ for qw(b w d q);
     }
    for my $o(@i3qdwb)
     {push @i3, $o.$_ for qw(b w d q);
     }
    for my $o(@i4qdwb)
     {push @i4, $o.$_ for qw(b w d q);
     }
   }

  for my $r(sort keys %r)                                                       # Create register definitions
   {if (1)
     {my $s = "sub $r\{q($r)\}";
      eval $s;
      confess "$s$@ "if $@;
     }
    if (1)
     {my $b = $r{$r}[0] / 8;
      my $s = "sub ${r}Size\{$b}";
      eval $s;
      confess "$s$@ "if $@;
     }
   }

  my %v = map {$$_[1]=>1} values %r;
  for my $v(sort keys %v)                                                       # Types of register
   {my @r = grep {$r{$_}[1] eq $v} sort keys %r;
    my $s = "sub registers_$v\{".dump(\@r)."}";
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take zero operands
   {my $s = '';
    for my $i(@i0)
      {my $I = ucfirst $i;
       $s .= <<END;
       sub $I()
        {\@_ == 0 or confess "No arguments allowed";
         my \$s = '  ' x scalar(my \@d = caller);
         push \@text, qq(\${s}$i\\n);
        }
END
     }
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take one operand
   {my $s = '';
    for my $i(@i1)
      {my $I = ucfirst $i;
       $s .= <<END;
       sub $I(\$)
        {my (\$target) = \@_;
         \@_ == 1 or confess "One argument required";
         my \$s = '  ' x scalar(my \@d = caller);
         push \@text, qq(\${s}$i \$target\\n);
        }
END
     }
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take two operands
   {my $s = '';
    for my $i(@i2)
      {my $I = ucfirst $i;
       $s .= <<END;
       sub $I(\$\$)
        {my (\$target, \$source) = \@_;
         \@_ == 2 or confess "Two arguments required";
         Keep(\$target)    if "$i" =~ m(\\Amov\\Z) and \$Registers{\$target};
         KeepSet(\$source) if "$i" =~ m(\\Amov\\Z) and \$Registers{\$source};
         my \$s = '  ' x scalar(my \@d = caller);
         push \@text, qq(\${s}$i \$target, \$source\\n);
        }
END
     }
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take three operands
   {my $s = '';
    for my $i(@i3)
      {my $I = ucfirst $i;
       $s .= <<END;
       sub $I(\$\$\$)
        {my (\$target, \$source, \$bits) = \@_;
         \@_ == 3 or confess "Three arguments required";
         my \$s = '  ' x scalar(my \@d = caller);
         push \@text, qq(\${s}$i \$target, \$source, \$bits\\n);
        }
END
     }
    eval "$s$@";
    confess $@ if $@;
   }

  if (1)                                                                        # Instructions that take four operands
   {my $s = '';
    for my $i(@i4)
      {my $I = ucfirst $i;
       $s .= <<END;
       sub $I(\$\$\$\$)
        {my (\$target, \$source, \$bits, \$zero) = \@_;
         \@_ == 4 or confess "Four arguments required";
         my \$s = '  ' x scalar(my \@d = caller);
         push \@text, qq(\${s}$i \$target, \$source, \$bits, \$zero\\n);
        }
END
     }
    eval "$s$@";
    confess $@ if $@;
   }
 }

sub ClearRegisters(@);                                                          # Clear registers by setting them to zero
sub Comment(@);                                                                 # Insert a comment into the assembly code
sub DComment(@);                                                                # Insert a comment into the data section
sub RComment(@);                                                                # Insert a comment into the read only data section
sub KeepFree(@);                                                                # Free registers so that they can be reused
sub Keep(@);                                                                    # Mark free registers so that they are not updated until we Free them or complain if the register is already in use.
sub KeepPop(@);                                                                 # Reset the status of the specified registers to the status quo ante the last push
sub KeepPush(@);                                                                # Push the current status of the specified registers and then mark them as free
sub KeepReturn(@);                                                              # Pop the specified register and mark it as in use to effect a subroutine return with this register.
sub PeekR($);                                                                   # Peek at the register on top of the stack
sub PopR(@);                                                                    # Pop a list of registers off the stack
sub PopRR(@);                                                                   # Pop a list of registers off the stack without tracking
sub PrintOutMemory;                                                             # Print the memory addressed by rax for a length of rdi
sub PrintOutRegisterInHex(@);                                                   # Print any register as a hex string
sub PrintOutStringNL(@);                                                        # Print a constant string to stdout followed by new line
sub PrintString($@);                                                            # Print a constant string to the specified channel
sub PushR(@);                                                                   # Push a list of registers onto the stack
sub PushRR(@);                                                                  # Push a list of registers onto the stack without tracking
sub Syscall();                                                                  # System call in linux 64 format

#D1 Data                                                                        # Layout data

my $Labels = 0;
sub Label                                                                       #P Create a unique label
 {"l".++$Labels;                                                                # Generate a label
 }

sub SetLabel($)                                                                 # Set a label in the code section
 {my ($l) = @_;                                                                 # Label
  push @text, <<END;                                                            # Define bytes
  $l:
END
  $l                                                                            # Return label name
 }

sub Ds(@)                                                                       # Layout bytes in memory and return their label
 {my (@d) = @_;                                                                 # Data to be laid out
  my $d = join '', @_;
     $d =~ s(') (\')gs;
  my $l = Label;
  push @data, <<END;                                                            # Define bytes
  $l: db  '$d';
END
  $l                                                                            # Return label
 }

sub Rs(@)                                                                       # Layout bytes in read only memory and return their label
 {my (@d) = @_;                                                                 # Data to be laid out
  my $d = join '', @_;
     $d =~ s(') (\')gs;
  my $D = $rodatas{$d};
  return $D if defined $D;                                                      # Data already exists so return it
  my $l = Label;
  my @e;
  for my $e(split //, $d)
   {if ($e =~ m(\A(\n|\t)\Z)) {push @e, ord($e)} else {push @e, qq('$e')}
   }
  my $e = join ', ', @e;
  $rodatas{$e} = $l;                                                            # Record label
  push @rodata, <<END;                                                          # Define bytes
  $l: db  $e, 0;
END
  $l                                                                            # Return label
 }

sub Dbwdq($@)                                                                   #P Layout data
 {my ($s, @d) = @_;                                                             # Element size, data to be laid out
  my $d = join ', ', @d;
  my $l = Label;
  push @data, <<END;
  $l: d$s $d
END
  $l                                                                            # Return label
 }

sub Db(@)                                                                       # Layout bytes in the data segment and return their label
 {my (@bytes) = @_;                                                             # Bytes to layout
  Dbwdq 'b', @_;
 }
sub Dw(@)                                                                       # Layout words in the data segment and return their label
 {my (@words) = @_;                                                             # Words to layout
  Dbwdq 'w', @_;
 }
sub Dd(@)                                                                       # Layout double words in the data segment and return their label
 {my (@dwords) = @_;                                                            # Double words to layout
  Dbwdq 'd', @_;
 }
sub Dq(@)                                                                       # Layout quad words in the data segment and return their label
 {my (@qwords) = @_;                                                            # Quad words to layout
  Dbwdq 'q', @_;
 }

sub Rbwdq($@)                                                                   #P Layout data
 {my ($s, @d) = @_;                                                             # Element size, data to be laid out
  my $d = join ', ', @d;                                                        # Data to be laid out
  if (my $c = $rodata{$d})                                                      # Data already exists so return it
   {return $c
   }
  my $l = Label;                                                                # New data - create a label
  push @rodata, <<END;                                                          # Save in read only data
  $l: d$s $d
END
  $rodata{$d} = $l;                                                             # Record label
  $l                                                                            # Return label
 }

sub Rb(@)                                                                       # Layout bytes in the data segment and return their label
 {my (@bytes) = @_;                                                             # Bytes to layout
  Rbwdq 'b', @_;
 }
sub Rw(@)                                                                       # Layout words in the data segment and return their label
 {my (@words) = @_;                                                             # Words to layout
  Rbwdq 'w', @_;
 }
sub Rd(@)                                                                       # Layout double words in the data segment and return their label
 {my (@dwords) = @_;                                                            # Double words to layout
  Rbwdq 'd', @_;
 }
sub Rq(@)                                                                       # Layout quad words in the data segment and return their label
 {my (@qwords) = @_;                                                            # Quad words to layout
  Rbwdq 'q', @_;
 }

sub Float32($)                                                                  # 32 bit float
 {my ($float) = @_;                                                             # Float
  "__float32__($float)"
 }

sub Float64($)                                                                  # 64 bit float
 {my ($float) = @_;                                                             # Float
  "__float64__($float)"
 }

my $Pi = "3.141592653589793238462";

sub Pi32 {Rd(Float32($Pi))}                                                     # Pi as a 32 bit float
sub Pi64 {Rq(Float64($Pi))}                                                     # Pi as a 64 bit float

#D1 Registers                                                                   # Operations on registers

#D2 Save and Restore                                                            # Saving and restoring registers via the stack

my @syscallSequence = qw(rax rdi rsi rdx r10 r8 r9);                            # The parameter list sequence for system calls

sub SaveFirstFour(@)                                                            # Save the first 4 parameter registers making any parameter registers read only
 {my (@keep) = @_;                                                              # Registers to mark as read only
  my $N = 4;
  PushR $_ for @syscallSequence[0..$N-1];
  Keep @keep;                                                                   # Mark any parameters as read only
  $N * &RegisterSize(rax);                                                      # Space occupied by push
 }

sub RestoreFirstFour()                                                          # Restore the first 4 parameter registers
 {my $N = 4;
  PopR $_ for reverse @syscallSequence[0..$N-1];
 }

sub RestoreFirstFourExceptRax()                                                 # Restore the first 4 parameter registers except rax so it can return its value
 {my $N = 4;
  PopR $_ for reverse @syscallSequence[1..$N-1];
  Add rsp, 1*RegisterSize(rax);
  KeepReturn rax;
 }

sub RestoreFirstFourExceptRaxAndRdi()                                           # Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values
 {my $N = 4;
  PopR $_ for reverse @syscallSequence[2..$N-1];
  Add rsp, 2*RegisterSize(rax);
  KeepReturn rax, rdi;
 }

sub SaveFirstSeven()                                                            # Save the first 7 parameter registers
 {my $N = 7;
  PushR $_ for @syscallSequence[0..$N-1];
  $N * 1*RegisterSize(rax);                                                     # Space occupied by push
 }

sub RestoreFirstSeven()                                                         # Restore the first 7 parameter registers
 {my $N = 7;
  PopR $_ for reverse @syscallSequence[0..$N-1];
 }

sub RestoreFirstSevenExceptRax()                                                # Restore the first 7 parameter registers except rax which is being used to return the result
 {my $N = 7;
  PopR $_ for reverse @syscallSequence[1..$N-1];
  Add rsp, 1*RegisterSize(rax);
  KeepReturn rax;
 }

sub RestoreFirstSevenExceptRaxAndRdi()                                          # Restore the first 7 parameter registers except rax and rdi which are being used to return the results
 {my $N = 7;
  PopR $_ for reverse @syscallSequence[2..$N-1];
  Add rsp, 2*RegisterSize(rax);                                                 # Skip rdi and rax
  KeepReturn rax, rdi;
 }

sub ReorderSyscallRegisters(@)                                                  # Map the list of registers provided to the 64 bit system call sequence
 {my (@registers) = @_;                                                         # Registers
  PushR  @syscallSequence[0..$#registers];
  PushRR @registers;
  PopRR  @syscallSequence[0..$#registers];
 }

sub UnReorderSyscallRegisters(@)                                                # Recover the initial values in registers that were reordered
 {my (@registers) = @_;                                                         # Registers
  PopR  @syscallSequence[0..$#registers];
 }

my @xmmRegisters = map {"xmm$_"} 0..31;                                         # The xmm registers

sub ReorderXmmRegisters(@)                                                      # Map the list of xmm registers provided to 0-31
 {my (@registers) = map {"xmm$_"} @_;                                           # Registers
  my    @r = @xmmRegisters; $#r = $#registers;
  PushRR @r, @registers;
  PopRR  @r;
 }

sub UnReorderXmmRegisters(@)                                                    # Recover the initial values in the xmm registers that were reordered
 {my (@registers) = @_;                                                         # Registers
  my   @r = @xmmRegisters; $#r = $#registers;
  PopRR @r;
 }

sub RegisterSize($)                                                             # Return the size of a register
 {my ($r) = @_;                                                                 # Register

  eval "${r}Size()";
 }

sub ClearRegisters(@)                                                           # Clear registers by setting them to zero
 {my (@registers) = @_;                                                         # Registers
  for my $r(@registers)                                                         # Each register
   {Keep $r;                                                                    # Register must not already be in use
    my $size = RegisterSize $r;
    Xor    $r, $r     if $size == 8 and $r !~ m(\Ak);
    Kxorq  $r, $r, $r if $size == 8 and $r =~ m(\Ak);
    Vpxorq $r, $r     if $size  > 8;
   }
 }

sub SetRegisterToMinusOne($)                                                    # Set the specified register to -1
 {my ($register) = @_;                                                          # Register to set
  @_ == 1 or confess;
  &Copy($register, -1);
 }

sub SetMaskRegister($$$)                                                        # Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere
 {my ($mask, $start, $length) = @_;                                             # Mask register to set, register containing start position or 0 for position 0, register containing end position
  @_ == 3 or confess;

  PushR my @save = (r15, r14);
  Mov r15, -1;
  if ($start)                                                                   # Non zero start
   {Mov  r14, $start;
    Bzhi r15, r15, r14;
    Not  r15;
    Add  r14, $length;
   }
  else                                                                          # Starting at zero
   {Mov r14, $length;
   }
  Bzhi r15, r15, r14;
  Kmovq $mask, r15;
  PopR @save;
 }

sub SetZF()                                                                     # Set the zero flag
 {Cmp rax, rax;
 }

sub ClearZF()                                                                   # Clear the zero flag
 {PushR rax;
  Mov rax, 1;
  Cmp rax, 0;
  PopR rax;
 }

#D2 Tracking                                                                    # Track the use of registers so that we do not accidently use unset registers or write into registers that are already in use.

my %Keep;                                                                       # Registers to keep
my %KeepStack;                                                                  # Registers keep stack across PushR and PopR

sub Keep(@)                                                                     # Mark free registers so that they are not updated until we Free them or complain if the register is already in use.
 {my (@target) = @_;                                                            # Registers to keep
  for my $target(@target)
   {my $r = $RegisterContaining{$target};                                       # Containing register
    if (my $l = $Keep{$r})                                                      # Check whether the register is already in use
     {say STDERR $l;
      confess "$r reset";
     }
    eval {confess "$r set"};
    $Keep{$r} = $@;
   }
  $target[0]                                                                    # Return first register
 }

sub KeepSet($)                                                                  # Confirm that the specified registers are in use
 {my ($target) = @_;                                                            # Registers to keep
  my $r = $RegisterContaining{$target};                                         # Containing register
  confess "No such register: $target\n" unless $r;
  $Keep{$r}                                                                     # Confirm that the register is already in use
 }

sub KeepPush(@)                                                                 # Push the current status of the specified registers and then mark them as free
 {my (@target) = @_;                                                            # Registers to keep
  for my $target(@target)
   {my $r = $RegisterContaining{$target};                                       # Containing register
    push $KeepStack{$r}->@*, $Keep{$r};                                         # Check whether the register is already in use
   }
  KeepFree @target;
 }                                                                              # Mark them as free

sub KeepPop(@)                                                                  # Reset the status of the specified registers to the status quo ante the last push
 {my (@target) = @_;                                                            # Registers to keep
  for my $target(@target)
   {my $r = $RegisterContaining{$target};                                       # Containing register
    if (my $s = $KeepStack{$r})                                                 # Stack for register
     {if (@$s)                                                                  # Stack of previous statuses
       {$Keep{$r} = pop @$s;                                                    # Reload prior status
       }
      else                                                                      # Stack empty
       {confess "Cannot restore $target as stack is empty";
       }
     }
    else                                                                        # Stack empty
     {confess "Cannot restore $target as never stacked";
     }
   }
 }                                                                              # Mark them as free

sub KeepReturn(@)                                                               # Pop the specified register and mark it as in use to effect a subroutine return with this register.
 {my (@target) = @_;                                                            # Registers to return
  KeepPop @target;
  for my $target(@target)
   {Keep $target unless KeepSet $target;                                        # Mark as use in use unless already in use at this level
   }
 }                                                                              # Mark them as free

sub KeepFree(@)                                                                 # Free registers so that they can be reused
 {my (@target) = @_;                                                            # Registers to free
  for my $target(@target)
   {my $r = $RegisterContaining{$target};                                       # Containing register
       $r or confess "No such register: $target";
    delete $Keep{$r};
   }
  $target[0]                                                                    # Return first register
 }

#D2 Arithmetic                                                                  # Arithmetic operations on registers

sub Copy($$)                                                                    # Copy the source to the target register
 {my ($target, $source) = @_;                                                   # Target register, source expression

  $Registers{$source} and !$Keep{$source} and confess "$source not set";        # Check that the register has been initialized

  if ($target =~ m(\A(x|y|z)mm\d{1,2}\Z))                                       # Copy x|y|z mm register
   {Keep $target;
    Vmovdqu64 $target, $source;
   }
  else                                                                          # Normal register
   {Mov $target, $source;
   }
  $target                                                                       # Return register containing result
 }

sub MaximumOfTwoRegisters($$$)                                                  # Return in the specified register the value in the second register if it is greater than the value in the first register
 {my ($result, $first, $second) = @_;                                           # Result register, first register, second register
  Cmp $first, $second;
  &IfGt(sub {Mov $result, $first;  KeepFree $result},
        sub {Mov $result, $second; KeepFree $result});
  $result                                                                       # Result register
 }

sub MinimumOfTwoRegisters($$$)                                                  # Return in the specified register the value in the second register if it is less than the value in the first register
 {my ($result, $first, $second) = @_;                                           # Result register, first register, second register
  Cmp $first, $second;
  &IfLt(sub {Mov $result, $first;  KeepFree $result},
        sub {Mov $result, $second; KeepFree $result});
  $result                                                                       # Result register
 }

sub Increment($;$)                                                              # Increment the specified register
 {my ($target, $amount) = @_;                                                   # Target register, optional amount if not 1
  @_ >= 1 && @_ <= 2 or confess "Nothing to increment";
  KeepSet $target;
  if (@_ == 1)
   {Inc $target;                                                                # Increment register
   }
  else
   {Add $target, $amount;                                                       # Increment register by specified amount
   }
  $target                                                                       # Return register containing result
 }

sub Decrement($;$)                                                              # Decrement the specified register
 {my ($target, $amount) = @_;                                                   # Target register, optional amount if not 1
  @_ >= 1 && @_ <= 2 or confess "Nothing to decrement";
  KeepSet $target;
  if (@_ == 1)
   {Dec $target;                                                                # Increment register
   }
  else
   {Sub $target, $amount;                                                       # Increment register by specified amount
   }
  $target                                                                       # Return register containing result
 }

sub Plus($@)                                                                    # Add the last operands and place the result in the first operand
 {my ($target, @source) = @_;                                                   # Target register, source registers
  @_ > 1 or confess "Nothing to add";

  my $s = shift @source;
  Mov $target, $s unless $target eq $s;                                         # Move first source to target unless they are the same register
  my %source = map {$_=>1} @source;                                             # Hash of sources
  confess "Target $target in source list" if $source{$target};                  # Cannot have target on rhs as well
  Add $target, shift @source while @source;                                     # Add remaining sources
  $target                                                                       # Return register containing result
 }

sub Minus($$$)                                                                  # Subtract the third operand from the second operand and place the result in the first operand
 {my ($target, $s1, $s2) = @_;                                                  # Target register, register to subtract from, register to subtract
  @_ == 3 or confess;

  if ($target ne $s1 and $target ne $s2)                                        # Target different from sources
   {Mov $target, $s1;
    Sub $target, $s2;
   }
  elsif ($target eq $s1)                                                        # Target is to be subtracted from
   {Sub $target, $s2;
   }
  elsif ($target eq $s2)                                                        # Target is amount to subtract
   {Neg $target;
    Add $target, $s1;
   }
  else                                                                          # All the same
   {confess "Use ClearRegisters instead";
   }
  $target                                                                       # Return register containing result
 }

#D2 Zmm                                                                         # Operations on zmm registers

sub InsertIntoXyz($$$)                                                          # Shift and insert the specified word, double, quad from rax or the contents of xmm0 into the specified xyz register at the specified position shifting data above it to the left towards higher order bytes.
 {my ($reg, $unit, $pos) = @_;                                                  # Register to insert into, width of insert, position of insert in units from least significant byte starting at 0

  Keep my $k = k7;                                                              # Choose a mask register
  PushR $reg;                                                                   # Save register to be modified
  Kxnorq $k, $k, $k;                                                            # Mask to all ones
  Kshiftlq $k, $k, $pos * $unit;                                                # Zero mask data we are going to keep in position

  my $a = $unit == 2 ? q(ax) : $unit == 4 ? q(eax): $unit == 8 ? q(rax) : xmm0; # Source of inserted value
  my $u = $unit < 16 ? \&Mov : \&Vmovdqu8;                                      # Move instruction
  &$u("[rsp+$pos*$unit-$unit]", $a);                                            # Insert data into stack
  Vmovdqu8 "${reg}{$k}", "[rsp-$unit]";                                         # Reload data shifted over
  Add rsp, RegisterSize $reg;                                                   # Skip over target register on stack
  KeepFree $k;                                                                  # Release mask register
 }

sub LoadTargetZmmFromSourceZmm($$$$$)                                           # Load bytes into the numbered target zmm register at a register specified offset with source bytes from a numbered source zmm register at a specified register offset for a specified register length.
 {my ($target, $targetOffset, $source, $sourceOffset, $length) = @_;            # Number of zmm register to load, register containing start or 0 if from the start, numbered source zmm register, register containing length, optional offset from stack top
  @_ == 5 or confess;
  SetMaskRegister(k7, $targetOffset, $length);                                  # Set mask for target
  PushRR "zmm$source";                                                          # Stack source
  Sub rsp, $targetOffset;                                                       # Position stack for target
  Add rsp, $sourceOffset;                                                       # Position stack for source
  Vmovdqu8 "zmm${target}{k7}", "[rsp]";                                         # Read from stack
  Add rsp, $targetOffset;                                                       # Restore stack from target
  Sub rsp, $sourceOffset;                                                       # Restore stack from source
 }

sub LoadZmmFromMemory($$$$)                                                     # Load bytes into the numbered target zmm register at a register specified offset with source bytes from memory addressed by a specified register for a specified register length from memory addressed by a specified register.
 {my ($target, $targetOffset, $length, $source) = @_;                           # Number of zmm register to load, register containing start or 0 if from the start, register containing length, register addressing memory to load from
  @_ == 4 or confess;
  Comment "Load Target Zmm from Memory";
  SetMaskRegister(k7, $targetOffset, $length);                                  # Set mask for target
  PushR r15;
  Mov r15, $source;
  Sub r15, $targetOffset;                                                       # Position memory for target
  Vmovdqu8 "zmm${target}{k7}", "[r15]";                                         # Read from memory
  Add $targetOffset, $length;                                                   # Increment position in target
  Add $source,       $length;                                                   # Increment position in source
  PopR r15;
 }

#D1 Structured Programming                                                      # Structured programming constructs

sub If($$;$)                                                                    # If
 {my ($jump, $then, $else) = @_;                                                # Jump op code of variable, then - required , else - optional
  @_ >= 2 && @_ <= 3 or confess;

  if (ref($jump))                                                               # Variable reference - non zero then then else else
   {PushR r15;
    Mov r15, $jump->address;
    Cmp r15,0;
    PopR r15;
    __SUB__->(q(Jz), $then, $else);
   }
  elsif (!$else)                                                                # No else
   {Comment "if then";
    my $end = Label;
    push @text, <<END;
    $jump $end;
END
    &$then;
    SetLabel $end;
   }
  else                                                                          # With else
   {Comment "if then else";
    my $endIf     = Label;
    my $startElse = Label;
    push @text, <<END;
    $jump $startElse
END
    &$then;
    Jmp $endIf;
    SetLabel $startElse;
    &$else;
    SetLabel  $endIf;
   }
 }

sub IfEq(&;&)                                                                   # If equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jne), $then, $else);                                                     # Opposite code
 }

sub IfNe(&;&)                                                                   # If not equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Je), $then, $else);                                                      # Opposite code
 }

sub IfNz(&;&)                                                                   # If not zero execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jz), $then, $else);                                                      # Opposite code
 }

sub IfLt(&;&)                                                                   # If less than execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jge), $then, $else);                                                     # Opposite code
 }

sub IfLe(&;&)                                                                   # If less than or equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jg), $then, $else);                                                      # Opposite code
 }

sub IfGt(&;&)                                                                   # If greater than execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jle), $then, $else);                                                     # Opposite code
 }

sub IfGe(&;&)                                                                   # If greater than or equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jl), $then, $else);                                                      # Opposite code
 }

sub For(&$$$)                                                                   # For - iterate the body as long as register is less than limit incrementing by increment each time
 {my ($body, $register, $limit, $increment) = @_;                               # Body, register, limit on loop, increment on each iteration
  @_ == 4 or confess;
  Comment "For $register $limit";
  my $start = Label;
  my $end   = Label;
  SetLabel $start;
  Cmp $register, $limit;
  Jge $end;

  &$body;

  if ($increment == 1)
   {Inc $register;
   }
  else
   {Add $register, $increment;
   }
  Jmp $start;
  SetLabel $end;
 }

sub ForIn(&$$$$)                                                                # For - iterate the full body as long as register plus increment is less than than limit incrementing by increment each time then increment the last body for the last non full block.
 {my ($full, $last, $register, $limit, $increment) = @_;                        # Body for full block, body for last block , register, limit on loop, increment on each iteration
  @_ == 5 or confess;
  Comment "For $register $limit";
  my $start = Label;
  my $end   = Label;

  SetLabel $start;                                                              # Start of loop
  PushR $register;                                                              # Save the register so we can test that there is still room
  Add   $register, $increment;                                                  # Add increment
  Cmp   $register, $limit;                                                      # Test that we have room for increment
  PopR  $register;                                                              # Remove increment
  Jge   $end;

  &$full;

  Add $register, $increment;                                                    # Increment for real
  Jmp $start;
  SetLabel $end;

  Sub $limit, $register;                                                        # Size of remainder
  IfNz                                                                          # Non remainder
   {&$last;                                                                     # Process remainder
   }
 }

sub ForEver(&)                                                                  # Iterate for ever
 {my ($body) = @_;                                                              # Body to iterate
  @_ == 1 or confess;
  Comment "ForEver";
  my $start = Label;                                                            # Start label
  my $end   = Label;                                                            # End label

  SetLabel $start;                                                              # Start of loop

  &$body($start, $end);                                                         # End of loop

  Jmp $start;                                                                   # Restart loop
  SetLabel $end;                                                                # End of loop
 }

sub Macro(&%)                                                                   # Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub
 {my ($body, %options) = @_;                                                    # Body, options.

  @_ >= 1 or confess;
  my $name = $options{name} // [caller(1)]->[3];                                # Optional name for subroutine reuse
  if ($name and !$options{keepOut} and my $n = $subroutines{$name}) {return $n} # Return the label of a pre-existing copy of the code

  my $start = Label;
  my $end   = Label;
  Jmp $end;
  SetLabel $start;
  &$body;
  Ret;
  SetLabel $end;
  $subroutines{$name} = $start if $name;                                        # Cache a reference to the generated code if a name was supplied

  $start
 }

sub Subroutine(&%)                                                              # Create a subroutine that can be called in assembler code
 {my ($body, %options) = @_;                                                    # Body, options.
  @_ >= 1 or confess;
  my $name    = $options{name} // [caller(1)]->[3];                             # Subroutine name
  my %in      = ($options{in}  // {})->%*;                                      # Input parameters
  my %out     = ($options{out} // {})->%*;                                      # Output parameters
  my %io      = ($options{io}  // {})->%*;                                      # Update u=in place parameters
  my $comment = $options{comment};                                              # Optional comment describing sub
  Comment "Subroutine " .($comment) if $comment;                                # Assemble comment

  if ($name and my $n = $subroutines{$name}) {return $n}                        # Return the label of a pre-existing copy of the code

  my $scope = &Scope;                                                           # Create a new scope

  my %p;
  my sub checkSize($$)                                                          # Check the size of a parameter
   {my ($name, $size) = @_;
    confess "Invalid size $size for parameter: $name" unless $size =~ m(\A(1|2|3|4|5|6)\Z);
    $p{$name} = Variable($size, $name);
   }

  my sub checkIo($$)                                                            # Check an io parameter
   {my ($name, $size) = @_;
    confess "Invalid size $size for parameter: $name" unless $size =~ m(\A(1|2|3|4|5|6)\Z);
    $p{$name} = Vr($name, $size);                                               # Make a reference
   }

  checkSize($_, $in {$_}) for keys %in;
  checkSize($_, $out{$_}) for keys %out;
  checkIo  ($_, $io {$_}) for keys %io;

  my $start = Label;                                                            # Jump over code
  my $end   = Label;
  Jmp $end;

  SetLabel $start;
  &$body({%p});                                                                 # Code with parameters
  Ret;
  SetLabel $end;

  &ScopeEnd;                                                                    # End scope
  defined($name) or confess "Name missing";
  $subroutines{$name} = genHash(__PACKAGE__."::Sub",                            # Subroutine definition
    start     => $start,
    scope     => $scope,
    name      => $name,
    comment   => $comment,
    in        => {%in},
    out       => {%out},
    io        => {%io},
    variables => {%p},
   );
 }

sub Nasm::X86::Sub::call($%)                                                    # Call a sub passing it some parameters
 {my ($sub, @parameters) = @_;                                                  # Subroutine descriptor, parameter variables

  my %p;
  while(@parameters)                                                            # Namify parameters supplied by the caller
   {my $p = shift @parameters;                                                  # Check parameters provided by caller
    my $n = ref($p) ? $p->name : $p;
    defined($n) or confess "No name or variable";
    my $v = ref($p) ? $p       : shift @parameters;
    unless ($sub->in->{$n} or $sub->out->{$n} or $sub->io->{$n})
     {my @t;
      push @t, map {[q(in),  $_]} keys $sub->in ->%*;
      push @t, map {[q(io),  $_]} keys $sub->io ->%*;
      push @t, map {[q(out), $_]} keys $sub->out->%*;
      my $t = formatTable([@t], [qw(Type Name)]);
      confess "Invalid parameter: '$n'\n$t";
     }
    $p{$n} = $v;
   }

  for my $p(keys $sub->in->%*)                                                  # Load input parameters
   {confess "Missing in parameter: $p" unless my $v = $p{$p};
    $sub->variables->{$p}->copy($v);
   }

  for my $p(keys $sub->io->%*)                                                  # Load io parameters
   {confess "Missing io parameter: $p" unless my $v = $p{$p};
    if ($v->isRef)                                                              # If we already have a reference we can just copy the content
     {$sub->variables->{$p}->copy($v);
     }
    else                                                                        # Otherwise make a reference
     {$sub->variables->{$p}->copyAddress($v);
     }
   }

  Call $$sub{start};                                                            # Call the sub routine
  for my $p(keys $sub->out->%*)                                                 # Load output parameters
   {confess qq(Missing output parameter: "$p") unless my $v = $p{$p};
    $v->copy($sub->variables->{$p});
   }
 }

sub cr(&@)                                                                      # Call a subroutine with a reordering of the registers.
 {my ($body, @registers) = @_;                                                  # Code to execute with reordered registers, registers to reorder
  ReorderSyscallRegisters   @registers;
  &$body;
  UnReorderSyscallRegisters @registers;
 }

sub cxr(&@)                                                                     # Call a subroutine with a reordering of the xmm registers.
 {my ($body, @registers) = @_;                                                  # Code to execute with reordered registers, registers to reorder
  ReorderXmmRegisters   @registers;
  &$body;
  UnReorderXmmRegisters @registers;
 }

sub Comment(@)                                                                  # Insert a comment into the assembly code
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  push @text, <<END;
; $c
END
 }

sub DComment(@)                                                                 # Insert a comment into the data segment
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  push @data, <<END;
; $c
END
 }

sub RComment(@)                                                                 # Insert a comment into the read only data segment
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  push @data, <<END;
; $c
END
 }

#D1 Print                                                                       # Print

sub PrintNL($)                                                                  # Print a new line to stdout  or stderr
 {my ($channel) = @_;                                                           # Channel to write on
  @_ == 1 or confess;
  my $a = Rb(10);
  Comment "Write new line to $channel";

  Call Macro
   {SaveFirstFour;
    Mov rax, 1;
    Mov rdi, $channel;
    Mov rsi, $a;
    Mov rdx, 1;
    Syscall;
    RestoreFirstFour()
   } name => qq(PrintNL$channel);
 }

sub PrintErrNL()                                                                # Print a new line to stderr
 {@_ == 0 or confess;
  PrintNL($stderr);
 }

sub PrintOutNL()                                                                # Print a new line to stderr
 {@_ == 0 or confess;
  PrintNL($stdout);
 }

sub PrintString($@)                                                             # Print a constant string to the specified channel
 {my ($channel, @string) = @_;                                                  # Channel, Strings
  @_ >= 1 or confess;

  my $c = join ' ', @string;
  my $l = length($c);
  my $a = Rs($c);

  SaveFirstFour;
  Comment "Write to channel  $channel, the string: $c";
  Mov rax, 1;
  Mov rdi, $channel;
  Mov rsi, $a;
  Mov rdx, $l;
  Syscall;
  RestoreFirstFour();
 }

sub PrintErrString(@)                                                           # Print a constant string to stderr.
 {my (@string) = @_;                                                            # String
  PrintString($stderr, @string);
 }

sub PrintOutString(@)                                                           # Print a constant string to stdout.
 {my (@string) = @_;                                                            # String
  PrintString($stdout, @string);
 }

sub PrintErrStringNL(@)                                                         # Print a constant string followed by a new line to stderr
 {my (@string) = @_;                                                            # Strings
  PrintErrString(@string);
  PrintErrNL;
 }

sub PrintOutStringNL(@)                                                         # Print a constant string followed by a new line to stdout
 {my (@string) = @_;                                                            # Strings
  PrintOutString(@string);
  PrintOutNL;
 }

sub hexTranslateTable                                                           #P Create/address a hex translate table and return its label
 {my $h = '0123456789ABCDEF';
  my @t;
  for   my $i(split //, $h)
   {for my $j(split //, $h)
     {push @t, "$i$j";
     }
   }
   Rs @t                                                                        # Constant strings are only saved if they are unique, else a read only copy is returned.
 }

sub PrintRaxInHex($)                                                            # Write the content of register rax in hexadecimal in big endian notation to the specified channel
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess;
  Comment "Print Rax In Hex on channel: $channel";
  my $hexTranslateTable = hexTranslateTable;

  my $sub = Macro
   {SaveFirstFour rax;                                                          # Rax is a parameter
    Mov rdx, rax;                                                               # Content to be printed
    Mov rdi, 2;                                                                 # Length of a byte in hex
    KeepFree rax;

    for my $i(0..7)
     {my $s = 8*$i;
      KeepFree rax;
      Mov rax, rdx;
      Shl rax, $s;                                                              # Push selected byte high
      Shr rax, 56;                                                              # Push select byte low
      Shl rax, 1;                                                               # Multiply by two because each entry in the translation table is two bytes long
      Lea rax, "[$hexTranslateTable+rax]";
      PrintMemory($channel);
      PrintString($channel, ' ') if $i % 2 and $i < 7;
     }
    RestoreFirstFour;
   } name => "PrintOutRaxInHexOn$channel";

  Call $sub;
 }

sub PrintErrRaxInHex()                                                          # Write the content of register rax in hexadecimal in big endian notation to stderr
 {@_ == 0 or confess;
  PrintRaxInHex($stderr);
 }

sub PrintOutRaxInHex()                                                          # Write the content of register rax in hexadecimal in big endian notation to stderr
 {@_ == 0 or confess;
  PrintRaxInHex($stdout);
 }

sub PrintOutRaxInReverseInHex                                                   # Write the content of register rax to stderr in hexadecimal in little endian notation
 {@_ == 0 or confess;
  Comment "Print Rax In Reverse In Hex";
  Push rax;
  Bswap rax;
  PrintOutRaxInHex;
  Pop rax;
 }

sub PrintRegisterInHex($@)                                                      # Print the named registers as hex strings
 {my ($channel, @r) = @_;                                                       # Channel to print on, names of the registers to print
  @_ >= 2 or confess;

  for my $r(@r)                                                                 # Each register to print
   {Comment "Print register $r in Hex on channel: $channel";

    Call Macro
     {PrintString($channel,  sprintf("%6s: ", $r));                             # Register name

      my sub printReg(@)                                                        # Print the contents of a register
       {my (@regs) = @_;                                                        # Size in bytes, work registers
        my $s = RegisterSize $r;                                                # Size of the register
        PushR  @regs;                                                           # Save work registers
        PushRR $r;                                                              # Place register contents on stack - might be a x|y|z - without tracking
        PopRR  @regs;                                                           # Load work registers without tracking
        for my $i(keys @regs)                                                   # Print work registers to print input register
         {my $R = $regs[$i];
          if ($R !~ m(\Arax))
           {PrintString($channel, "  ");                                        # Separate blocks of bytes with a space
            Keep $R; KeepFree rax;
            Mov rax, $R
           }
          PrintRaxInHex($channel);                                              # Print work register
          PrintString($channel, " ") unless $i == $#regs;
         }
        PopR @regs;                                                             # Balance the single push of what might be a large register
       };
      if    ($r =~ m(\A[kr])) {printReg qw(rax)}                                # 64 bit register requested
      elsif ($r =~ m(\Ax))    {printReg qw(rax rbx)}                            # xmm*
      elsif ($r =~ m(\Ay))    {printReg qw(rax rbx rcx rdx)}                    # ymm*
      elsif ($r =~ m(\Az))    {printReg qw(rax rbx rcx rdx r8 r9 r10 r11)}      # zmm*

      PrintNL($channel);
     } name => "PrintOutRegister${r}InHexOn$channel";                           # One routine per register printed
   }
 }

sub PrintErrRegisterInHex(@)                                                    # Print the named registers as hex strings on stderr
 {my (@r) = @_;                                                                 # Names of the registers to print
  PrintRegisterInHex $stderr, @r;
 }

sub PrintOutRegisterInHex(@)                                                    # Print the named registers as hex strings on stdout
 {my (@r) = @_;                                                                 # Names of the registers to print
  PrintRegisterInHex $stdout, @r;
 }

sub PrintOutRipInHex                                                            #P Print the instruction pointer in hex
 {@_ == 0 or confess;
  my @regs = qw(rax);
  my $sub = Macro
   {PushR @regs;
    my $l = Label;
    push @text, <<END;
$l:
END
    Lea rax, "[$l]";                                                            # Current instruction pointer
    PrintOutString "rip: ";
    PrintOutRaxInHex;
    PrintOutNL;
    PopR @regs;
   } name=> "PrintOutRipInHex";

  Call $sub;
 }

sub PrintOutRflagsInHex                                                         #P Print the flags register in hex
 {@_ == 0 or confess;
  my @regs = qw(rax);

  my $sub = Macro
   {PushR @regs;
    Pushfq;
    Pop rax;
    PrintOutString "rfl: ";
    PrintOutRaxInHex;
    PrintOutNL;
    PopR @regs;
   } name=> "PrintOutRflagsInHex";

  Call $sub;
 }

sub PrintOutRegistersInHex                                                      # Print the general purpose registers in hex
 {@_ == 0 or confess;

  my $sub = Macro
   {PrintOutRipInHex;
    PrintOutRflagsInHex;

    my @regs = qw(rax);
    PushR @regs;

    my $w = registers_64();
    for my $r(sort @$w)
     {next if $r =~ m(rip|rflags);
      if ($r eq rax)
       {Pop rax;
        Push rax
       }
      PrintOutString reverse(pad(reverse($r), 3)).": ";
      Keep $r unless KeepSet $r ; KeepFree rax;
      Mov rax, $r;
      PrintOutRaxInHex;
      PrintOutNL;
     }
    PopR @regs;
   } name=> "PrintOutRegistersInHex";

  Call $sub;
 }

sub PrintOutZF                                                                  # Print the zero flag without disturbing it
 {@_ == 0 or confess;

  Pushfq;
  IfNz {PrintOutStringNL "ZF=0"} sub {PrintOutStringNL "ZF=1"};
  Popfq;
 }

#D1 Variables                                                                   # Variable definitions and operations

#D2 Scopes                                                                      # Each variable is contained in a scope in an effort to detect references to out of scope variables

my $ScopeCurrent;                                                               # The current scope - being the last one created

sub Scope(*)                                                                    # Create and stack a new scope and continue with it as the current scope
 {my ($name) = @_;                                                              # Scope name
  my $N = $ScopeCurrent ? $ScopeCurrent->number+1 : 0;                          # Number of this scope
  my $s = genHash(__PACKAGE__."::Scope",                                        # Scope definition
    name   => $name,                                                            # Name of scope - usually the sub routine name
    number => $N,                                                               # Number of this scope
    depth  => undef,                                                            # Lexical depth of scope
    parent => undef,                                                            # Parent scope
   );
  if (my $c = $ScopeCurrent)
   {$s->parent = $c;
    $s->depth  = $c->depth + 1;
   }
  else
   {$s->depth  = 0;
   }
  $ScopeCurrent = $s;
 }

sub ScopeEnd                                                                    # End the current scope and continue with the containing parent scope
 {if (my $c = $ScopeCurrent)
   {$ScopeCurrent = $c->parent;
   }
  else
   {confess "No more scopes to finish";
   }
 }

sub Nasm::X86::Scope::contains($;$)                                             # Check that the named parent scope contains the specified child scope. If no child scope is supplied we use the current scope to check that the parent scope is currently visible
 {my ($parent, $child) = @_;                                                    # Parent scope, child scope,
  for(my $c = $child//$ScopeCurrent; $c; $c = $c->parent)                       # Ascend scope tree looking for parent
   {return 1 if $c == $parent;                                                  # Found parent so child or current scope can see the parent
   }
  undef                                                                         # Parent not found so child is not contained by the parent scope
 }

sub Nasm::X86::Scope::currentlyVisible($)                                       # Check that the named parent scope is currently visible
 {my ($scope) = @_;                                                             # Scope to check for visibility
  $scope->contains                                                              # Check that the named parent scope is currently visible
 }

#D2 Definitions                                                                 # Variable definitions

sub Variable($$;$)                                                              # Create a new variable with the specified size and name initialized via an expression
 {my ($size, $name, $expr) = @_;                                                # Size as a power of 2, name of variable, optional expression initializing variable
  $size =~ m(\A0|1|2|3|4|5|6|b|w|d|q|x|y|z\Z)i or confess "Size must be 0..6 or b|w|d|q|x|y|z";# Check size of variable

  DComment qq(Variable name: "$name", size: $size);
  my $label = $size =~ m(\A0|b\Z) ? Db(0) :                                     # Allocate space for variable
              $size =~ m(\A1|w\Z) ? Dw(0) :                                     # Allocate space for variable
              $size =~ m(\A2|d\Z) ? Dd(0) :
              $size =~ m(\A3|q\Z) ? Dq(0) :
              $size =~ m(\A4|x\Z) ? Dq(0,0) :
              $size =~ m(\A5|y\Z) ? Dq(0,0,0,0) :
              $size =~ m(\A6|z\Z) ? Dq(0,0,0,0,0,0,0,0) : undef;

  my $nSize = $size =~ tr(bwdqxyz) (0123456)r;                                  # Size of variable

  if (defined $expr)                                                            # Initialize variable if an initializer was supplied
   {my $t = "[$label]";
    if ($Registers{$expr})
     {Mov $t, $expr;
     }
    else
     {PushR r15;
      Mov r15, $expr;
      Mov $t, r15b        if $nSize == 0;
      Mov $t, r15w        if $nSize == 1;
      Mov $t, r15d        if $nSize == 2;
      Mov $t, r15         if $nSize == 3;
      PopR r15;
     }
   }

  genHash(__PACKAGE__."::Variable",                                             # Variable definition
    expr      => $expr,                                                         # Expression that initializes the variable
    label     => $label,                                                        # Address in memory
    laneSize  => undef,                                                         # Size of the lanes in this variable
    name      => $name,                                                         # Name of the variable
    purpose   => undef,                                                         # Purpose of this variable
    reference => undef,                                                         # Reference to another variable
    saturate  => undef,                                                         # Computations should saturate rather then wrap if true
    signed    => undef,                                                         # Elements of x|y|zmm registers are signed if true
    size      => $nSize,                                                        # Size of variable
   );
 }

sub Vb(*;$)                                                                     # Define a byte variable
 {my ($name, $expr) = @_;                                                       # Name of variable, initializing expression
  &Variable(0, @_)
 }

sub Vw(*;$)                                                                     # Define a word variable
 {my ($name, $expr) = @_;                                                       # Name of variable, initializing expression
  &Variable(1, @_)
 }

sub Vd(*;$)                                                                     # Define a double word variable
 {my ($name, $expr) = @_;                                                       # Name of variable, initializing expression
  &Variable(2, @_)
 }

sub Vq(*;$)                                                                     # Define a quad variable
 {my ($name, $expr) = @_;                                                       # Name of variable, initializing expression
  &Variable(3, @_)
 }

sub VxyzInit($@)                                                                # Initialize an xyz register from general purpose registers
 {my ($var, @expr) = @_;                                                        # Variable, initializing general purpose registers or undef
  if (@expr == 1 and $expr[0] =~ m(\Al))                                        # Load from the memory at the specified label
   {if ($var->size == 6)
     {PushR zmm0;
      Vmovdqu8 zmm0, "[".$expr[0]."]";
      Vmovdqu8 $var->address, zmm0;
      PopR  zmm0;
      return $var;
     }
    confess "More code needed";
   }
  my $N = 2 ** ($var->size - 3);                                                # Number of quads to fully initialize
  @expr <= $N or confess "$N initializers required";                            # Number of quads to fully initialize
  my $l = $var->label;                                                          # Label
  my $s = RegisterSize(rax);                                                    # Size of initializers
  for my $i(keys @expr)                                                         # Each initializer
   {my $o = $s * $i;                                                            # Offset
    Mov "qword[$l+$o]", $expr[$i] if $expr[$i];                                 # Move in initial value if present
   }
  $var
 }

sub Vx(*;@)                                                                     # Define an xmm variable
 {my ($name, @expr) = @_;                                                       # Name of variable, initializing expression
  VxyzInit(&Variable(4, $name), @expr);
 }

sub Vy(*;@)                                                                     # Define an ymm variable
 {my ($name, @expr) = @_;                                                       # Name of variable, initializing expression
  VxyzInit(&Variable(5, $name), @expr);
 }

sub Vz(*;@)                                                                     # Define an zmm variable
 {my ($name, @expr) = @_;                                                       # Name of variable, initializing expression
  VxyzInit(&Variable(6, $name), @expr);
 }

sub Vr(*;$)                                                                     # Define a reference variable
 {my ($name, $size) = @_;                                                       # Name of variable, variable being referenced
  my $r = &Variable(3, $name);                                                  # The referring variable is 64 bits wide
  $r->reference = $size;                                                        # Mark variable as a reference
  $r                                                                            # Size of the referenced variable
 }

#D2 Operations                                                                  # Variable operations

if (1)                                                                          # Define operator overloading for Variables
 {package Nasm::X86::Variable;
  use overload
    '+'  => \&add,
    '-'  => \&sub,
    '*'  => \&times,
    '/'  => \&divide,
    '%'  => \&mod,
   '=='  => \&eq,
   '!='  => \&ne,
   '>='  => \&ge,
    '>'  => \&gt,
   '<='  => \&le,
   '<'   => \&lt,
   '++'  => \&inc,
   '--'  => \&dec,
   '""'  => \&str,
   '&'   => \&and,
   '|'   => \&or,
   '+='  => \&plusAssign,
   '-='  => \&minusAssign,
   '='   => \&equals,
 }

sub Nasm::X86::Variable::address($;$)                                           # Get the address of a variable with an optional offset
 {my ($left, $offset) = @_;                                                     # Left variable, optional offset
  my $o = $offset ? "+$offset" : "";
  "[".$left-> label."$o]"
 }

sub Nasm::X86::Variable::copy($$)                                               # Copy one variable into another
 {my ($left, $right) = @_;                                                      # Left variable, right variable

  ref($right) =~ m(Variable) or confess "Variable required";
  my $l = $left ->address;
  my $r = $right->address;

  if ($left->size == 3 and $right->size == 3)
   {Comment "Copy parameter ".$right->name.' to '.$left->name;
    PushR my @save = (r15);
    Mov r15, $r;
    Mov $l, r15;
    PopR @save;
    return;
   }

  confess "Need more code";
 }

sub Nasm::X86::Variable::copyRef($$)                                            # Copy one variable into an referenced variable
 {my ($left, $right) = @_;                                                      # Left variable, right variable

  $left->reference           or confess "Reference required for: ".$left->name;
  ref($right) =~ m(Variable) or confess "Variable required";
  my $l = $left ->address;
  my $r = $right->address;


  if ($left->size == 3 and $right->size == 3)
   {Comment "Copy parameter ".$right->name.' to '.$left->name;
    PushR my @save = (r14, r15);
    Mov r15, $r;
    Mov r14, $l;
    Mov "[r14]", r15;
    PopR @save;
    return;
   }

  confess "Need more code";
 }

sub Nasm::X86::Variable::copyAddress($$)                                        # Copy a reference to a variable
 {my ($left, $right) = @_;                                                      # Left variable, right variable

  my $l = $left ->address;
  my $r = $right->address;

  if ($left->size == 3 and $right->size == 3)
   {Comment "Copy parameter address";
    PushR my @save = (r15);
    Lea r15, $r;
    Mov $l, r15;
    PopR @save;
    return;
   }

  confess "Need more code";
 }

sub Nasm::X86::Variable::equals($$$)                                            # Equals operator
 {my ($op, $left, $right) = @_;                                                 # Operator, left variable,  right variable
  $op
 }

sub Nasm::X86::Variable::assign($$$)                                            # Assign to the left hand side the value of the right hand side
 {my ($left, $op, $right) = @_;                                                 # Left variable, operator, right variable

  if ($left->size == 3 and !ref($right) || $right->size == 3)
   {Comment "Variable assign";
    PushR my @save = (r14, r15);
    Mov r14, $left ->address;
    Mov r15, ref($right) ? $right->address : $right;
    &$op(r14,r15);
    Mov $left ->address, r14;
    PopR @save;
    return $left;
   }
  confess "Need more code";
 }

sub Nasm::X86::Variable::plusAssign($$)                                         # Implement plus and assign
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  $left->assign(\&Add, $right);
 }

sub Nasm::X86::Variable::minusAssign($$)                                        # Implement minus and assign
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  $left->assign(\&Sub, $right);
 }

sub Nasm::X86::Variable::arithmetic($$$$)                                       # Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables
 {my ($op, $name, $left, $right) = @_;                                          # Operator, operator name, Left variable,  right variable

  my $l = $left ->address;
  my $r = ref($right) ? $right->address : $right;                               # Right can be either a variable reference or a constant

  if ($left->size == 3 and !ref($right) || $right->size == 3)                   # Vq
   {PushR my @save = (r14, r15);
    Mov r15, $l;
    if ($left->reference)                                                       # Dereference left if necessary
     {KeepFree r15;
      Mov r15, "[r15]";
     }
    Mov r14, $r;
    if (ref($right) and $right->reference)                                      # Dereference right if necessary
     {KeepFree r14;
      Mov r14, "[r14]";
     }
    &$op(r15, r14);
    my $v = Vq(join(' ', '('.$left->name, $name, (ref($right) ? $right->name : $right).')'), r15);
    PopR @save;
    return $v;
   }

  if ($left->size == 6 and ref($right) and $right->size == 6)                   # Vz
   {if ($name =~ m(add|sub))
     {PushR my @save = (zmm0, zmm1);
      Vmovdqu64 zmm0, $left->address;
      Vmovdqu64 zmm1, $right->address;
      my $l = $left->laneSize // $right->laneSize // 0;                         # Size of elements to add
      my $o = substr("bwdq", $l, 1);                                            # Size of operation
      eval "Vp$name$o zmm0, zmm0, zmm1";                                        # Add or subtract
      my $z = Vz(join(' ', $left->name, $op, $right->name));                    # Variable to hold result
      Vmovdqu64 $z->address, zmm0;                                              # Save result in variable
      PopR @save;
      return $z;
     }
   }
  confess "Need more code";
 }

sub Nasm::X86::Variable::add($$)                                                # Add the right hand variable to the left hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::arithmetic(\&Add, q(add), $left, $right);
 }

sub Nasm::X86::Variable::sub($$)                                                # Subtract the right hand variable from the left hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::arithmetic(\&Sub, q(sub), $left, $right);
 }

sub Nasm::X86::Variable::times($$)                                              # Multiply the left hand variable by the right hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::arithmetic(\&Imul, q(times), $left, $right);
 }

sub Nasm::X86::Variable::division($$$)                                          # Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side
 {my ($op, $left, $right) = @_;                                                 # Operator, Left variable,  right variable

  my $l = $left ->address;
  my $r = ref($right) ? $right->address : $right;                               # Right can be either a variable reference or a constant
  if ($left->size == 3 and ! ref($right) || $right->size == 3)
   {PushR my @regs = (rax, rdx, r15);
    Mov rax, $l;
    Mov r15, $r;
    Idiv r15;
    my $v = Vq(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), $op eq "%" ? rdx : rax);
    PopR @regs;
    return $v;
   }
  confess "Need more code";
 }

sub Nasm::X86::Variable::divide($$)                                             # Divide the left hand variable by the right hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::division("/", $left, $right);
 }

sub Nasm::X86::Variable::mod($$)                                                # Divide the left hand variable by the right hand variable and return the remainder as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::division("%", $left, $right);
 }

sub Nasm::X86::Variable::boolean($$$$)                                          # Combine the left hand variable with the right hand variable via a boolean operator
 {my ($sub, $op, $left, $right) = @_;                                           # Operator, operator name, Left variable,  right variable

  my $l = $left ->address;
  my $r = ref($right) ? $right->address : $right;                               # Right can be either a variable reference or a constant
  if ($left->size == 3 and ! ref($right) || $right->size == 3)
   {PushR r15;
    Mov r15, $l;
    Cmp r15, $r;
    KeepFree r15;
    &$sub(sub {Mov  r15, 1; KeepFree r15},
          sub {Mov  r15, 0; KeepFree r15});
    my $v = Vq(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), r15);
    PopR r15;
    return $v;
   }
  confess "Need more code";
 }

sub Nasm::X86::Variable::eq($$)                                                 # Check whether the left hand variable is equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::boolean(\&IfEq, q(eq), $left, $right);
 }

sub Nasm::X86::Variable::ne($$)                                                 # Check whether the left hand variable is not equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::boolean(\&IfNe, q(ne), $left, $right);
 }

sub Nasm::X86::Variable::ge($$)                                                 # Check whether the left hand variable is greater than or equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::boolean(\&IfGe, q(ge), $left, $right);
 }

sub Nasm::X86::Variable::gt($$)                                                 # Check whether the left hand variable is greater than the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::boolean(\&IfGt, q(gt), $left, $right);
 }

sub Nasm::X86::Variable::le($$)                                                 # Check whether the left hand variable is less than or equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::boolean(\&IfLe, q(le), $left, $right);
 }

sub Nasm::X86::Variable::lt($$)                                                 # Check whether the left hand variable is less than the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::boolean(\&IfLt, q(lt), $left, $right);
 }

sub Nasm::X86::Variable::print($)                                               # Write the value of a variable on stdout
 {my ($left) = @_;                                                              # Left variable
  PushR my @regs = (rax, rdi);
  Mov rax, $left->label;
  Mov rdi, 8;
  &PrintOutMemoryInHexNL();
  PopR @regs;
 }

sub Nasm::X86::Variable::dump($$$;$$)                                           # Dump the value of a variable to the specified channel adding an optional title and new line if requested
 {my ($left, $channel, $newLine, $title1, $title2) = @_;                        # Left variable, channel, new line required, optional leading title, optional trailing title
  @_ >= 3 or confess;
  if ($left->size == 3)                                                         # General purpose register
   {PushR my @regs = (rax, rdi);
    Mov rax, $left->label;                                                      # Address in memory
    KeepFree rax;
    if ($left->reference)
     {Mov rax, "[rax]";
      KeepFree rax;
     }
    Mov rax, "[rax]";
    confess  dump($channel) unless $channel =~ m(\A1|2\Z);
    PrintString  ($channel, $title1//$left->name.": ");
    PrintRaxInHex($channel);
    PrintString  ($channel, $title2) if defined $title2;
    PrintNL      ($channel) if $newLine;
    PopR @regs;
   }
  elsif ($left->size == 4)                                                      # xmm
   {PushR my @regs = (rax, rdi);
    my $l = $left->label;                                                       # Address in memory
    my $s = RegisterSize rax;
    Mov rax, "[$l]";
    Mov rdi, "[$l+$s]";
    &PrintErrString($title1//$left->name.": ");
    &PrintErrRaxInHex();
    &PrintErrString("  ");
    KeepFree rax;
    Mov rax, rdi;
    &PrintErrRaxInHex();
    &PrintErrNL();
    PopR @regs;
   }
 }

sub Nasm::X86::Variable::err($;$$)                                              # Dump the value of a variable on stderr
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stderr, 0, $title1, $title2);
 }

sub Nasm::X86::Variable::out($;$$)                                               # Dump the value of a variable on stdout
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stdout, 0, $title1, $title2);
 }

sub Nasm::X86::Variable::errNL($;$$)                                             # Dump the value of a variable on stderr and append a new line
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stderr, 1, $title1, $title2);
 }

sub Nasm::X86::Variable::outNL($;$$)                                             # Dump the value of a variable on stdout and append a new line
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stdout, 1, $title1, $title2);
 }

sub Nasm::X86::Variable::debug($)                                               # Dump the value of a variable on stdout with an indication of where the dump came from
 {my ($left) = @_;                                                              # Left variable
  PushR my @regs = (rax, rdi);
  Mov rax, $left->label;                                                        # Address in memory
  KeepFree rax;
  Mov rax, "[rax]";
  &PrintErrString(pad($left->name, 32).": ");
  &PrintErrRaxInHex();
  my ($p, $f, $l) = caller(0);                                                  # Position of caller in file
  &PrintErrString("               at $f line $l");
  &PrintErrNL();
  PopR @regs;
 }

sub Nasm::X86::Variable::isRef($)                                               # Check whether the specified  variable is a reference to another variable
 {my ($variable) = @_;                                                          # Variable
  my $n = $variable->name;                                                      # Variable name
  $variable->size == 3 or confess "Wrong size for reference: $n";
  $variable->reference
 }

sub Nasm::X86::Variable::setReg($$@)                                            # Set the named registers from the content of the variable
 {my ($variable, $register, @registers) = @_;                                   # Variable, register to load, optional further registers to load
  if ($variable->size == 3)                                                     # General purpose register
   {if ($variable->isRef)
     {Mov $register, $variable->address;
      KeepFree $register;
      Mov $register, "[$register]";
     }
    else
     {Mov $register, $variable->address;
     }
   }
  elsif ($variable->size == 4)                                                  # Xmm
   {Mov $register, $variable->address;
    for my $i(keys @registers)
     {Mov $registers[$i], $variable->address(($i + 1) * RegisterSize rax);
     }
   }
  else                                                                          #
   {confess "More code needed";
   }
  $register
 }

sub Nasm::X86::Variable::getReg($$@)                                            # Load the variable from the named registers
 {my ($variable, $register, @registers) = @_;                                   # Variable, register to load, optional further registers to load from
  if ($variable->size == 3)
   {if ($variable->isRef)
     {Comment "Get variable value from register";
      my $r = $register eq r15 ? r14 : r15;
      PushR $r;
      Mov $r, $variable->address;
      Mov "[$r]", $register;
      PopR $r;
     }
    else
     {Mov $variable->address, $register;
     }
   }
  elsif ($variable->size == 4)                                                  # Xmm
   {Mov $variable->address, $register;
    for my $i(keys @registers)
     {Mov $variable->address(($i + 1) * RegisterSize rax), $registers[$i];
     }
   }
  else                                                                          #
   {confess "More code needed";
   }
 }

sub Nasm::X86::Variable::incDec($$)                                             # Increment or decrement a variable
 {my ($left, $op) = @_;                                                         # Left variable operator, address of operator to perform inc or dec
  my $l = $left ->address;
  if ($left->size == 3)
   {PushR r15;
    Mov r15, $l;
    &$op(r15);
    Mov $l, r15;
    PopR r15;
    return $left;
   }
  confess "Need more code";
 }

sub Nasm::X86::Variable::inc($)                                                 # Increment a variable
 {my ($left) = @_;                                                              # Variable
  $left->incDec(\&Inc);
 }

sub Nasm::X86::Variable::dec($)                                                 # Decrement a variable
 {my ($left) = @_;                                                              # Variable
  $left->incDec(\&Dec);
 }

sub Nasm::X86::Variable::str($)                                                 # The name of the variable
 {my ($left) = @_;                                                              # Variable
  $left->name;
 }

sub Nasm::X86::Variable::min($$)                                                # Minimum of two variables
 {my ($left, $right) = @_;                                                      # Left variable, Right variable,
  PushR my @save = (r12, r14, r15);
  $left->setReg(r14);
  $right->setReg(r15);
  Cmp r14, r15;
  IfLt(sub {Mov r12, r14; KeepFree r12},
       sub {Mov r12, r15; KeepFree r12});
  my $r = Vq("Minimum(".$left->name.", ".$right->name.")", r12);
  PopR @save;
  $r
 }

sub Nasm::X86::Variable::max($$)                                                # Maximum of two variables
 {my ($left, $right) = @_;                                                      # Left variable, Right variable,
  PushR my @save = (r12, r14, r15);
  $left->setReg(r14);
  $right->setReg(r15);
  Cmp r14, r15;
  &IfGt(sub {Mov r12, r14; KeepFree r12},
        sub {Mov r12, r15; KeepFree r12});
  my $r = Vq("Maximum(".$left->name.", ".$right->name.")", r12);
  PopR @save;
  $r
 }

sub Nasm::X86::Variable::and($$)                                                # And two variables
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushR my @save = (r14, r15);
  Mov r14, 0;
  $left->setReg(r15);
  Cmp r15, 0;
  KeepFree r15;
  &IfNe (
    sub
     {$right->setReg(r15);
      Cmp r15, 0;
      &IfNe(sub {Add r14, 1});
     }
   );
  my $r = Vq("And(".$left->name.", ".$right->name.")", r14);
  PopR @save;
  $r
 }

sub Nasm::X86::Variable::or($$)                                                 # Or two variables
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushR my @save = (r14, r15);
  Mov r14, 1;
  $left->setReg(r15);
  KeepFree r14, r15;
  Cmp r15, 0;
  &IfEq (
    sub
     {$right->setReg(r15);
      Cmp r15, 0;
      &IfEq(sub {Mov r14, 0});
     }
   );
  my $r = Vq("Or(".$left->name.", ".$right->name.")", r14);
  PopR @save;
  $r
 }

sub Nasm::X86::Variable::setMask($$$)                                           # Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere
 {my ($start, $length, $mask) = @_;                                             # Variable containing start of mask, variable containing length of mask, mask register
  @_ == 3 or confess;

  PushR my @save = (r13, r14, r15);
  Mov r15, -1;
  if ($start)                                                                   # Non zero start
   {$start->setReg(r14);
    Bzhi r15, r15, r14;
    Not  r15;
    $length->setReg(r13);
    Add  r14, r13;
   }
  else                                                                          # Starting at zero
   {$length->setReg(r13);
    Mov r14, $length;
   }
  Bzhi r15, r15, r14;
  Kmovq $mask, r15;
  PopR @save;
 }

sub Nasm::X86::Variable::setZmm($$$$)                                           # Load bytes from the memory addressed by specified source variable into the numbered zmm register at the offset in the specified offset moving the number of bytes in the specified variable
 {my ($source, $zmm, $offset, $length) = @_;                                    # Variable containing the address of the source, number of zmm to load, variable containing offset in zmm to move to, variable containing length of move
  @_ == 4 or confess;
  ref($offset) && ref($length) or confess "Missing variable";                   # Need variables of offset and length
  Comment "Set Zmm $zmm from Memory";
  PushR my @save = (k7, r14, r15);
  $offset->setMask($length, k7);                                                # Set mask for target
  $source->setReg(r15);
  $offset->setReg(r14);                                                         # Position memory for target
  Sub r15, r14;                                                                 # Position memory for target
  Vmovdqu8 "zmm${zmm}{k7}", "[r15]";                                            # Read from memory
  PopR @save;
 }

sub Nasm::X86::Variable::loadZmm($$)                                            # Load bytes from the memory addressed by the specified source variable into the numbered zmm register.
 {my ($source, $zmm) = @_;                                                      # Variable containing the address of the source, number of zmm to get
  @_ == 2 or confess;
  if ($source->size == 3)                                                       # Load through memory addressed by a Vq
   {Comment "Load zmm$zmm from memory addressed by ".$source->name;
    PushR r15;
    $source->setReg(r15);
    Vmovdqu8 "zmm$zmm", "[r15]";
    PopR r15;
   }
  elsif ($source->size == 6)                                                    # Load from Vz
   {Comment "Load zmm$zmm from ".$source->name;
    Vmovdqu8 "zmm$zmm", $source->address;
   }
 }

sub Nasm::X86::Variable::saveZmm($$)                                            # Save bytes into the memory addressed by the target variable from the numbered zmm register.
 {my ($target, $zmm) = @_;                                                      # Variable containing the address of the source, number of zmm to put
  @_ == 2 or confess;
  Comment "Save zmm$zmm into memory addressed by ".$target->name;
  PushR r15;
  $target->setReg(r15);
  Vmovdqu8 "[r15]", "zmm$zmm";                                                  # Write into memory
  PopR r15;
 }

sub getBwdqFromMmAsVariable($$$)                                                # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 {my ($size, $mm, $offset) = @_;                                                # Size of get, register, offset in bytes
  @_ == 3 or confess;

  my $o;                                                                        # The offset into the mm register
  if (ref($offset))                                                             # The offset is being passed in a variable
   {my $name = $offset->name;
    Comment "Get $size at $name in $mm";
    PushR ($o = r14);
    $offset->setReg($o);
   }
  else                                                                          # The offset is being passed as a register expression
   {$o = $offset;
    Comment "Get $size at $offset in $mm";
    $offset =~ m(r15) and confess "Cannot pass offset: '$offset', in r15, choose another register";
   }

  PushR r15;
  PushRR $mm;                                                                   # Push source register

  if ($size !~ m(q))                                                            # Clear the register if necessary
   {ClearRegisters r15; KeepFree r15;
   }

  Mov r15b, "[rsp+$o]" if $size =~ m(b);                                        # Load byte register from offset
  Mov r15w, "[rsp+$o]" if $size =~ m(w);                                        # Load word register from offset
  Mov r15d, "[rsp+$o]" if $size =~ m(d);                                        # Load double word register from offset
  Mov r15,  "[rsp+$o]" if $size =~ m(q);                                        # Load register from offset
  Add rsp, RegisterSize $mm;                                                    # Pop source register

  my $v = Vq("$size at offset $offset in $mm", r15);                            # Create variable
     $v->getReg(r15);                                                           # Load variable
  PopR r15;

  PopR $o if ref($offset);                                                      # The offset is being passed in a variable

  $v                                                                            # Return variable
 }

sub getBFromXmmAsVariable($$)                                                   # Get the byte from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMmAsVariable('b', "xmm$xmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getWFromXmmAsVariable($$)                                                   # Get the word from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMmAsVariable('w', "xmm$xmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getDFromXmmAsVariable($$)                                                   # Get the double word from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMmAsVariable('d', "xmm$xmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getQFromXmmAsVariable($$)                                                   # Get the quad word from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMmAsVariable('q', "xmm$xmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getBFromZmmAsVariable($$)                                                   # Get the byte from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMmAsVariable('b', "zmm$zmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getWFromZmmAsVariable($$)                                                   # Get the word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMmAsVariable('w', "zmm$zmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getDFromZmmAsVariable($$)                                                   # Get the double word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMmAsVariable('d', "zmm$zmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getQFromZmmAsVariable($$)                                                   # Get the quad word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMmAsVariable('q', "zmm$zmm", $offset)                              # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub Nasm::X86::Variable::getBFromZmm($$$)                                       # Get the byte from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMmAsVariable('b', "zmm$zmm", $offset))             # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::getWFromZmm($$$)                                       # Get the word from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMmAsVariable('w', "zmm$zmm", $offset))             # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::getDFromZmm($$$)                                       # Get the double word from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMmAsVariable('d', "zmm$zmm", $offset))             # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::getQFromZmm($$$)                                       # Get the quad word from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMmAsVariable('q', "zmm$zmm", $offset))             # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::putBwdqIntoMm($$$$)                                    # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 {my ($content, $size, $mm, $offset) = @_;                                      # Variable with content, size of put, numbered zmm, offset in bytes
  @_ == 4 or confess;

  my $o;                                                                        # The offset into the mm register
  if (ref($offset))                                                             # The offset is being passed in a variable
   {my $name = $offset->name;
    Comment "Put $size at $name in $mm";
    PushR ($o = r14);
    $offset->setReg($o);
   }
  else                                                                          # The offset is being passed as a register expression
   {$o = $offset;
    Comment "Put $size at $offset in $mm";
    $offset =~ m(r15) and confess "Cannot pass offset: '$offset', in r15, choose another register";
   }

  PushR my @save=(r15, $mm);                                                    # Push target register
  $content->setReg(r15);
  Mov   "[rsp+$o]", r15b if $size =~ m(b);                                      # Write byte register
  Mov   "[rsp+$o]", r15w if $size =~ m(w);                                      # Write word register
  Mov   "[rsp+$o]", r15d if $size =~ m(d);                                      # Write double word register
  Mov   "[rsp+$o]", r15  if $size =~ m(q);                                      # Write register
  PopR @save;

  PopR $o if ref($offset);                                                      # The offset is being passed in a variable
 }

sub Nasm::X86::Variable::putBIntoXmm($$$)                                       # Place the value of the content variable at the byte in the numbered xmm register
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  $content->putBwdqIntoMm('b', "xmm$xmm", $offset)                              # Place the value of the content variable at the word in the numbered xmm register
 }

sub Nasm::X86::Variable::putWIntoXmm($$$)                                       # Place the value of the content variable at the word in the numbered xmm register
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  $content->putBwdqIntoMm('w', "xmm$xmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered xmm register
 }

sub Nasm::X86::Variable::putDIntoXmm($$$)                                       # Place the value of the content variable at the double word in the numbered xmm register
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  $content->putBwdqIntoMm('d', "xmm$xmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered xmm register
 }

sub Nasm::X86::Variable::putQIntoXmm($$$)                                       # Place the value of the content variable at the quad word in the numbered xmm register
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  $content->putBwdqIntoMm('q', "xmm$xmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered xmm register
 }

sub Nasm::X86::Variable::putBIntoZmm($$$)                                       # Place the value of the content variable at the byte in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $zmm =~ m(\A(0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31)\Z) or confess;
  $content->putBwdqIntoMm('b', "zmm$zmm", $offset)                              # Place the value of the content variable at the word in the numbered zmm register
 }

sub Nasm::X86::Variable::putWIntoZmm($$$)                                       # Place the value of the content variable at the word in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $zmm =~ m(\A(0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31)\Z) or confess;
  $content->putBwdqIntoMm('w', "zmm$zmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Nasm::X86::Variable::putDIntoZmm($$$)                                       # Place the value of the content variable at the double word in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $zmm =~ m(\A(0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31)\Z) or confess;
  $content->putBwdqIntoMm('d', "zmm$zmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Nasm::X86::Variable::putQIntoZmm($$$)                                       # Place the value of the content variable at the quad word in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $zmm =~ m(\A(0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31)\Z) or confess;
  $content->putBwdqIntoMm('q', "zmm$zmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Nasm::X86::Variable::confirmIsMemory($;$$)                                  #P Check that variable describes allocated memory and optionally load registers with its length and size
 {my ($memory, $address, $length) = @_;                                         # Variable describing memory as returned by Allocate Memory, register to contain address, register to contain size
  $memory->size == 4 or confess "Wrong size";
  $memory->purpose =~ m(\AAllocated memory\Z) or confess "Not a memory allocator";
  my $l = $memory->label;
  my $s = RegisterSize rax;
  Mov $address, "[$l]" if $address;                                             # Optionally load address
  Mov $length,  "[$l+$s]" if $length;                                           # Optionally load length
 }

sub Nasm::X86::Variable::clearMemory($)                                         # Clear the memory described in this variable
 {my ($memory) = @_;                                                            # Variable describing memory as returned by Allocate Memory
  PushR my @save = (rax, rdi);
  $memory->confirmIsMemory(@save);
  &ClearMemory();                                                               # Clear the memory
  PopR @save;
 }

sub Nasm::X86::Variable::copyMemoryFrom($$)                                     # Copy from one block of memory to another
 {my ($target, $source) = @_;                                                   # Variable describing the target, variable describing the source
  SaveFirstFour;
  $target->confirmIsMemory(rax, rdx);
  $source->confirmIsMemory(rsi, rdi);

  Cmp rdx, rdi;
  IfLt {PrintErrStringNL "Copy memory source is larger than target"; Exit(1)};  # Check memory sizes
  &CopyMemory();                                                                # Copy the memory
  RestoreFirstFour;
 }

sub Nasm::X86::Variable::printOutMemoryInHex($)                                 # Print allocated memory in hex
 {my ($memory) = @_;                                                            # Variable describing the memory
  PushR my @save = (rax, rdi);
  $memory->confirmIsMemory(@save);
  &PrintOutMemoryInHexNL();                                                     # Print the memory
  PopR @save;
 }

sub Nasm::X86::Variable::freeMemory($)                                          # Free the memory described in this variable
 {my ($memory) = @_;                                                            # Variable describing memory as returned by Allocate Memory
  $memory->size == 4 or confess "Wrong size";
  $memory->purpose =~ m(\AAllocated memory\Z) or confess "Not a memory allocator";
  PushR my @save = (rax, rdi);
  my $l = $memory->label;
  my $s = RegisterSize rax;
  Mov rax, "[$l]";
  Mov rdi, "[$l+$s]";
  &FreeMemory;                                                                  # Free the memory
  PopR @save;
 }

sub Nasm::X86::Variable::for($&)                                                # Iterate the body limit times.
 {my ($limit, $body) = @_;                                                      # Limit, Body
  @_ == 2 or confess;
  Comment "Variable::For $limit";
  my $index = Vq(q(index), 0);                                                  # The index that will be incremented
  my $start = Label;
  my $next  = Label;
  my $end   = Label;
  SetLabel $start;                                                              # Start of loop

  If ($index >= $limit, sub{Jge $end});                                         # Condition

  &$body($index, $start, $next, $end);                                          # Execute body

  SetLabel $next;                                                               # Next iteration
  $index++;                                                                     # Increment
  Jmp $start;
  SetLabel $end;
 }

#D1 Processes                                                                   # Create and manage processes

sub Fork()                                                                      # Fork
 {@_ == 0 or confess;
  Comment "Fork";
  Mov rax, 57;
  Syscall
 }

sub GetPid()                                                                    # Get process identifier
 {@_ == 0 or confess;
  Comment "Get Pid";

  Mov rax, 39;
  Syscall
 }

sub GetPidInHex()                                                               # Get process identifier in hex as 8 zero terminated bytes in rax
 {@_ == 0 or confess;
  Comment "Get Pid";
  my $hexTranslateTable = hexTranslateTable;

  my $sub = Macro
   {SaveFirstFour;
    Mov rax, 39;                                                                # Get pid
    Syscall;
    Mov rdx, rax;                                                               # Content to be printed
    KeepFree rax;

    ClearRegisters rax;                                                         # Save a trailing 00 on the stack
    Push ax;
    for my $i(reverse 5..7)
     {my $s = 8*$i;
      KeepFree rax, rdi;
      Mov rdi,rdx;
      Shl rdi,$s;                                                               # Push selected byte high
      Shr rdi,56;                                                               # Push select byte low
      Shl rdi,1;                                                                # Multiply by two because each entry in the translation table is two bytes long
      Mov ax, "[$hexTranslateTable+rdi]";
      Push ax;
     }
    Pop rax;                                                                    # Get result from stack
    RestoreFirstFourExceptRax;
   } name => "GetPidInHex";

  Call $sub;
 }

sub GetPPid()                                                                   # Get parent process identifier
 {@_ == 0 or confess;
  Comment "Get Parent Pid";

  Mov rax, 110;
  Syscall
 }

sub GetUid()                                                                    # Get userid of current process
 {@_ == 0 or confess;
  Comment "Get User id";

  Mov rax, 102;
  Syscall
 }

sub WaitPid()                                                                   # Wait for the pid in rax to complete
 {@_ == 0 or confess;
  Comment "WaitPid - wait for the pid in rax";

  my $sub = Macro
   {SaveFirstSeven;
    Mov rdi,rax;
    Mov rax, 61;
    Mov rsi, 0;
    Mov rdx, 0;
    Mov r10, 0;
    Syscall;
    RestoreFirstSevenExceptRax;
   } name => "WaitPid";

  Call $sub;
 }

sub ReadTimeStampCounter()                                                      # Read the time stamp counter and return the time in nanoseconds in rax
 {@_ == 0 or confess;

  my $sub = Macro
   {Comment "Read Time-Stamp Counter";
    Push rdx;
    Rdtsc;
    Shl rdx,32;
    Or rax,rdx;
    Pop rdx;
   } name => "ReadTimeStampCounter";

  Call $sub;
 }

#D1 Stack                                                                       # Manage data on the stack

#D2 Push, Pop, Peek                                                             # Generic versions of push, pop, peek

sub PushRR(@)                                                                   #P Push registers onto the stack without tracking
 {my (@r) = @_;                                                                 # Register
  for my $r(@r)
   {my $size = RegisterSize $r;
    if    ($size > 8)                                                           # Wide registers
     {Sub rsp, $size;
      Vmovdqu32 "[rsp]", $r;
     }
    elsif ($r =~ m(\Ak))                                                        # Mask as they do not respond to push
     {Sub rsp, $size;
      Kmovq "[rsp]", $r;
     }
    else                                                                        # Normal register
     {Push $r;
     }
   }
 }

sub PushR(@)                                                                    #P Push registers onto the stack
 {my (@r) = @_;                                                                 # Register
  PushRR   @r;                                                                  # Push
  KeepPush @r;                                                                  # Track
 }

sub PopRR(@)                                                                    #P Pop registers from the stack without tracking
 {my (@r) = @_;                                                                 # Register
  for my $r(reverse @r)                                                         # Pop registers in reverse order
   {my $size = RegisterSize $r;
    if    ($size > 8)
     {Vmovdqu32 $r, "[rsp]";
      Add rsp, $size;
     }
    elsif ($r =~ m(\Ak))
     {Kmovq $r, "[rsp]";
      Add rsp, $size;
     }
    else
     {Pop $r;
     }
   }
 }

sub PopR(@)                                                                     # Pop registers from the stack
 {my (@r) = @_;                                                                 # Register
  PopRR   @r;                                                                   # Pop registers from the stack without tracking
  KeepPop @r;                                                                   # Track
 }

sub PeekR($)                                                                    # Peek at register on stack
 {my ($r) = @_;                                                                 # Register
  my $size = RegisterSize $r;
  if    ($size > 8)                                                             # x|y|zmm*
   {Vmovdqu32 $r, "[rsp]";
   }
  else                                                                          # 8 byte register
   {Mov $r, "[rsp]";
   }
 }

#D2 Declarations                                                                # Declare variables and structures

#D3 Structures                                                                  # Declare a structure

sub Structure()                                                                 # Create a structure addressed by a register
 {@_ == 0 or confess;
  my $local = genHash(__PACKAGE__."::Structure",
    size      => 0,
    variables => [],
   );
 }

sub Nasm::X86::Structure::field($$;$)                                           # Add a field of the specified length with an optional comment
 {my ($structure, $length, $comment) = @_;                                      # Structure data descriptor, length of data, optional comment
  @_ >= 2 or confess;
  my $variable = genHash(__PACKAGE__."::StructureField",
    structure  => $structure,
    loc        => $structure->size,
    size       => $length,
    comment    => $comment
   );
  $structure->size += $length;                                                  # Update size of local data
  push $structure->variables->@*, $variable;                                    # Save variable
  $variable
 }

sub Nasm::X86::StructureField::addr($;$)                                        # Address a field in a structure by either the default register or the named register
 {my ($field, $register) = @_;                                                  # Field, optional address register else rax
  @_ <= 2 or confess;
  my $loc = $field->loc;                                                        # Offset of field in structure
  my $reg = $register || 'rax';                                                 # Register locating the structure
  "[$loc+$reg]"                                                                 # Address field
 }

sub All8Structure($)                                                            # Create a structure consisting of 8 byte fields
 {my ($N) = @_;                                                                 # Number of variables required
  @_ == 1 or confess;
  my $s = Structure;                                                            # Structure of specified size based on specified register
  my @f;
  my $z = RegisterSize rax;
  for(1..$N)                                                                    # Create the variables
   {push @f, $s->field($z);
   }
  ($s, @f)                                                                      # Structure, fields
 }

#D3 Stack Frame                                                                 # Declare local variables in a frame on the stack

sub LocalData()                                                                 # Map local data
 {@_ == 0 or confess;
  my $local = genHash(__PACKAGE__."::LocalData",
    size      => 0,
    variables => [],
   );
 }

sub Nasm::X86::LocalData::start($)                                              # Start a local data area on the stack
 {my ($local) = @_;                                                             # Local data descriptor
  @_ == 1 or confess;
  my $size = $local->size;                                                      # Size of local data
  Push rbp;
  Mov rbp,rsp;
  Sub rsp, $size;
 }

sub Nasm::X86::LocalData::free($)                                               # Free a local data area on the stack
 {my ($local) = @_;                                                             # Local data descriptor
  @_ == 1 or confess;
  Mov rsp, rbp;
  Pop rbp;
 }

sub Nasm::X86::LocalData::variable($$;$)                                        # Add a local variable
 {my ($local, $length, $comment) = @_;                                          # Local data descriptor, length of data, optional comment
  @_ >= 2 or confess;
  my $variable = genHash(__PACKAGE__."::LocalVariable",
    loc        => $local->size,
    size       => $length,
    comment    => $comment
   );
  $local->size += $length;                                                      # Update size of local data
  $variable
 }

sub Nasm::X86::LocalVariable::stack($)                                          # Address a local variable on the stack
 {my ($variable) = @_;                                                          # Variable
  @_ == 1 or confess;
  my $l = $variable->loc;                                                       # Location of variable on stack
  my $S = $variable->size;
  my $s = $S == 8 ? 'qword' : $S == 4 ? 'dword' : $S == 2 ? 'word' : 'byte';    # Variable size
  "${s}[rbp-$l]"                                                                # Address variable - offsets are negative per Tino
 }

sub Nasm::X86::LocalData::allocate8($@)                                         # Add some 8 byte local variables and return an array of variable definitions
 {my ($local, @comments) = @_;                                                  # Local data descriptor, optional comment
  my @v;
  for my $c(@comments)
   {push @v, Nasm::X86::LocalData::variable($local, 8, $c);
   }
  wantarray ? @v : $v[-1];                                                      # Avoid returning the number of elements accidently
 }

sub AllocateAll8OnStack($)                                                      # Create a local data descriptor consisting of the specified number of 8 byte local variables and return an array: (local data descriptor,  variable definitions...)
 {my ($N) = @_;                                                                 # Number of variables required
  my $local = LocalData;                                                        # Create local data descriptor
  my @v;
  for(1..$N)                                                                    # Create the variables
   {my $v = $local->variable(RegisterSize(rax));
    push @v, $v->stack;
   }
  $local->start;                                                                # Create the local data area on the stack
  ($local, @v)
 }

#D1 Memory                                                                      # Allocate and print memory

sub PrintMemoryInHex($)                                                         # Dump memory from the address in rax for the length in rdi on the specified channel
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess;
  Comment "Print out memory in hex on channel: $channel";

  Call Macro
   {my $size = RegisterSize rax;
    SaveFirstFour;
    Mov rsi,rax;                                                                # Position in memory
    Lea rdi,"[rax+rdi-$size+1]";                                                # Upper limit of printing with an 8 byte register
    For                                                                         # Print string in blocks
     {Mov rax, "[rsi]";
      Bswap rax;
      PrintRaxInHex($channel);
     } rsi, rdi, $size;
    RestoreFirstFour;
   } name=> "PrintOutMemoryInHexOnChannel$channel";
 }

sub PrintErrMemoryInHex                                                         # Dump memory from the address in rax for the length in rdi on stderr
 {@_ == 0 or confess;
  PrintMemoryInHex($stderr);
 }

sub PrintOutMemoryInHex                                                         # Dump memory from the address in rax for the length in rdi on stdout
 {@_ == 0 or confess;
  PrintMemoryInHex($stdout);
 }

sub PrintErrMemoryInHexNL                                                       # Dump memory from the address in rax for the length in rdi and then print a new line
 {@_ == 0 or confess;
  PrintMemoryInHex($stderr);
  PrintNL($stderr);
 }

sub PrintOutMemoryInHexNL                                                       # Dump memory from the address in rax for the length in rdi and then print a new line
 {@_ == 0 or confess;
  PrintMemoryInHex($stdout);
  PrintNL($stdout);
 }

sub PrintMemory                                                                 # Print the memory addressed by rax for a length of rdi on the specified channel
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess;

  Call Macro
   {Comment "Print memory on channel: $channel";
    SaveFirstFour rax, rdi;
    Mov rsi, rax;
    Mov rdx, rdi;
    KeepFree rax, rdi;
    Mov rax, 1;
    Mov rdi, $channel;
    Syscall;
    RestoreFirstFour();
   } name => "PrintOutMemoryOnChannel$channel";
 }

sub PrintErrMemory                                                              # Print the memory addressed by rax for a length of rdi on stderr
 {@_ == 0 or confess;
  PrintMemory($stdout);
 }

sub PrintOutMemory                                                              # Print the memory addressed by rax for a length of rdi on stdout
 {@_ == 0 or confess;
  PrintMemory($stdout);
 }

sub PrintErrMemoryNL                                                            # Print the memory addressed by rax for a length of rdi followed by a new line on stderr
 {@_ == 0 or confess;
  PrintErrMemory;
  PrintErrNL;
 }

sub PrintOutMemoryNL                                                            # Print the memory addressed by rax for a length of rdi followed by a new line on stdout
 {@_ == 0 or confess;
  PrintOutMemory;
  PrintOutNL;
 }

sub AllocateMemory(@)                                                           # Allocate the specified amount of memory via mmap and return its address
 {my (@variables) = @_;                                                         # Parameters
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Allocate memory";
    SaveFirstSeven;
    my $d = extractMacroDefinitionsFromCHeaderFile "linux/mman.h";              # mmap constants
    my $pa = $$d{MAP_PRIVATE} | $$d{MAP_ANONYMOUS};
    my $wr = $$d{PROT_WRITE}  | $$d{PROT_READ};

    Mov rax, 9;                                                                 # mmap
    $$p{size}->setReg(rsi);                                                     # Amount of memory
    Xor rdi, rdi;                                                               # Anywhere
    Mov rdx, $wr;                                                               # Read write protections
    Mov r10, $pa;                                                               # Private and anonymous map
    Mov r8,  -1;                                                                # File descriptor for file backing memory if any
    Mov r9,  0;                                                                 # Offset into file
    Syscall;
    $$p{address}->getReg(rax);                                                  # Amount of memory

    RestoreFirstSeven;
   } in => {size => 3}, out => {address=>3};

  $s->call(@variables);
 }

sub FreeMemory(@)                                                               # Free memory
 {my (@variables) = @_;                                                         # Variables
  @_ >= 2 or confess;
  Comment "Free memory";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    Mov rax, 11;                                                                # Munmap
    $$p{address}->setReg(rdi);                                                  # Address
    $$p{size}   ->setReg(rsi);                                                  # Length
    Syscall;
    RestoreFirstFour;
   } in => {size=>3, address=>3};

  $s->call(@variables);
 }

sub ClearMemory(@)                                                              # Clear memory - the address of the memory is in rax, the length in rdi
 {my (@variables) = @_;                                                         # Variables
  @_ >= 2 or confess;
  Comment "Clear memory";

  my $size = RegisterSize zmm0;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    $$p{address}->setReg(rax);
    $$p{size}   ->setReg(rdi);
    PushR zmm0;                                                                 # Pump zeros with this register
    Lea rdi, "[rax+rdi-$size]";                                                 # Address of upper limit of buffer
    ClearRegisters zmm0;                                                        # Clear the register that will be written into memory

    For                                                                         # Clear memory
     {Vmovdqu64 "[rax]", zmm0;
     } rax, rdi, $size;

    PopR zmm0;
    RestoreFirstFour;
   } in => {size => 3, address => 3};

  $s->call(@variables);
 }

sub CopyMemory(@)                                                               # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
 {my (@variables) = @_;                                                         # Variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Copy memory";
    my $source   = rsi;
    my $target   = rax;
    my $length   = rdi;
    my $copied   = rdx;
    my $transfer = r8;

    SaveFirstSeven;
    $$p{source}->setReg($source);
    $$p{target}->setReg($target);
    $$p{size}  ->setReg($length);
    ClearRegisters $copied;
    For                                                                         # Clear memory
     {Mov "r8b", "[$source+$copied]";
      Mov "[$target+$copied]", "r8b";
     } $copied, $length, 1;

    RestoreFirstSeven;
   } in => {source => 3, target => 3, size => 3};

  $s->call(@variables);
 }

#D1 Files                                                                       # Process a file

sub OpenRead()                                                                  # Open a file, whose name is addressed by rax, for read and return the file descriptor in rax
 {@_ == 0 or confess;
  Comment "Open a file for read";

  my $sub = Macro
   {my $S = extractMacroDefinitionsFromCHeaderFile "asm-generic/fcntl.h";       # Constants for reading a file
    my $O_RDONLY = $$S{O_RDONLY};
    SaveFirstFour;
    Mov rdi,rax;
    Mov rax,2;
    Mov rsi,$O_RDONLY;
    Xor rdx,rdx;
    Syscall;
    RestoreFirstFourExceptRax;
   } name=> "OpenRead";

  Call $sub;
 }

sub OpenWrite()                                                                 # Create the file named by the terminated string addressed by rax for write
 {@_ == 0 or confess;
  Comment "Open a file for write";

  my $sub = Macro
   {my $S = extractMacroDefinitionsFromCHeaderFile "fcntl.h";                   # Constants for creating a file
#   my $T = extractMacroDefinitionsFromCHeaderFile "sys/stat.h";
    my $O_WRONLY  = $$S{O_WRONLY};
    my $O_CREAT   = $$S{O_CREAT};
    my $O_RDWR    = $$S{O_RDWR};
#   my $S_IRUSR   = $$T{__S_IREAD};
#   my $S_IWUSR   = $$T{__S_IWRITE};
    my $write = $O_WRONLY+0 | $O_CREAT+0;

    SaveFirstFour;
#   Mov rdi,16;
    Mov rdi, rax;
    Mov rax, 2;
    Mov rsi, $write;
#   ClearRegisters rdx;
    Mov rdx, 0x1c0;                                                             # u=rwx  1o=x 4o=r 8g=x 10g=w 20g=r 40u=x 80u=r 100u=r 200=T 400g=S 800u=S #0,2,1000, nothing
    Syscall;

    RestoreFirstFourExceptRax;
   } name=> "OpenWrite";

  Call $sub;
 }

sub CloseFile()                                                                 # Close the file whose descriptor is in rax
 {@_ == 0 or confess;

  my $sub = Macro
   {Comment "Close a file";
    SaveFirstFour;
    Mov rdi, rax;
    Mov rax, 3;
    Syscall;
    RestoreFirstFourExceptRax;
   } name=> "CloseFile";

  Call $sub;
 }

sub StatSize()                                                                  # Stat a file whose name is addressed by rax to get its size in rax
 {@_ == 0 or confess;

  my $S = extractCStructure "#include <sys/stat.h>";                            # Get location of size field
  my $Size = $$S{stat}{size};
  my $off  = $$S{stat}{fields}{st_size}{loc};

  my $sub = Macro
   {Comment "Stat a file for size";
    SaveFirstFour rax;
    Mov rdi, rax;                                                               # File name
    KeepFree rax;
    Mov rax,4;
    Lea rsi, "[rsp-$Size]";
    Syscall;
    KeepFree rax;
    Mov rax, "[$off+rsp-$Size]";                                                # Place size in rax
    RestoreFirstFourExceptRax;
   } name=> "StatSize";

  Call $sub;
 }

sub ReadFile(@)                                                                 # Read a file whose name is addressed by rax into memory.  The address of the mapped memory and its length are returned in registers rax,rdi
 {my (@variables) = @_;                                                         # Variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;
    Comment "Read a file into memory";
    SaveFirstSeven;                                                             # Generated code
    my ($local, $file, $addr, $size, $fdes) = AllocateAll8OnStack 4;            # Local data

    $$p{file}->setReg(rax);                                                     # File name

    StatSize;                                                                   # File size
    Mov $size, rax;                                                             # Save file size
    KeepFree rax;

    $$p{file}->setReg(rax);                                                     # File name
    OpenRead;                                                                   # Open file for read
    Mov $fdes, rax;                                                             # Save file descriptor
    KeepFree rax;

    my $d  = extractMacroDefinitionsFromCHeaderFile "linux/mman.h";             # mmap constants
    my $pa = $$d{MAP_PRIVATE};
    my $ro = $$d{PROT_READ};

    Mov rax, 9;                                                                 # mmap
    Mov rsi, $size;                                                             # Amount of memory
    Xor rdi, rdi;                                                               # Anywhere
    Mov rdx, $ro;                                                               # Read write protections
    Mov r10, $pa;                                                               # Private and anonymous map
    Mov r8,  $fdes;                                                             # File descriptor for file backing memory
    Mov r9,  0;                                                                 # Offset into file
    Syscall;
    Mov rdi, $size;
    $local->free;                                                               # Free stack frame
    $$p{address}->getReg(rax);
    $$p{size}   ->getReg(rdi);
    RestoreFirstSeven;
   } in => {file => 3}, out => {address => 3, size => 3};

  $s->call(@variables);
 }

#D1 Short Strings                                                               # Operations on Short Strings

sub LoadShortStringFromMemoryToZmm2($)                                          # Load the short string addressed by rax into the zmm register with the specified number
 {my ($zmm) = @_;                                                               # Zmm register to load
  @_ == 1 or confess;

  my $sub = Macro
   {Comment "Load a short string from memory into zmm$zmm";
    PushR rax;
    Mov r15b, "[rax]";                                                          # Load first byte which is the length of the string
    Inc r15;                                                                    # Length field
    Mov r14, -1;                                                                # Clear bits that we do not wish to load
    Bzhi r14, r14, r15;
    Kmovq k1, r14;
    Vmovdqu8 "zmm${zmm}{k1}", "[rax]";                                          # Load string
    PopR rax;
   } name=> "LoadShortStringFromMemoryTozmm$zmm";

  Call $sub;
 }

sub LoadShortStringFromMemoryToZmm($$)                                          # Load the short string addressed by rax into the zmm register with the specified number
 {my ($zmm, $address) = @_;                                                     # Zmm register to load, address of string in memory
  @_ == 2 or confess;

  Comment "Load a short string from memory into zmm$zmm from $address";
  PushR my @save = (r15, r14, k7);                                              # Use these registers
  Mov r15b, "[$address]";                                                       # Load first byte which is the length of the string
  Inc r15;                                                                      # Length field
  Mov r14, -1;                                                                  # Clear bits that we do not wish to load
  Bzhi r14, r14, r15;
  Kmovq k7, r14;
  Vmovdqu8 "zmm${zmm}{k7}", "[$address]";                                       # Load string
  PopR @save;
 }

sub GetLengthOfShortString($$)                                                  # Get the length of the short string held in the numbered zmm register into the specified register
 {my ($reg, $zmm) = @_;                                                         # Register to hold length, number of zmm register containing string
  @_ == 2 or confess;
  Pextrb $reg, "xmm$zmm", 0;                                                    # Length
  Keep $reg                                                                     # Result register
 }

sub SetLengthOfShortString($$)                                                  # Set the length of the short string held in the numbered zmm register into the specified register
 {my ($zmm, $reg) = @_;                                                         # Number of zmm register containing string, register to hold length
  @_ == 2 or confess;
  RegisterSize $reg == 1 or confess "Use a byte register";                      # Nasm thinks that PinsrB requires a byte register
  Pinsrb "xmm$zmm", $reg, 0;                                                    # Set length
  $reg                                                                          # Input register
 }

sub ConcatenateShortStrings($$)                                                 # Concatenate the numbered source zmm containing a short string with the short string in the numbered target zmm.
 {my ($left, $right) = @_;                                                      # Target zmm, source zmm
  @_ == 2 or confess;

  my $sub = Macro                                                               # Read file
   {Comment "Concatenate the short string in zmm$right to the short string in zmm$left";
    PushR my @save = (k7, rcx, r14, r15);
    GetLengthOfShortString r15, $right;                                         # Right length
    Mov   r14, -1;                                                              # Expand mask
    Bzhi  r14, r14, r15;                                                        # Skip bits for left
    GetLengthOfShortString rcx, $left;                                          # Left length
    Inc   rcx;                                                                  # Skip length
    Shl   r14, cl;                                                              # Skip length
    Kmovq k7,  r14;                                                             # Unload mask
    PushR "zmm${right}";                                                        # Stack right
    Sub   rsp, rcx;                                                             # Position for masked read
    Vmovdqu8 "zmm${left}{k7}", "[rsp+1]";                                       # Load right string
    Add   rsp, rcx;                                                             # Restore stack
    Add   rsp, RegisterSize zmm0;
    Dec   rcx;                                                                  # Length of left
    Add   rcx, r15;                                                             # Length of combined string = length of left plus length of right
    Pinsrb "xmm${left}", cl, 0;                                                 # Save length in result
    PopR @save;
   } name=> "ConcatenateShortStrings${left}and${right}";

  Call $sub;
 }

#D1 Hash functions                                                              # Hash functions

sub Hash()                                                                      # Hash a string addressed by rax with length held in rdi and return the hash code in r15
 {@_ == 0 or confess;

  my $sub = Macro                                                               # Read file
   {Comment "Hash";

    PushR my @regs = (rax, rdi, k1, zmm0, zmm1);                                # Save registers
    PushR r15;
    Vpbroadcastq zmm0, rdi;                                                     # Broadcast length through ymm0
    Vcvtuqq2pd   zmm0, zmm0;                                                    # Convert to lengths to float
    Vgetmantps   zmm0, zmm0, 4;                                                 # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

    Add rdi, rax;                                                               # Upper limit of string

    ForIn                                                                       # Hash in ymm0 sized blocks
     {Vmovdqu ymm1, "[rax]";                                                    # Load data to hash
      Vcvtudq2pd zmm1, ymm1;                                                    # Convert to float
      Vgetmantps zmm0, zmm0, 4;                                                 # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

      Vmulpd zmm0, zmm1, zmm0;                                                  # Multiply current hash by data
     }
    sub                                                                         # Remainder in partial block
     {Mov r15, -1;
      Bzhi r15, r15, rdi;                                                       # Clear bits that we do not wish to load
      Kmovq k1, r15;                                                            # Take up mask
      Vmovdqu8 "ymm1{k1}", "[rax]";                                             # Load data to hash
      KeepFree r15;

      Vcvtudq2pd zmm1, ymm1;                                                    # Convert to float
      Vgetmantps   zmm0, zmm0, 4;                                               # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

      Vmulpd zmm0, zmm1, zmm0;                                                  # Multiply current hash by data
     }, rax, rdi, RegisterSize ymm0;

    Vgetmantps   zmm0, zmm0, 4;                                                 # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

    Mov r15, 0b11110000;                                                        # Top 4 to bottom 4
    Kmovq k1, r15;
    Vpcompressq  "zmm1{k1}", zmm0;
    Vaddpd       ymm0, ymm0, ymm1;                                              # Top 4 plus bottom 4
    KeepFree r15;

    Mov r15, 0b1100;                                                            # Top 2 to bottom 2
    Kmovq k1, r15;
    Vpcompressq  "ymm1{k1}", ymm0;
    Vaddpd       xmm0, xmm0, xmm1;                                              # Top 2 plus bottom 2
    KeepFree r15;

    Pslldq       xmm0, 2;                                                       # Move centers into double words
    Psrldq       xmm0, 4;
    Mov r15, 0b0101;                                                            # Centers to lower quad
    Kmovq k1, r15;
    Vpcompressd  "xmm0{k1}", xmm0;                                              # Compress to lower quad
    PopR r15;

    Vmovq r15, xmm0;                                                            # Result in r15

    PopR @regs;
   } name=> "Hash";

  Call $sub;
 }

#D1 Byte Strings                                                                # Operations on Byte Strings

sub Cstrlen()                                                                   # Length of the C style string addressed by rax returning the length in r15
 {@_ == 0 or confess;

  my $sub  = Macro                                                              # Create byte string
   {Comment "C strlen";
    PushR my @regs = (rax, rdi, rcx);
    Mov rdi, rax;
    Mov rcx, -1;
    ClearRegisters rax;
    push @text, <<END;
    repne scasb
END
    KeepFree r15;
    Mov r15, rcx;
    Not r15;
    Dec r15;
    PopR @regs;
   } name=> "Cstrlen";

  Call $sub;
 }

sub CreateByteString(%)                                                         # Create an relocatable string of bytes in an arena and returns its address in rax. Optionally add a chain header so that 64 byte blocks of memory can be freed and reused within the byte string.
 {my (%options) = @_;                                                           # free=>1 adds a free chain.
  Comment "Create byte string";
  my $N = Vq(size, 4096);                                                       # Initial size of string

  my ($string, $size, $used, $free) = All8Structure 3;                          # String base
  my $data = $string->field(0, "start of data");                                # Start of data

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;

    AllocateMemory($N, address=>$$p{bs});                                       # Allocate memory and save its location in a variable

    $$p{bs}->setReg(rax);
    $N     ->setReg(rdx);
    Mov rdi, $string->size;                                                     # Size of byte string base structure which is constant
    Mov $used->addr, rdi;                                                       # Used space
    Mov $size->addr, rdx;                                                       # Size

    RestoreFirstFour;
   } out => {bs => 3};

  $s->call(my $bs = Vq(bs));                                                    # Variable that holds the reference to the byte string

  genHash(__PACKAGE__."::ByteString",                                           # Definition of byte string
    structure => $string,                                                       # Structure details
    size      => $size,                                                         # Size field details
    used      => $used,                                                         # Used field details
    free      => $free,                                                         # Free chain offset
    data      => $data,                                                         # The first 8 bytes of the data
    bs        => $bs,                                                           # Variable that address the bytes string
   );
 }

sub Nasm::X86::ByteString::length($@)                                           # Get the length of a byte string
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables
  @_ >= 2 or confess;
  my $size = $byteString->size->addr;
  my $used = $byteString->used->addr;

  my $s = Subroutine                                                            # Allocate more space if required
   {my ($p) = @_;                                                               # Parameters
    Comment "Byte string length";
    SaveFirstFour;
    $$p{bs}->setReg(rax);                                                       # Address byte string
    Mov rdx, $byteString->used->addr;                                           # Used
    Sub rdx, $byteString->structure->size;
    $$p{size}->getReg(rdx);
    RestoreFirstFour;
   } in => {bs=>3}, out => {size => 3};

  $s->call($byteString->bs, @variables);
 }

sub Nasm::X86::ByteString::updateSpace($@)                                      #P Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables

  @_ >= 3 or confess;
  my $size = $byteString->size->addr;
  my $used = $byteString->used->addr;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Allocate more space for a byte string";

    SaveFirstFour;
    $$p{bs}->setReg(rax);                                                       # Address byte string
    my $oldSize = Vq(oldSize, $size);                                           # Size
    my $oldUsed = Vq(oldUsed, $used);                                           # Used
    my $minSize = $oldUsed + $$p{size};                                         # Minimum size of new string
    KeepFree rax;
    If ($minSize > $oldSize, sub                                                # More space needed
     {Mov rax, 4096;                                                            # Minimum byte string size
      $minSize->setReg(rdx);
      ForEver
       {my ($start, $end) = @_;
        Shl rax, 1;                                                             # New byte string size - double the size of the old byte string
        Cmp rax, rdx;                                                           # Big enough?
        IfGe {Jmp $end};                                                        # Big enough!
       };
      my $newSize = Vq(size, rax);                                              # Save new byte string size
      AllocateMemory(size => $newSize, my $address = Vq(address));              # Create new byte string
      CopyMemory(target  => $address, source => $$p{bs}, size => $oldUsed);     # Copy old byte string into new byte string
      FreeMemory(address => $$p{bs},  size   => $oldSize);                      # Free previous memory previously occupied byte string
      $$p{bs}->copyRef($address);                                               # Save new byte string address
     });

    RestoreFirstFour;
   } io => {bs=>3}, in=>{size => 3};

  $s->call(@variables);
 } # updateSpace

sub Nasm::X86::ByteString::makeReadOnly($)                                      # Make a byte string read only
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Make a byte string readable";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    Mov rdi, rax;                                                               # Address of byte string
    Mov rsi, $byteString->size->addr;                                           # Size of byte string
    KeepFree rax;

    Mov rdx, 1;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded byte string
   } in => {bs => 3};

  $s->call(bs => $byteString->bs);
 }

sub Nasm::X86::ByteString::makeWriteable($)                                     # Make a byte string writable
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Make a byte string writable";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    Mov rdi, rax;                                                               # Address of byte string
    Mov rsi, $byteString->size->addr;                                           # Size of byte string
    KeepFree rax;
    Mov rdx, 3;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded byte string
   } in => {bs => 3};

  $s->call(bs => $byteString->bs);
 }

sub Nasm::X86::ByteString::allocate($@)                                         # Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Allocate space in a byte string";
    SaveFirstFour;

    $byteString->updateSpace($$p{bs}, $$p{size});                               # Update space if needed
    $$p{bs}  ->setReg(rax);
    Mov rsi, $byteString->used->addr;                                           # Currently used
    $$p{offset}->getReg(rsi);
    $$p{size}  ->setReg(rdi);
    Add rsi, rdi;
    Mov $byteString->used->addr, rsi;                                           # Currently used
    KeepFree rax, rdi, rsi;

    RestoreFirstFour;
   } in => {bs => 3, size => 3}, out => {offset => 3};

  $s->call($byteString->bs, @variables);
 }

sub Nasm::X86::ByteString::blockSize($)                                         # Size of a block
 {my ($byteString) = @_;                                                        # Byte string
  RegisterSize(zmm0)
 }

sub Nasm::X86::ByteString::allocBlock($@)                                       # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($byteString, @variables) = @_;                                            # Byte string, variables
  @_ >= 2 or confess;
  my $ffb = $byteString->firstFreeBlock;                                        # Check for a free block
  If ($ffb > 0, sub                                                             # Free block available
   {PushR zmm31;
    $byteString->getBlock($byteString->bs, $ffb, 31);                           # Load the first block on the free chain
    my $second = getDFromZmmAsVariable(31, 60);                                # The location of the next pointer is forced upon us by block string which got there first.
    $byteString->setFirstFreeBlock($second);                                   # Set the first free block field to point to the second block
    for my $v(@variables)
     {if (ref($v) and $v->name eq "offset")
       {$v->copy($ffb);
        last;
       }
     }
    PopR zmm31;
   },
  sub
   {$byteString->allocate(Vq(size, RegisterSize(zmm0)), @variables);
   });
 }

sub Nasm::X86::ByteString::firstFreeBlock($)                                    #P Create and load a variable with the first free block on the free block chain or zero if no such block in the given byte string
 {my ($byteString) = @_;                                                        # Byte string address as a variable
  @_ == 1 or confess;

  Comment "Get first free block in a byte string";
  PushR rax;
  $byteString->bs->setReg(rax);                                                 #P Address underlying byte string
  KeepFree rax;
  Mov rax, $byteString->free->addr;                                             # Content of free chain pointer
  my $v = Vq('free', rax);                                                      # Remainder of the free chain
  PopR rax;
  $v
 }

sub Nasm::X86::ByteString::setFirstFreeBlock($$)                                #P Set the first free block field from a variable
 {my ($byteString, $offset) = @_;                                               # Byte string descriptor, first free block offset as a variable
  @_ == 2 or confess;

  Comment "Set first free block";
  PushR my @save = (rax, rsi, rdx);
  $byteString->bs->setReg(rax);                                                 # Address underlying byte string
  Lea rdx, $byteString->free->addr;                                             # Address of address of free chain
  $offset->setReg(rsi);                                                         # Offset of block being freed
  Mov "[rdx]", rsi;                                                             # Set head of free chain to point to block just freed
  PopR @save;
 }

sub Nasm::X86::ByteString::freeBlock($@)                                        # Free a block in a byte string by placing it on the free chain
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Free a block in a byte string";
    PushR zmm31;
    my $rfc = $byteString->firstFreeBlock;                                      # Get first free block
    ClearRegisters zmm31;                                                       # Second block
    $rfc->putDIntoZmm(31, 60);                                                  # The position of the next pointer was dictated by block strings.
    $byteString->putBlock($$p{bs}, $$p{offset}, 31);                            # Link the freed block to the rest of the free chain
    $byteString->setFirstFreeBlock($$p{offset});                                # Set free chain field to point to latest free chain element
    PopR zmm31;
   } in => {bs => 3, offset => 3};

  $s->call($byteString->bs, @variables);
 }

sub Nasm::X86::ByteString::getBlock($$$$)                                       # Get the block with the specified offset in the specified block string and return it in the numbered zmm
 {my ($byteString, $bsa, $block, $zmm) = @_;                                    # Byte string descriptor, byte string variable, offset of the block as a variable, number of zmm register to contain block
  @_ == 4 or confess;
  PushR my @save = (r14, r15);                                                  # Result register
  defined($bsa) or confess;
  $bsa->setReg(r15);                                                            # Byte string address
  defined($block) or confess;
  $block->setReg(r14);                                                          # Offset of block in byte string
  Vmovdqu64 "zmm$zmm", "[r15+r14]";                                             # Read from memory
  PopR @save;                                                                   # Restore registers
 }

sub Nasm::X86::ByteString::putBlock($$$$)                                       # Write the numbered zmm to the block at the specified offset in the specified byte string
 {my ($byteString, $bsa, $block, $zmm) = @_;                                    # Byte string descriptor, byte string variable, block in byte string, content variable
  @_ >= 4 or confess;
  PushR my @save = (r14, r15);                                                  # Work registers
  defined($bsa) or confess "Byte string not set";
  $bsa->setReg(r15);                                                            # Byte string address
  defined($block) or confess;
  $block->setReg(r14);                                                          # Offset of block in byte string
  Vmovdqu64 "[r15+r14]", "zmm$zmm";                                             # Write to memory
  PopR @save;                                                                   # Restore registers
 }

sub Nasm::X86::ByteString::m($@)                                                # Append the content with length rdi addressed by rsi to the byte string addressed by rax
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables
  @_ >= 4 or confess;
  my $used = $byteString->used->addr;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Append memory to a byte string";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    my $oldUsed = Vq("used", $used);
    $byteString->updateSpace($$p{bs}, $$p{size});                               # Update space if needed

    my $target  = $oldUsed + $$p{bs};
    KeepFree rax;
    CopyMemory(source => $$p{address}, $$p{size}, target => $target);           # Move data in

    KeepFree rdx;
    my $newUsed = $oldUsed + $$p{size};

    $$p{bs} ->setReg(rax);                                                      # Update used field
    $newUsed->setReg(rdi);
    Mov $used, rdi;

    RestoreFirstFour;
   } io => { bs => 3}, in => {address => 3, size => 3};

  $s->call(@variables);
 }

sub Nasm::X86::ByteString::q($$)                                                # Append a constant string to the byte string
 {my ($byteString, $string) = @_;                                               # Byte string descriptor, string
  @_ == 2 or confess;

  my $s = Rs($string);

  my $bs = $byteString->bs;                                                     # Move data
  my $ad = Vq(address, $s);
  my $sz = Vq(size, length($string));
  $byteString->m($bs, $ad, $sz);
 }

sub Nasm::X86::ByteString::ql($$)                                               # Append a quoted string containing new line characters to the byte string addressed by rax
 {my ($byteString, $const) = @_;                                                # Byte string, constant
  @_ == 2 or confess;
  for my $l(split /\s*\n/, $const)
   {$byteString->q($l);
    $byteString->nl;
   }
 }

sub Nasm::X86::ByteString::char($$)                                             # Append a character expressed as a decimal number to the byte string addressed by rax
 {my ($byteString, $char) = @_;                                                 # Byte string descriptor, number of character to be appended
  @_ == 2 or confess;
  my $s = Rb(ord($char));
  $byteString->m($byteString->bs, Vq(address, $s), Vq(size, 1));                # Move data
 }

sub Nasm::X86::ByteString::nl($)                                                # Append a new line to the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;
  $byteString->char("\n");
 }

sub Nasm::X86::ByteString::z($)                                                 # Append a trailing zero to the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;
  $byteString->char("\0");
 }

sub Nasm::X86::ByteString::rdiInHex                                             # Add the content of register rdi in hexadecimal in big endian notation to a byte string
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;

  PushR rax;                                                                    # Get address of byte string
  $byteString->address->setReg(rax);

  Comment "Rdi in hex into byte string";
  my $hexTranslateTable = hexTranslateTable;
  my $value =  r8;
  my $hex   =  r9;
  my $byte  = r10;
  my $size  = RegisterSize rax;

  SaveFirstSeven;
  Mov $value, rdi;                                                              # Content to be printed
  Mov rdi, 2;                                                                   # Length of a byte in hex
  for my $i(0..7)                                                               # Each byte in rdi
   {KeepFree $byte;
    Mov $byte, $value;
    Shl $byte, 8 *  $i;                                                         # Push selected byte high
    Shr $byte, 8 * ($size - 1);                                                 # Push select byte low
    Shl $byte, 1;                                                               # Multiply by two because each entry in the translation table is two bytes long
    Lea rsi, "[$hexTranslateTable+$byte]";
    $byteString->m;
   }
  RestoreFirstSeven;
 }

sub Nasm::X86::ByteString::append($@)                                           # Append one byte string to another
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Concatenate byte strings";
    SaveFirstFour;
    $$p{source}->setReg(rax);
    Mov rdi, $byteString->used->addr;
    Sub rdi, $byteString->structure->size;
    Lea rsi, $byteString->data->addr;
    $byteString->m(bs=>$$p{target}, Vq(address, rsi), Vq(size, rdi));
    RestoreFirstFour;
   } in => {target=>3, source=>3};

  $s->call(target=>$byteString->bs, @variables);
 }

sub Nasm::X86::ByteString::clear($)                                             # Clear the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Clear byte string";
    PushR my @save = (rax, rdi);
    $$p{bs}->setReg(rax);
    Mov rdi, $byteString->structure->size;
    Mov $byteString->used->addr, rdi;
    PopR     @save;
   } in => {bs => 3};

  $s->call(bs => $byteString->bs);
 }

sub Nasm::X86::ByteString::write($@)                                            # Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Write a byte string to a file";
    SaveFirstFour;

    $$p{file}->setReg(rax);
    OpenWrite;                                                                  # Open file
    my $file = Vq('fd', rax);                                                   # File descriptor
    KeepFree rax;

    $$p{bs}->setReg(rax);                                                       # Write file
    Lea rsi, $byteString->data->addr;
    Mov rdx, $byteString->used->addr;
    Sub rdx, $byteString->structure->size;
    KeepFree rax;

    Mov rax, 1;                                                                 # Write content to file
    $file->setReg(rdi);
    Syscall;
    KeepFree rax, rdi, rsi, rdx;

    $file->setReg(rax);
    CloseFile;
    RestoreFirstFour;
   }  in => {bs => 3, file => 3};

  $s->call(bs => $byteString->bs, @variables);
 }

sub Nasm::X86::ByteString::read($@)                                             # Read the named file (terminated with a zero byte) and place it into the named byte string.
 {my ($byteString, @variables) = @_;                                            # Byte string descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Read a byte string";
    ReadFile($$p{file}, (my $size = Vq(size)), my $address = Vq(address));
    $byteString->m($$p{bs}, $size, $address);                                   # Move data into byte string
    FreeMemory($size, $address);                                                # Free memory allocated by read
   } io => {bs => 3}, in => {file => 3};

  $s->call(bs => $byteString->bs, @variables);
 }

sub Nasm::X86::ByteString::out($)                                               # Print the specified byte string addressed by rax on sysout
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Write a byte string";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    Mov rdi, $byteString->used->addr;                                           # Length to print
    Sub rdi, $byteString->structure->size;                                      # Length to print
    Lea rax, $byteString->data->addr;                                           # Address of data field
    PrintOutMemory;
    RestoreFirstFour;
   } in => {bs => 3};

  $s->call($byteString->bs);
 }

sub executeFileViaBash(@)                                                       # Execute the file named in the byte string addressed by rax with bash
 {my (@variables) = @_;                                                         # Variables
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Execute a file via bash";
    SaveFirstFour;
    Fork;                                                                       # Fork

    Test rax, rax;

    IfNz                                                                        # Parent
     {WaitPid;
     }
    sub                                                                         # Child
     {KeepFree rax;
      $$p{file}->setReg(rdi);
      Mov rsi, 0;
      Mov rdx, 0;
      Mov rax, 59;
      Syscall;
     };
    RestoreFirstFour;
   } in => {file => 3};

  $s->call(@variables);
 }

sub unlinkFile(@)                                                               # Unlink the named file
 {my (@variables) = @_;                                                         # Variables
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Unlink a file";
    SaveFirstFour;
    $$p{file}->setReg(rdi);
    Mov rax, 87;
    Syscall;
    RestoreFirstFour;
   } in => {file => 3};

  $s->call(@variables);
 }

sub Nasm::X86::ByteString::dump($)                                              # Dump details of a byte string
 {my ($byteString) = @_;                                                        # Byte string descriptor
  @_ == 1 or confess;

  PushR my @save = (rax, r15);                                                  # Get address of byte string
  $byteString->bs->setReg(rax);

  Call Macro                                                                    # Bash string
   {Comment "Print details of a byte string";
    SaveFirstFour;
    PrintOutStringNL("Byte String");

    PushR rax;                                                                  # Print size
    Mov rax, $byteString->size->addr;
    PrintOutString("  Size: ");
    PrintOutRaxInHex;
    PrintOutNL;
    PopR rax;

    PushR rax;                                                                  # Print used
    Mov rax, $byteString->used->addr;
    PrintOutString("  Used: ");
    PrintOutRaxInHex;
    PrintOutNL;
    PopR rax;

    Mov rdi, 64;
    PrintOutString("0000: ");
    PrintOutMemoryInHexNL;

    Add rax, 64;
    PrintOutString("0040: ");
    PrintOutMemoryInHexNL;

    Add rax, 64;
    PrintOutString("0080: ");
    PrintOutMemoryInHexNL;

    Add rax, 64;
    PrintOutString("00C0: ");
    PrintOutMemoryInHexNL;
    RestoreFirstFour;
   } name => "Nasm::X86::ByteString::dump";

  PopR @save;
 }

#D1 Block Strings                                                               # Strings made from zmm sized blocks of text

sub Nasm::X86::ByteString::CreateBlockString($)                                 # Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the byte string addressed by rax and return its descriptor
 {my ($byteString) = @_;                                                        # Byte string description
  @_ == 1 or confess;
  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  Comment "Allocate a new block string in a byte string";

  my $s = genHash(__PACKAGE__."::BlockString",                                  # Block string definition
    bs      => $byteString,                                                     # Bytes string definition
    links   => $b - 2 * $o,                                                     # Location of links in bytes in zmm
    next    => $b - 1 * $o,                                                     # Location of next offset in block in bytes
    prev    => $b - 2 * $o,                                                     # Location of prev offset in block in bytes
    length  => $b - 2 * $o - 1,                                                 # Maximum length in a block
    first   => Vq('first'),                                                     # Variable addressing first block in block string
   );

  $s->allocBlock(my $first = Vq(offset));  $s->first->copy($first);             # Allocate first block and save it in a variable named first not offset

  if (1)                                                                        # Initialize circular list
   {my $nn = $s->next;
    my $pp = $s->prev;
    PushR my @save = (r14, r15);
    $byteString->bs->setReg(r15);
    $first         ->setReg(r14);
    Mov "[r15+r14+$nn]", r14d;
    Mov "[r15+r14+$pp]", r14d;
    PopR @save;
   }
  $s                                                                            # Description of block string
 }

sub Nasm::X86::BlockString::address($)                                          # Address of a block string
 {my ($blockString) = @_;                                                       # Block string descriptor
  @_ == 1 or confess;
  $blockString->bs->bs;
 }

sub Nasm::X86::BlockString::allocBlock($@)                                      # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($blockString, @variables) = @_;                                           # Block string descriptor, variables
  @_ >= 2 or confess;

  $blockString->bs->allocBlock($blockString->address, @variables);
 }

sub Nasm::X86::BlockString::getBlockLengthInZmm($$)                             # Get the block length of the numbered zmm and return it in a variable
 {my ($blockString, $zmm) = @_;                                                 # Block string descriptor, number of zmm register
  @_ == 2 or confess;
  getBFromZmmAsVariable $zmm, 0;                                                # Block length
 }

sub Nasm::X86::BlockString::setBlockLengthInZmm($$$)                            # Set the block length of the numbered zmm to the specified length
 {my ($blockString, $length, $zmm) = @_;                                        # Block string descriptor, length as a variable, number of zmm register
  @_ == 3 or confess;
  PushR my @save = (r15);                                                       # Save work register
  $length->setReg(r15);                                                         # New length
  $length->putBIntoZmm($zmm, 0);                                                # Insert block length
  PopR @save;                                                                   # Length of block is a byte
 }

sub Nasm::X86::BlockString::getBlock($$$$)                                      # Get the block with the specified offset in the specified block string and return it in the numbered zmm
 {my ($blockString, $bsa, $block, $zmm) = @_;                                   # Block string descriptor, byte string variable, offset of the block as a variable, number of zmm register to contain block
  @_ >= 4 or confess;
  $blockString->bs->getBlock($bsa, $block, $zmm);
 }

sub Nasm::X86::BlockString::putBlock($$$$)                                      # Write the numbered zmm to the block at the specified offset in the specified byte string
 {my ($blockString, $bsa, $block, $zmm) = @_;                                   # Block string descriptor, byte string variable, block in byte string, content variable
  @_ >= 4 or confess;
  $blockString->bs->putBlock($bsa, $block, $zmm);
 }

sub Nasm::X86::BlockString::getNextAndPrevBlockOffsetFromZmm($$)                # Get the offsets of the next and previous blocks as variables from the specified zmm
 {my ($blockString, $zmm) = @_;                                                 # Block string descriptor, zmm containing block
  @_ == 2 or confess;
  my $l = $blockString->links;                                                  # Location of links
  PushR my @regs = (r14, r15);                                                  # Work registers
  my $L = getQFromZmmAsVariable($zmm, $blockString->links);                     # Links in one register
  $L->setReg(r15);                                                              # Links
  Mov r14d, r15d;                                                               # Next
  Shr r15, RegisterSize(r14d) * 8;                                              # Prev
  my @r = (Vq("Next block offset", r15), Vq("Prev block offset", r14));         # Result
  PopR @regs;                                                                   # Free work registers
  @r;                                                                           # Return (next, prev)
 }

sub Nasm::X86::BlockString::putNextandPrevBlockOffsetIntoZmm($$$$)              # Save next and prev offsets into a zmm representing a block
 {my ($blockString, $zmm, $next, $prev) = @_;                                   # Block string descriptor, zmm containing block, next offset as a variable, prev offset as a variable
  @_ == 4 or confess;
  if ($next and $prev)                                                          # Set both previous and next
   {PushR my @regs = (r14, r15);                                                # Work registers
    $next->setReg(r14);                                                         # Next offset
    $prev->setReg(r15);                                                         # Prev offset
    Shl r14, RegisterSize(r14d) * 8;                                            # Prev high
    Or r15, r14;                                                                # Links in one register
    my $l = Vq("Links", r15);                                                   # Links as variable
    $l->putQIntoZmm($zmm, $blockString->links);                                 # Load links into zmm
    PopR @regs;                                                                 # Free work registers
   }
  elsif ($next)                                                                 # Set just next
   {PushR my @regs = (r15);                                                     # Work registers
    $next->setReg(r15);                                                         # Next offset
    my $l = Vq("Links", r15);                                                   # Links as variable
    $l->putDIntoZmm($zmm, $blockString->next);                                  # Load links into zmm
    PopR @regs;                                                                 # Free work registers
   }
  elsif ($prev)                                                                 # Set just prev
   {PushR my @regs = (r15);                                                     # Work registers
    $prev->setReg(r15);                                                         # Next offset
    my $l = Vq("Links", r15);                                                   # Links as variable
    $l->putDIntoZmm($zmm, $blockString->prev);                                  # Load links into zmm
    PopR @regs;                                                                 # Free work registers
   }
 }

sub Nasm::X86::BlockString::dump($)                                             # Dump a block string to sysout
 {my ($blockString) = @_;                                                       # Block string descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Dump a block in a block string";
    PushR my @save = (zmm31);
    my $block  = $$p{first};                                                    # The first block
                 $blockString->getBlock($$p{bs}, $block, 31);                   # The first block in zmm31
    my $length = $blockString->getBlockLengthInZmm(31);                         # Length of block
    PrintOutStringNL "Block String Dump";
    $block ->out("Offset: ");
    PrintOutString "   ";
    $length->outNL("Length: "); PrintOutRegisterInHex zmm31;                    # Print block

    ForEver                                                                     # Each block in string
     {my ($start, $end) = @_;                                                   #
      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Get links from current block
      If ($next == $block, sub{Jmp $end});                                      # Next block is the first block so we have printed the block string
      $blockString->getBlock($$p{bs}, $next, 31);                               # Next block in zmm
      my $length = $blockString->getBlockLengthInZmm(31);                       # Length of block
      $next  ->out("Offset: ");                                                 # Print block
      PrintOutString "   ";
      $length->outNL("Length: "); PrintOutRegisterInHex zmm31;
     };
    PrintOutNL;

    PopR @save;
   } in => {bs => 3, first => 3};

  $s->call($blockString->address, $blockString->first);
 }

sub Nasm::X86::BlockString::len($$)                                             # Find the length of a block string
 {my ($blockString, $size) = @_;                                                # Block string descriptor, size variable
  @_ == 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Length of a block string";
    PushR my @save = (zmm31);
    my $block  = $$p{first};                                                    # The first block
                 $blockString->getBlock($$p{bs}, $block, 31);                   # The first block in zmm31
    my $length = $blockString->getBlockLengthInZmm(31);                         # Length of block

    ForEver                                                                     # Each block in string
     {my ($start, $end) = @_;                                                   #
      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Get links from current block
      If ($next == $block, sub{Jmp $end});                                      # Next block is the first block so we have printed the block string
      $blockString->getBlock($$p{bs}, $next, 31);                               # Next block in zmm
      $length += $blockString->getBlockLengthInZmm(31);                         # Add length of block
     };
    $$p{size}->copy($length);
    PopR @save;
   } in => {bs => 3, first => 3}, out => {size => 3};

  $s->call($blockString->address, $blockString->first, $size);
 }

sub Nasm::X86::BlockString::concatenate($$)                                     # Concatenate two block strings by appending a copy of the source to the target block string.
 {my ($target, $source) = @_;                                                   # Target block string, source block string
  @_ == 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Concatenate block strings";
    PushR my @save = (zmm29, zmm30, zmm31);
    my $sb = $$p{sBs};                                                          # The byte string underlying the source
    my $sf = $$p{sFirst};                                                       # The first block in the source
    my $tb = $$p{tBs};                                                          # The byte string underlying the target
    my $tf = $$p{tFirst};                                                       # The first block in the target
    $source->getBlock($sb, $sf, 31);                                            # The first source block
    $target->getBlock($tb, $tf, 30);                                            # The first target block
    my ($ts, $tl) = $target->getNextAndPrevBlockOffsetFromZmm(30);              # Target second and last
    $target->getBlock($tb, $tl, 30);                                            # The last target block to which we will append

    ForEver                                                                     # Each block in source string
     {my ($start, $end) = @_;                                                   # Start and end labels

      $target->allocBlock(bs => $tb, my $new = Vq(offset));                     # Allocate new block
      Vmovdqu8 zmm29, zmm31;                                                    # Load new target block from source
      my ($next, $prev) = $target->getNextAndPrevBlockOffsetFromZmm(30);        # Linkage from last target block

      $target->putNextandPrevBlockOffsetIntoZmm(30, $new,    $prev);            # From last block
      $target->putNextandPrevBlockOffsetIntoZmm(29, $tf,     $tl);              # From new block
      $target->putBlock($tb, $tl, 30);                                          # Put the modified last target block
      $tl->copy($new);                                                          # New last target block
      $target->putBlock($tb, $tl, 29);                                          # Put the modified new last target block
      Vmovdqu8 zmm30, zmm29;                                                    # Last target block

      my ($sn, $sp) = $source->getNextAndPrevBlockOffsetFromZmm(31);            # Get links from current source block
      If ($sn == $sf, sub                                                       # Last source block
       {$source->getBlock($tb, $tf, 30);                                        # The first target block
        $source->putNextandPrevBlockOffsetIntoZmm(30, undef, $new);             # Update end of block chain
        $source->putBlock($tb, $tf, 30);                                        # Save modified first target block

        Jmp $end
       });

      $source->getBlock($sb, $sn, 31);                                          # Next source block
     };

    PopR @save;
   } in => {sBs => 3, sFirst => 3, tBs => 3, tFirst => 3};

  $s->call(sBs => $source->address, sFirst => $source->first,
           tBs => $target->address, tFirst => $target->first);
 }

sub Nasm::X86::BlockString::insertChar($@)                                      # Insert a character into a block string
 {my ($blockString, @variables) = @_;                                           # Block string, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Insert character into a block string";
    PushR my @save = (k7, r14, r15, zmm30, zmm31);
    my $B = $$p{bs};                                                            # The byte string underlying the block string
    my $F = $$p{first};                                                         # The first block in block string
    my $c = $$p{character};                                                     # The character to insert
    my $P = $$p{position};                                                      # The position in the block string at which we want to insert the character
    $blockString->getBlock($B, $F, 31);                                         # The first source block
    my $C = Vq('Current character position', 0);                                # Current character position
    my $L = $blockString->getBlockLengthInZmm(31);                              # Length of last block
    my $M   = Vq('Block length', $blockString->length);                         # Maximum length of a block
    my $One = Vq('One', 1);                                                     # Literal one
    my $current = $F;                                                           # Current position in scan of block chain

    ForEver                                                                     # Each block in source string
     {my ($start, $end) = @_;                                                   # Start and end labels

      If ((($P >= $C) & ($P <= $C + $L)), sub                                   # Position is in current block
       {my $O = $P - $C;                                                        # Offset in current block
        PushRR zmm31;                                                           # Stack block
        $O->setReg(r14);                                                        # Offset of character in block
        $c->setReg(r15);                                                        # Character to insert
        Mov "[rsp+r14]", r15b;                                                  # Place character after skipping length field

        If ($L < $M, sub                                                        # Current block has space
         {($P+1)->setMask($C + $L - $P + 1, k7);                                # Set mask for reload
          Vmovdqu8 "zmm31{k7}", "[rsp-1]";                                      # Reload
          $blockString->setBlockLengthInZmm($L + 1, 31);                        # Length of block
         },
        sub                                                                     # In the current block but no space so split the block
         {$One->setMask($C + $L - $P + 2, k7);                                  # Set mask for reload
          Vmovdqu8 "zmm30{k7}", "[rsp+r14-1]";                                  # Reload
          $blockString->setBlockLengthInZmm($O,          31);                   # New shorter length of original block
          $blockString->setBlockLengthInZmm($L - $O + 1, 30);                   # Set length of  remainder plus inserted char in the new block

          $blockString->allocBlock($B, my $new = Vq(offset));                   # Allocate new block
          my ($next, $prev)=$blockString->getNextAndPrevBlockOffsetFromZmm(31); # Linkage from last block

          If ($next == $prev, sub                                               # The existing string has one block, add new as the second block
           {$blockString->putNextandPrevBlockOffsetIntoZmm(31, $new,  $new);
            $blockString->putNextandPrevBlockOffsetIntoZmm(30, $next, $prev);
           },
          sub                                                                   # The existing string has two or more blocks
           {$blockString->putNextandPrevBlockOffsetIntoZmm(31, $new,  $prev);   # From last block
            $blockString->putNextandPrevBlockOffsetIntoZmm(30, $next, $current);# From new block
           });

          $blockString->putBlock($B, $new, 30);                                 # Save the modified block
         });

        $blockString->putBlock($B, $current, 31);                               # Save the modified block
        PopRR zmm31;                                                            # Restore stack
        KeepFree r14, r15;
        Jmp $end;                                                               # Character successfully inserted
       });

      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Get links from current source block
      If ($next == $F, sub                                                      # Last source block
       {$c->setReg(r15);                                                        # Character to insert
        Push r15;
        $blockString->append($B, $F, Vq(size, 1), Vq(source, rsp));             # Append character if we go beyond limit
        Pop  r15;
        Jmp $end;
       });

      $current->copy($next);
      $blockString->getBlock($B, $current, 31);                                 # Next block
      $L = $blockString->getBlockLengthInZmm(31);                               # Length of block
      $C += $L;                                                                 # Current character position at the start of this block
     };

    PopR @save;
   } in => {bs => 3, first => 3, character => 3, position => 3};

  $s->call($blockString->address, first => $blockString->first, @variables)
 }

sub Nasm::X86::BlockString::deleteChar($@)                                      # Delete a character in a block string
 {my ($blockString, @variables) = @_;                                           # Block string, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Delete a character in a block string";
    PushR my @save = (k7, zmm31);
    my $B = $$p{bs};                                                            # The byte string underlying the block string
    my $F = $$p{first};                                                         # The first block in block string
    my $P = $$p{position};                                                      # The position in the block string at which we want to insert the character
    $blockString->getBlock($B, $F, 31);                                         # The first source block
    my $C = Vq('Current character position', 0);                                # Current character position
    my $L = $blockString->getBlockLengthInZmm(31);                              # Length of last block
    my $current = $F;                                                           # Current position in scan of block chain

    ForEver                                                                     # Each block in source string
     {my ($start, $end) = @_;                                                   # Start and end labels

      If ((($P >= $C) & ($P <= $C + $L)), sub                                   # Position is in current block
       {my $O = $P - $C;                                                        # Offset in current block
        PushRR zmm31;                                                           # Stack block
        ($O+1)->setMask($L - $O, k7);                                           # Set mask for reload
        Vmovdqu8 "zmm31{k7}", "[rsp+1]";                                        # Reload
        $blockString->setBlockLengthInZmm($L-1, 31);                            # Length of block
        $blockString->putBlock($B, $current, 31);                               # Save the modified block
        PopRR zmm31;                                                            # Stack block
        Jmp $end;                                                               # Character successfully inserted
       });

      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Get links from current source block
      $blockString->getBlock($B, $next, 31);                                    # Next block
      $current->copy($next);
      $L = $blockString->getBlockLengthInZmm(31);                               # Length of block
      $C += $L;                                                                 # Current character position at the start of this block
     };

    PopR @save;
   } in => {bs => 3, first => 3, position => 3};

  $s->call($blockString->address, first => $blockString->first, @variables)
 }

sub Nasm::X86::BlockString::getCharacter($@)                                    # Get a character from a block string
 {my ($blockString, @variables) = @_;                                           # Block string, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Get a character from a block string";
    PushR my @save = (r15, zmm31);
    my $B = $$p{bs};                                                            # The byte string underlying the block string
    my $F = $$p{first};                                                         # The first block in block string
    my $P = $$p{position};                                                      # The position in the block string at which we want to insert the character
    $blockString->getBlock($B, $F, 31);                                         # The first source block
    my $C = Vq('Current character position', 0);                                # Current character position
    my $L = $blockString->getBlockLengthInZmm(31);                              # Length of last block

    ForEver                                                                     # Each block in source string
     {my ($start, $end) = @_;                                                   # Start and end labels

      If ((($P >= $C) & ($P <= $C + $L)), sub                                   # Position is in current block
       {my $O = $P - $C;                                                        # Offset in current block
        PushRR zmm31;                                                           # Stack block
        ($O+1)  ->setReg(r15);                                                  # Character to get
        KeepFree r15;
        Mov r15b, "[rsp+r15]";                                                  # Reload
        $$p{out}->getReg(r15);                                                  # Save character
        PopRR zmm31;                                                            # Stack block
        Jmp $end;                                                               # Character successfully inserted
       });

      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Get links from current source block
      $blockString->getBlock($B, $next, 31);                                    # Next block
      $L = $blockString->getBlockLengthInZmm(31);                               # Length of block
      $C += $L;                                                                 # Current character position at the start of this block
     };

    PopR @save;
   } in => {bs => 3, first => 3, position => 3}, out => {out => 3};

  $s->call($blockString->address, first => $blockString->first, @variables)
 }

sub Nasm::X86::BlockString::append($@)                                          # Append the specified content in memory to the specified block string
 {my ($blockString, @variables) = @_;                                           # Block string descriptor, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Append completed successfully
    my $Z       = Vq(zero, 0);                                                  # Zero
    my $O       = Vq(one,  1);                                                  # One
    my $L       = Vq(size, $blockString->length);                               # Length of a full block
    my $B       = $$p{bs};                                                      # Underlying block string
    my $source  = $$p{source};                                                  # Address of content to be appended
    my $size    = $$p{size};                                                    # Size of content
    my $first   = $$p{first};                                                   # First (preallocated) block in block string

    PushR my @save = (zmm29, zmm30, zmm31);
    ForEver                                                                     # Append content until source exhausted
     {my ($start, $end) = @_;                                                   # Parameters
      $blockString->getBlock($B, $first, 29);                                   # Get the first block
      my ($second, $last) = $blockString->getNextAndPrevBlockOffsetFromZmm(29); # Get the offsets of the second and last blocks
      $blockString->getBlock($B, $last,  31);                                   # Get the last block
      my $lengthLast      = $blockString->getBlockLengthInZmm(31);              # Length of last block
      my $spaceLast       = $L - $lengthLast;                                   # Space in last block
      my $toCopy          = $spaceLast->min($size);                             # Amount of data required to fill first block
      my $startPos        = $O + $lengthLast;                                   # Start position in zmm
      $source->setZmm(31, $startPos, $toCopy);                                  # Append bytes
      $blockString->setBlockLengthInZmm($lengthLast + $toCopy, 31);             # Set the length
      $blockString->putBlock($B, $last, 31);                                    # Put the block
      If ($size <= $spaceLast, sub {Jmp $end});                                 # We are finished because the last block had enough space

      $source += $toCopy;                                                       # Remaining source
      $size   -= $toCopy;                                                       # Remaining source length

      $blockString->allocBlock($B, my $new = Vq(offset));                       # Allocate new block
      $blockString->getBlock  ($B, $new, 30);                                   # Load the new block
      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Linkage from last block

      If ($first == $last, sub                                                  # The existing string has one block, add new as the second block
        {$blockString->putNextandPrevBlockOffsetIntoZmm(31, $new,  $new);
         $blockString->putNextandPrevBlockOffsetIntoZmm(30, $last, $last);
        },
      sub                                                                       # The existing string has two or more blocks
       {$blockString->putNextandPrevBlockOffsetIntoZmm(31, $new,    $prev);     # From last block
        $blockString->putNextandPrevBlockOffsetIntoZmm(30, $next,   $last);     # From new block
        $blockString->putNextandPrevBlockOffsetIntoZmm(29, undef,   $new);      # From first block
        $blockString->putBlock($B, $first, 29);                                 # Put the modified last block
        });

      $blockString->putBlock($B, $last, 31);                                    # Put the modified last block
      $blockString->putBlock($B, $new,  30);                                    # Put the modified new block
     };
    PopR @save;
   }  in => {bs => 3, first => 3, source => 3, size => 3};

  $s->call($blockString->address, $blockString->first, @variables);
 }

sub Nasm::X86::BlockString::clear($)                                            # Clear the block by freeing all but the first block
 {my ($blockString) = @_;                                                       # Block string descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    PushR my @save = (rax, r14, r15, zmm29, zmm30, zmm31);

    my $first = $$p{first};                                                     # First block
    $blockString->getBlock($$p{bs}, $$p{first}, 29);                            # Get the first block
    my ($second, $last) = $blockString->getNextAndPrevBlockOffsetFromZmm(29);   # Get the offsets of the second and last blocks
    ClearRegisters zmm29;                                                       # Clear first block
    $blockString->putNextandPrevBlockOffsetIntoZmm(29, $first, $first);         # Initialize block chain
    $blockString->putBlock($$p{bs}, $first, 29);                                # Put the first block

    If ($last == $first, sub                                                    # String only has one block
     {},
    sub                                                                         # Two or more blocks on the chain
     {$$p{bs}->setReg(rax);                                                     # Address underlying byte string
      Lea r14, $blockString->bs->free->addr;                                    # Address of address of free chain
      Mov r15, "[r14]";                                                         # Address of free chain
      my $rfc = Vq('next', r15);                                                # Remainder of the free chain

      If ($second == $last, sub                                                 # Two blocks on the chain
       {ClearRegisters zmm30;                                                   # Second block
        $blockString->putNextandPrevBlockOffsetIntoZmm(30, $rfc, undef);        # Put second block on head of the list
        $blockString->putBlock($$p{bs}, $second, 30);                           # Put the second block
       },
      sub                                                                       # Three or more blocks on the chain
       {my $z = Vq(zero, 0);                                                    # A variable with zero in it
        $blockString->getBlock($$p{bs}, $second, 30);                           # Get the second block
        $blockString->getBlock($$p{bs}, $last,   31);                           # Get the last block
        $blockString->putNextandPrevBlockOffsetIntoZmm(30, undef, $z);          # Reset prev pointer in second block
        $blockString->putNextandPrevBlockOffsetIntoZmm(31, $rfc, undef);        # Reset next pointer in last block to remainder of free chain
        $blockString->putBlock($$p{bs}, $second, 30);                           # Put the second block
        $blockString->putBlock($$p{bs}, $last, 31);                             # Put the last block
       }),

      KeepFree        r15;                                                      # Put the second block at the top of the free chain
      $second->setReg(r15);
      Mov  "[r14]",   r15;
     });

    PopR @save;
   }  in => {bs => 3, first => 3};

  $s->call($blockString->address, $blockString->first);
 }

#D1 Block Array                                                                 # Array constructed as a tree of blocks in a byte string

sub Nasm::X86::ByteString::CreateBlockArray($)                                  # Create a block array in a byte string
 {my ($byteString) = @_;                                                        # Byte string description
  @_ == 1 or confess;
  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  Comment "Allocate a new block array in a byte string";

  my $p = 0;                                                                    # Position in block
  my $s = genHash(__PACKAGE__."::BlockArray",                                   # Block string definition
    bs     => $byteString,                                                      # Bytes string definition
    width  => $o,                                                               # Width of each element
    first  => Vq('first'),                                                      # Variable addressing first block in block string
    slots1 => $b / $o - 1,                                                      # Number of slots in first block
    slots2 => $b / $o,                                                          # Number of slots in second and subsequent blocks
   );
  $s->slots2 == 16 or confess "Number of slots per block not 16";               # Slots per block

  $s->allocBlock(bs => $byteString->bs, my $first = Vq(offset));                # Allocate first block
  $s->first->copy($first);                                                      # Save first block
  $s                                                                            # Description of block array
 }

sub Nasm::X86::BlockArray::address($)                                           # Address of a block string
 {my ($blockArray) = @_;                                                        # Block array descriptor
  @_ == 1 or confess;
  $blockArray->bs->bs;
 }

sub Nasm::X86::BlockArray::allocBlock($@)                                       # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($blockArray, @variables) = @_;                                            # Block array descriptor, variables
  @_ >= 2 or confess;

  $blockArray->bs->allocBlock($blockArray->address, @variables);
 }

sub Nasm::X86::BlockArray::dump($@)                                             # Dump a block array
 {my ($blockArray, @variables) = @_;                                            # Block array descriptor, variables
  @_ >= 1 or confess;
  my $b = $blockArray->bs;                                                      # Underlying byte string
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $blockArray->width;                                                   # The size of an entry in a block
  my $n = $blockArray->slots1;                                                  # The number of slots per block
  my $N = $blockArray->slots2;                                                  # The number of slots per block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First block

    PushR my @save = (zmm30, zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmmAsVariable(31, 0);                                    # Size of array
    PrintOutStringNL("Block Array");
    $size->out("Size: ", "  ");
    PrintOutRegisterInHex zmm31;

    If ($size > $n, sub                                                         # Array has secondary blocks
     {my $T = $size / $N;                                                       # Number of full blocks

      $T->for(sub                                                               # Print out each block
       {my ($index, $start, $next, $end) = @_;                                  # Execute body
        my $S = getDFromZmmAsVariable(31, ($index + 1) * $w);                   # Address secondary block from first block
        $b->getBlock($B, $S, 30);                                               # Get the secondary block
        $S->out("Full: ", "  ");
        PrintOutRegisterInHex zmm30;
       });

      my $lastBlockCount = $size % $N;                                          # Number of elements in the last block
      If ($lastBlockCount, sub                                                  # Print non empty last block
       {my $S = getDFromZmmAsVariable(31, ($T + 1) * $w);                       # Address secondary block from first block
        $b->getBlock($B, $S, 30);                                               # Get the secondary block
        $S->out("Last: ", "  ");
        PrintOutRegisterInHex zmm30;
       });
     });

    PopR @save;
   }  in => {bs => 3, first => 3};

  $s->call($blockArray->address, $blockArray->first, @variables);
 }

sub Nasm::X86::BlockArray::push($@)                                             # Push an element onto the array
 {my ($blockArray, @variables) = @_;                                            # Block array descriptor, variables
  @_ >= 2 or confess;
  my $b = $blockArray->bs;                                                      # Underlying byte string
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $blockArray->width;                                                   # The size of an entry in a block
  my $n = $blockArray->slots1;                                                  # The number of slots per block
  my $N = $blockArray->slots2;                                                  # The number of slots per block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element to be inserted

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmmAsVariable(31, 0);                                    # Size of array

    If ($size < $n, sub                                                         # Room in the first block
     {$E       ->putDIntoZmm(31, ($size + 1) * $w);                             # Place element
      ($size+1)->putDIntoZmm(31, 0);                                            # Update size
      $b       ->putBlock($B, $F, 31);                                          # Put the first block back into memory
      Jmp $success;                                                             # Element successfully inserted in first block
     });

    If ($size == $n, sub                                                        # Migrate the first block to the second block and fill in the last slot
     {PushR my @save = (rax, k7, zmm30);
      Mov rax, -2;                                                              # Load compression mask
      Kmovq k7, rax;                                                            # Set  compression mask
      Vpcompressd "zmm30{k7}{z}", zmm31;                                        # Compress first block into second block
      ClearRegisters zmm31;                                                     # Clear first block
      ($size+1)->putDIntoZmm(31, 0);                                            # Save new size in first block
      $b  ->allocBlock(my $new = Vq(offset));                                   # Allocate new block
      $new->putDIntoZmm(31, $w);                                                # Save offset of second block in first block
      $E  ->putDIntoZmm(30, $W - 1 * $w);                                       # Place new element
      $b  ->putBlock($B, $new, 30);                                             # Put the second block back into memory
      $b  ->putBlock($B, $F,   31);                                             # Put the first  block back into memory
      PopR @save;
      Jmp $success;                                                             # Element successfully inserted in second block
     });

    If ($size <= $N * ($N - 1), sub                                             # Still within two levels
     {If ($size % $N == 0, sub                                                  # New secondary block needed
       {PushR my @save = (rax, zmm30);
        $b->allocBlock(my $new = Vq(offset));                                   # Allocate new block
        $E       ->putDIntoZmm(30, 0);                                          # Place new element last in new second block
        ($size+1)->putDIntoZmm(31, 0);                                          # Save new size in first block
        $new     ->putDIntoZmm(31, ($size / $N + 1) * $w);                      # Address new second block from first block
        $b       ->putBlock($B, $new, 30);                                      # Put the second block back into memory
        $b       ->putBlock($B, $F,   31);                                      # Put the first  block back into memory
        PopR @save;
        Jmp $success;                                                           # Element successfully inserted in second block
       });

      if (1)                                                                    # Continue with existing secondary block
       {PushR my @save = (rax, r14, zmm30);
        my $S = getDFromZmmAsVariable(31, ($size / $N + 1) * $w);               # Offset of second block in first block
        $b       ->getBlock($B, $S, 30);                                        # Get the second block
        $E       ->putDIntoZmm(30, ($size % $N) * $w);                          # Place new element last in new second block
        ($size+1)->putDIntoZmm(31, 0);                                          # Save new size in first block
        $b       ->putBlock($B, $S, 30);                                        # Put the second block back into memory
        $b       ->putBlock($B, $F, 31);                                        # Put the first  block back into memory
        PopR @save;
        Jmp $success;                                                           # Element successfully inserted in second block
       }
     });

    SetLabel $success;
    PopR @save;
   }  in => {bs => 3, first => 3, element => 3};

  $s->call($blockArray->address, $blockArray->first, @variables);
 }

sub Nasm::X86::BlockArray::pop($@)                                              # Pop an element from an array
 {my ($blockArray, @variables) = @_;                                            # Block array descriptor, variables
  @_ >= 2 or confess;
  my $b = $blockArray->bs;                                                      # Underlying byte string
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $blockArray->width;                                                   # The size of an entry in a block
  my $n = $blockArray->slots1;                                                  # The number of slots per block
  my $N = $blockArray->slots2;                                                  # The number of slots per block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element being popped

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmmAsVariable(31, 0);                                    # Size of array

    If ($size > 0, sub                                                          # Array has elements
     {If ($size <= $n, sub                                                      # In the first block
       {$E       ->getDFromZmm(31, $size * $w);                                 # Get element
        ($size-1)->putDIntoZmm(31, 0);                                          # Update size
        $b       ->putBlock($B, $F, 31);                                        # Put the first block back into memory
        Jmp $success;                                                           # Element successfully retrieved from secondary block
       });

      If ($size == $N, sub                                                      # Migrate the second block to the first block now that the last slot is empty
       {PushR my @save = (rax, k7, zmm30);
        my $S = getDFromZmmAsVariable(31, $w);                                  # Offset of second block in first block
        $b->getBlock($B, $S, 30);                                               # Get the second block
        $E->getDFromZmm(30, $n * $w);                                           # Get element from second block
        Mov rax, -2;                                                            # Load expansion mask
        Kmovq k7, rax;                                                          # Set  expansion mask
        Vpexpandd "zmm31{k7}{z}", zmm30;                                        # Expand second block into first block
        ($size-1)->putDIntoZmm(31, 0);                                          # Save new size in first block
        $b  -> putBlock($B, $F, 31);                                            # Save the first block
        $b  ->freeBlock($B, offset=>$S);                                        # Free the now redundant second block
        PopR @save;
        Jmp $success;                                                           # Element successfully retrieved from secondary block
       });

      If ($size <= $N * ($N - 1), sub                                           # Still within two levels
       {If ($size % $N == 1, sub                                                # Secondary block can be freed
         {PushR my @save = (rax, zmm30);
          my $S = getDFromZmmAsVariable(31, ($size / $N + 1) * $w);             # Address secondary block from first block
          $b       ->getBlock($B, $S, 30);                                      # Load secondary block
          $E->getDFromZmm(30, 0);                                               # Get first element from secondary block
          Vq(zero, 0)->putDIntoZmm(31, ($size / $N + 1) * $w);                  # Zero at offset of secondary block in first block
          ($size-1)->putDIntoZmm(31, 0);                                        # Save new size in first block
          $b       ->freeBlock($B, offset=>$S);                                 # Free the secondary block
          $b       ->putBlock ($B, $F, 31);                                     # Put the first  block back into memory
          PopR @save;
          Jmp $success;                                                         # Element successfully retrieved from secondary block
         });

        if (1)                                                                  # Continue with existing secondary block
         {PushR my @save = (rax, r14, zmm30);
          my $S = getDFromZmmAsVariable(31, (($size-1) / $N + 1) * $w);             # Offset of secondary block in first block
          $b       ->getBlock($B, $S, 30);                                      # Get the secondary block
          $E       ->getDFromZmm(30, (($size - 1)  % $N) * $w);             # Get element from secondary block
          ($size-1)->putDIntoZmm(31, 0);                                        # Save new size in first block
          $b       ->putBlock($B, $S, 30);                                      # Put the secondary block back into memory
          $b       ->putBlock($B, $F, 31);                                      # Put the first  block back into memory
          PopR @save;
          Jmp $success;                                                         # Element successfully retrieved from secondary block
         }
       });
     });

    SetLabel $success;
    PopR @save;
   }  in => {bs => 3, first => 3}, out => {element => 3};

  $s->call($blockArray->address, $blockArray->first, @variables);
 }

sub Nasm::X86::BlockArray::get($@)                                              # Get an element from the array
 {my ($blockArray, @variables) = @_;                                            # Block array descriptor, variables
  @_ >= 3 or confess;
  my $b = $blockArray->bs;                                                      # Underlying byte string
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $blockArray->width;                                                   # The size of an entry in a block
  my $n = $blockArray->slots1;                                                  # The number of slots in the first block
  my $N = $blockArray->slots2;                                                  # The number of slots in the secondary blocks

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element to be returned
    my $I = $$p{index};                                                         # Index of the element to be returned

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmmAsVariable(31, 0);                                    # Size of array

    If ($I < $size, sub                                                         # Index is in array
     {If ($size <= $n, sub                                                      # Element is in the first block
       {$E->getDFromZmm(31, ($I + 1) * $w);                                     # Get element
        Jmp $success;                                                           # Element successfully inserted in first block
       });

      If ($size <= $N * ($N - 1), sub                                           # Still within two levels
       {my $S = getDFromZmmAsVariable(31, ($I / $N + 1) * $w);                  # Offset of second block in first block
        $b->getBlock($B, $S, 31);                                               # Get the second block
        $E->getDFromZmm(31, ($I % $N) * $w);                                    # Offset of element in second block
        Jmp $success;                                                           # Element successfully inserted in second block
       });
     });

    PrintErrString "Index out of bounds on get from array, ";                   # Array index out of bounds
    $I->err("Index: "); PrintErrString "  "; $size->errNL("Size: ");
    Exit(1);

    SetLabel $success;
    PopR @save;
   }  in => {bs => 3, first => 3, index => 3}, out => {element => 3};

  $s->call($blockArray->address, $blockArray->first, @variables);
 }

sub Nasm::X86::BlockArray::put($@)                                              # Put an element into an array as long as it is with in its limits established by pushing.
 {my ($blockArray, @variables) = @_;                                            # Block array descriptor, variables
  @_ >= 3 or confess;
  my $b = $blockArray->bs;                                                      # Underlying byte string
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $blockArray->width;                                                   # The size of an entry in a block
  my $n = $blockArray->slots1;                                                  # The number of slots in the first block
  my $N = $blockArray->slots2;                                                  # The number of slots in the secondary blocks

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element to be added
    my $I = $$p{index};                                                         # Index of the element to be inserted

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmmAsVariable(31, 0);                                    # Size of array
    If ($I < $size, sub                                                         # Index is in array
     {If ($size <= $n, sub                                                      # Element is in the first block
       {$E->putDIntoZmm(31, ($I + 1) * $w);                                     # Put element
        $b->putBlock($B, $F, 31);                                               # Get the first block
        Jmp $success;                                                           # Element successfully inserted in first block
       });

      If ($size <= $N * ($N - 1), sub                                           # Still within two levels
       {my $S = getDFromZmmAsVariable(31, ($I / $N + 1) * $w);                  # Offset of second block in first block
        $b->getBlock($B, $S, 31);                                               # Get the second block
        $E->putDIntoZmm(31, ($I % $N) * $w);                                    # Put the element into the second block in first block
        $b->putBlock($B, $S, 31);                                               # Get the first block
        Jmp $success;                                                           # Element successfully inserted in second block
       });
     });

    PrintErrString "Index out of bounds on put to array, ";                     # Array index out of bounds
    $I->err("Index: "); PrintErrString "  "; $size->errNL("Size: ");
    Exit(1);

    SetLabel $success;
    PopR @save;
   }  in => {bs => 3, first => 3, index => 3, element => 3};

  $s->call($blockArray->address, $blockArray->first, @variables);
 }

#D1 Assemble                                                                    # Assemble generated code

sub CallC($@)                                                                   # Call a C subroutine
 {my ($sub, @parameters) = @_;                                                  # Name of the sub to call, parameters
  my @order = (rdi, rsi, rdx, rcx, r8, r9, r15);
  PushR @order;

  for my $i(keys @parameters)                                                   # Load parameters into designated registers
   {Mov $order[$i], $parameters[$i];
   }

  Push rax;                                                                     # Align stack on 16 bytes
  Mov rax, rsp;                                                                 # Move stack pointer
  Shl rax, 60;                                                                  # Get lowest nibble
  Shr rax, 60;
  KeepFree rax;
  IfEq                                                                          # If we are 16 byte aligned push two twos
   {Mov rax, 2; Push rax; Push rax; KeepFree rax;
   }
  sub                                                                           # If we are not 16 byte aligned push one one.
   {Mov rax, 1; Push rax; KeepFree rax;
   };

  if (ref($sub))                                                                # ?
   {Call $sub->start;
   }
  else                                                                          # Call named subroutine
   {Call $sub;
   }

  Pop r15;                                                                      # Decode and reset stack after 16 byte alignment
  Cmp r15, 2;                                                                   # Check for double push
  Pop r15;                                                                      # Single or double push
  IfEq {Pop r15};                                                               # Double push
  PopR @order;
 }

sub Extern(@)                                                                   # Name external references
 {my (@externalReferences) = @_;                                                # External references
  push @extern, @_;
 }

sub Link(@)                                                                     # Libraries to link with
 {my (@libraries) = @_;                                                         # External references
  push @link, @_;
 }

sub Start()                                                                     # Initialize the assembler
 {@bss = @data = @rodata = %rodata = %rodatas = %subroutines = @text = %Keep = %KeepStack = @extern = @link = ();

  $Labels = 0;
  $ScopeCurrent = undef;
 }

sub Exit(;$)                                                                    # Exit with the specified return code or zero if no return code supplied.  Assemble() automatically adds a call to Exit(0) if the last operation in the program is not a call to Exit.
 {my ($c) = @_;                                                                 # Return code
  if (@_ == 0 or $c == 0)
   {Comment "Exit code: 0";
    KeepFree  rdi;
    Mov rdi, 0;
   }
  elsif (@_ == 1)
   {Comment "Exit code: $c";
    KeepFree  rdi;
    Mov rdi, $c;
   }
  KeepFree rax, rdi;
  Mov rax, 60;
  Syscall;
 }

my $LocateIntelEmulator;                                                        # Location of Intel Software Development Emulator

sub LocateIntelEmulator()                                                       #P Locate the Intel Software Development Emulator
 {my @locations = qw(/var/isde/sde64 sde/sde64 ./sde64);                        # Locations at which we might find the emulator

  return $LocateIntelEmulator if defined $LocateIntelEmulator;                  # Location has already been discovered

  for my $l(@locations)                                                         # Try each locations
   {return $LocateIntelEmulator = $l if -e $l;                                  # Found it - cache and return
   }

  if (qx(sde64 -version) =~ m(Intel.R. Software Development Emulator))          # Try path
   {return $LocateIntelEmulator = "sde64";
   }

  undef                                                                         # Emulator  not found
 }

my $assembliesPerformed = 0;                                                    # Number of assemblies performed
my $totalBytesAssembled = 0;                                                    # Estimate the size of the output programs

sub Assemble(%)                                                                 # Assemble the generated code
 {my (%options) = @_;                                                           # Options
  Exit 0 unless @text > 4 and $text[-4] =~ m(Exit code:);                       # Exit with code 0 if no other exit has been taken
  my $debug = $options{debug}//0;                                               # 0 - none (minimal output), 1 - normal (debug output and confess of failure), 2 - failures (debug output and no confess on failure) .

  my $k = $options{keep};                                                       # Keep the executable
  my $r = join "\n", map {s/\s+\Z//sr}   @rodata;
  my $d = join "\n", map {s/\s+\Z//sr}   @data;
  my $b = join "\n", map {s/\s+\Z//sr}   @bss;
  my $t = join "\n", map {s/\s+\Z//sr}   @text;
  my $x = join "\n", map {qq(extern $_)} @extern;
  my $L = join " ",  map {qq(-l$_)}      @link;
  my $a = <<END;
section .rodata
  $r
section .data
  $d
section .bss
  $b
section .text
$x
global _start, main
  _start:
  main:
  push rbp     ; function prologue
  mov  rbp,rsp
  $t
END

  my $c    = owf(q(z.asm), $a);                                                 # Source file
  my $e    = $k // q(z);                                                        # Executable file
  my $l    = q(z.txt);                                                          # Assembler listing
  my $o    = q(z.o);                                                            # Object file

  if (!confirmHasCommandLineCommand(q(nasm)))                                   # Check for network assembler
   {my $L = fpf(currentDirectory, $l);
    say STDERR <<END;
Assember code written to the following file:

$L

I cannot compile this file because you do not have Nasm installed, see:

https://www.nasm.us/
END
    return;
   }

  my $emulator = exists $options{emulator} ? $options{emulator} : 1;            # Emulate by default unless told otherwise
  my $sde      = LocateIntelEmulator;                                           # Locate the emulator

  if (!$k and $emulator and !$sde)                                              # Complain about the emulator if we are going to run and we have not suppressed the emulator and the emulator is not present
   {my $E = fpf(currentDirectory, $e);
    say STDERR <<END;
Executable written to the following file:

$E

I am going to run this without using the Intel emulator. Your program will
crash if it contains instructions not implemented on your computer.

You can get the Intel emulator from:

https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2

To avoid this message, use option(1) below to produce just an executable
without running it, or use the option(2) to run without the emulator:

(1) Assemble(keep=>"executable file name")

(2) Assemble(emulator=>0)
END
    $emulator = 0;
   }

  my $I = @link ? $interpreter : '';                                            # Interpreter only required if calling C
  my $cmd  = qq(nasm -f elf64 -g -l $l -o $o $c && ld $I $L -o $e $o && chmod 744 $e);# Assemble
  my $o1 = 'zzzOut.txt';
  my $o2 = 'zzzErr.txt';
  my $out  = $k ? '' : "1>$o1";
  my $err  = $k ? '' : "2>$o2";
  my $exec = $emulator                                                          # Execute with or without the emulator
             ? qq($sde -ptr-check -- ./$e $err $out)
             :                    qq(./$e $err $out);

  $cmd .= qq( && $exec) unless $k;                                              # Execute automatically unless suppressed by user

  $assembliesPerformed++;
  say STDERR qq($assembliesPerformed: $cmd);
  my $R    = qx($cmd);

  if (!$k and $debug == 0)                                                      # Print errors if not debugging
   {say STDERR readFile($o2);
   }

  if (!$k and $debug == 1)                                                      # Print files if soft debugging
   {say STDERR readFile($o1) =~ s(0) ( )gsr;
    say STDERR readFile($o2);
   }

  confess "Failed $?" if $debug < 2 and $?;                                     # Check that the assembly succeeded

  if (!$k and $debug < 2 and -e $o2 and readFile($o2) =~ m(SDE ERROR:)s)        # Emulator detected an error
   {confess "SDE ERROR\n".readFile($o2);
   }

  $totalBytesAssembled += fileSize $c;                                          # Estimate the size of the output programs
  unlink $o;                                                                    # Delete files
  unlink $e unless $k;                                                          # Delete executable unless asked to keep it
  $totalBytesAssembled += fileSize $c;                                          # Estimate the size of the output program
  Start;                                                                        # Clear work areas for next assembly

  return $exec if $k;                                                           # Executable wanted

  if (defined(my $e = $options{eq}))                                            # Diff against expected
   {my $g = readFile($debug < 2 ? $o1 : $o2);
    if ($g ne $e)
     {my ($s, $G, $E) = stringsAreNotEqual($g, $e);
      if (length($s))
       {my $line = 1 + length($s =~ s([^\n])  ()gsr);
        my $char = 1 + length($s =~ s(\A.*\n) ()sr);
        say STDERR "Comparing wanted with got failed at line: $line, character: $char";
        say STDERR "Start:\n$s";
       }
      my $b1 = '+' x 80;
      my $b2 = '_' x 80;
      say STDERR "Want $b1\n", firstNChars($E, 80);
      say STDERR "Got  $b2\n", firstNChars($G, 80);
      confess "Test failed";                                                    # Test failed unless we are debugging test failures
     }
    return 1;                                                                   # Test passed
   }

  scalar(readFile($debug < 2 ? $o1 : $o2));                                     # stdout results unless stderr results requested
 }

sub removeNonAsciiChars($)                                                      #P Return a copy of the specified string with all the non ascii characters removed
 {my ($string) = @_;                                                            # String
  $string =~ s([^a-z0..9]) ()igsr;                                              # Remove non ascii characters
 }

sub totalBytesAssembled                                                         #P Total size in bytes of all files assembled during testing
 {$totalBytesAssembled
 }

#d
#-------------------------------------------------------------------------------
# Export - eeee
#-------------------------------------------------------------------------------

if (0)                                                                          # Print exports
 {my @e;
  for my $a(sort keys %Nasm::X86::)
   {next if $a =~ m(BAIL_OUT|BEGIN|DATA|confirmHasCommandLineCommand|currentDirectory|fff|fileMd5Sum|fileSize|findFiles|firstNChars|formatTable|fpe|fpf|genHash|lll|owf|pad|readFile|stringsAreNotEqual|stringMd5Sum|temporaryFile);
    next if $a =~ m(\AEXPORT);
    next if $a !~ m(\A[A-Z]) and !$Registers{$a};
    next if $a =~ m(::\Z);
    push @e, $a if $Nasm::X86::{$a} =~ m(\*Nasm::X86::);
   }
  say STDERR q/@EXPORT_OK    = qw(/.join(' ', @e).q/);/;
  exit;
 }

use Exporter qw(import);

use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA          = qw(Exporter);
@EXPORT       = qw();
@EXPORT_OK    = qw(Add All8Structure AllocateAll8OnStack AllocateMemory And Assemble Bswap Bt Btc Btr Bts Bzhi Call CallC ClearMemory ClearRegisters ClearZF CloseFile Cmova Cmovae Cmovb Cmovbe Cmovc Cmove Cmovg Cmovge Cmovl Cmovle Cmovna Cmovnae Cmovnb Cmp Comment ConcatenateShortStrings Copy CopyMemory CreateByteString Cstrlen DComment Db Dbwdq Dd Dec Decrement Dq Ds Dw Exit Extern Float32 Float64 For ForEver ForIn Fork FreeMemory GetLengthOfShortString GetPPid GetPid GetPidInHex GetUid Hash ISA Idiv If IfEq IfGe IfGt IfLe IfLt IfNe IfNz Imul Inc Increment InsertIntoXyz Isa Ja Jae Jb Jbe Jc Jcxz Je Jecxz Jg Jge Jl Jle Jmp Jna Jnae Jnb Jnbe Jnc Jne Jng Jnge Jnl Jnle Jno Jnp Jns Jnz Jo Jp Jpe Jpo Jrcxz Js Jz Kaddb Kaddd Kaddq Kaddw Kandb Kandd Kandnb Kandnd Kandnq Kandnw Kandq Kandw Keep KeepFree KeepPop KeepPush KeepReturn KeepSet Kmovb Kmovd Kmovq Kmovw Knotb Knotd Knotq Knotw Korb Kord Korq Kortestb Kortestd Kortestq Kortestw Korw Kshiftlb Kshiftld Kshiftlq Kshiftlw Kshiftrb Kshiftrd Kshiftrq Kshiftrw Ktestb Ktestd Ktestq Ktestw Kunpckb Kunpckd Kunpckq Kunpckw Kxnorb Kxnord Kxnorq Kxnorw Kxorb Kxord Kxorq Kxorw Label Lea Link LoadShortStringFromMemoryToZmm LoadShortStringFromMemoryToZmm2 LoadTargetZmmFromSourceZmm LoadZmmFromMemory LocalData LocateIntelEmulator Lzcnt Macro MaximumOfTwoRegisters MinimumOfTwoRegisters Minus Mov Movdqa Mulpd Neg Not OpenRead OpenWrite Or PeekR Pextrb Pextrd Pextrq Pextrw Pi32 Pi64 Pinsrb Pinsrd Pinsrq Pinsrw Plus Pop PopR PopRR Popfq PrintErrMemory PrintErrMemoryInHex PrintErrMemoryInHexNL PrintErrMemoryNL PrintErrNL PrintErrRaxInHex PrintErrRegisterInHex PrintErrString PrintErrStringNL PrintMemory PrintMemoryInHex PrintNL PrintOutMemory PrintOutMemoryInHex PrintOutMemoryInHexNL PrintOutMemoryNL PrintOutNL PrintOutRaxInHex PrintOutRaxInReverseInHex PrintOutRegisterInHex PrintOutRegistersInHex PrintOutRflagsInHex PrintOutRipInHex PrintOutString PrintOutStringNL PrintOutZF PrintRaxInHex PrintRegisterInHex PrintString Pslldq Psrldq Push PushR PushRR Pushfq RComment Rb Rbwdq Rd Rdtsc ReadFile ReadTimeStampCounter RegisterSize ReorderSyscallRegisters ReorderXmmRegisters RestoreFirstFour RestoreFirstFourExceptRax RestoreFirstFourExceptRaxAndRdi RestoreFirstSeven RestoreFirstSevenExceptRax RestoreFirstSevenExceptRaxAndRdi Ret Rq Rs Rw SaveFirstFour SaveFirstSeven Scope ScopeEnd SetLabel SetLengthOfShortString SetMaskRegister SetRegisterToMinusOne SetZF Seta Setae Setb Setbe Setc Sete Setg Setge Setl Setle Setna Setnae Setnb Setnbe Setnc Setne Setng Setnge Setnl Setno Setnp Setns Setnz Seto Setp Setpe Setpo Sets Setz Shl Shr Start StatSize Structure Sub Subroutine Syscall TODO Test Tzcnt UnReorderSyscallRegisters UnReorderXmmRegisters VERSION Vaddd Vaddpd Variable Vb Vcvtudq2pd Vcvtudq2ps Vcvtuqq2pd Vd Vdpps Vgetmantps Vmovd Vmovdqa32 Vmovdqa64 Vmovdqu Vmovdqu32 Vmovdqu64 Vmovdqu8 Vmovq Vmulpd Vpbroadcastb Vpbroadcastd Vpbroadcastq Vpbroadcastw Vpcmpub Vpcmpud Vpcmpuq Vpcmpuw Vpcompressd Vpcompressq Vpexpandd Vpexpandq Vpextrb Vpextrd Vpextrq Vpextrw Vpinsrb Vpinsrd Vpinsrq Vpinsrw Vpmullb Vpmulld Vpmullq Vpmullw Vprolq Vpsubb Vpsubd Vpsubq Vpsubw Vpxorq Vq Vr Vsqrtpd Vw Vx VxyzInit Vy Vz WaitPid Xchg Xor ah al ax bh bl bp bpl bx ch cl cs cx dh di dil dl ds dx eax ebp ebx ecx edi edx es esi esp fs gs k0 k1 k2 k3 k4 k5 k6 k7 mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7 r10 r10b r10d r10l r10w r11 r11b r11d r11l r11w r12 r12b r12d r12l r12w r13 r13b r13d r13l r13w r14 r14b r14d r14l r14w r15 r15b r15d r15l r15w r8 r8b r8d r8l r8w r9 r9b r9d r9l r9w rax rbp rbx rcx rdi rdx rflags rip rsi rsp si sil sp spl ss st0 st1 st2 st3 st4 st5 st6 st7 xmm0 xmm1 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm2 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm3 xmm30 xmm31 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 ymm0 ymm1 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm2 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm3 ymm30 ymm31 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 zmm0 zmm1 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm2 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm3 zmm30 zmm31 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9);
%EXPORT_TAGS  = (all => [@EXPORT, @EXPORT_OK]);

# podDocumentation
=pod

=encoding utf-8

=head1 Name

Nasm::X86 - Generate X86 assembler code using Perl as a macro pre-processor.

=head1 Synopsis

Write and execute x64 instructions using Perl as a macro assembler as shown in
the following examples.

=head2 Examples

=head3 Avx512 instructions

Use avx512 instructions to do 64 comparisons in parallel:

  my $P = "2F";                                                                 # Value to test for
  my $l = Rb 0;  Rb $_ for 1..RegisterSize zmm0;                                # 0..63
  Vmovdqu8 zmm0, "[$l]";                                                        # Load data to test
  PrintOutRegisterInHex zmm0;

  Mov rax, "0x$P";                                                              # Broadcast the value to be tested
  Vpbroadcastb zmm1, rax;
  PrintOutRegisterInHex zmm1;

  for my $c(0..7)                                                               # Each possible test
   {my $m = "k$c";
    Vpcmpub $m, zmm1, zmm0, $c;
    PrintOutRegisterInHex $m;
   }

  Kmovq rax, k0;                                                                # Count the number of trailing zeros in k0
  Tzcnt rax, rax;
  PrintOutRegisterInHex rax;

  is_deeply Assemble, <<END;                                                    # Assemble and test
  zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  zmm1: 2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F
    k0: 0000 8000 0000 0000
    k1: FFFF 0000 0000 0000
    k2: FFFF 8000 0000 0000
    k3: 0000 0000 0000 0000
    k4: FFFF 7FFF FFFF FFFF
    k5: 0000 FFFF FFFF FFFF
    k6: 0000 7FFF FFFF FFFF
    k7: FFFF FFFF FFFF FFFF
   rax: 0000 0000 0000 002F
END

=head3 Dynamic string held in an arena

Create a dynamic byte string, add some content to it, write the byte string to
stdout:

  my $a = CreateByteString;                                                     # Create a string
  my $b = CreateByteString;                                                     # Create a string
  $a->q('aa');
  $b->q('bb');
  $a->q('AA');
  $b->q('BB');
  $a->q('aa');
  $b->q('bb');
  $a->out;
  $b->out;
  PrintOutNL;
  is_deeply Assemble, <<END;                                                    # Assemble and execute
aaAAaabbBBbb
END

=head3 Process management

Start a child process and wait for it, printing out the process identifiers of
each process involved:

  Fork;                                                                         # Fork

  Test rax,rax;
  If                                                                            # Parent
   {Mov rbx, rax;
    WaitPid;
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;
    GetPid;                                                                     # Pid of parent as seen in parent
    Mov rcx,rax;
    PrintOutRegisterInHex rcx;
   }
  sub                                                                           # Child
   {Mov r8,rax;
    PrintOutRegisterInHex r8;
    GetPid;                                                                     # Child pid as seen in child
    Mov r9,rax;
    PrintOutRegisterInHex r9;
    GetPPid;                                                                    # Parent pid as seen in child
    Mov r10,rax;
    PrintOutRegisterInHex r10;
   };

  my $r = Assemble;

  #    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
  #    r9: 0000 0000 0003 0C63   #2 Pid of child
  #   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
  #   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
  #   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
  #   rcx: 0000 0000 0003 0C60   #6 Pid of parent

=head3 Read a file

Read this file:

  ReadFile(Vq(file, Rs($0)), (my $s = Vq(size)), my $a = Vq(address));          # Read file
  $a->setReg(rax);                                                              # Address of file in memory
  $s->setReg(rdi);                                                              # Length  of file in memory
  PrintOutMemory;                                                               # Print contents of memory to stdout

  my $r = Assemble(1 => (my $f = temporaryFile));                               # Assemble and execute
  ok fileMd5Sum($f) eq fileMd5Sum($0);                                          # Output contains this file


=head3 Call functions in Libc

Call B<C> functions by naming them as external and including their library:

  my $format = Rs "Hello %s\n";
  my $data   = Rs "World";

  Extern qw(printf exit malloc strcpy); Link 'c';

  CallC 'malloc', length($format)+1;
  Mov r15, rax;
  CallC 'strcpy', r15, $format;
  CallC 'printf', r15, $data;
  CallC 'exit', 0;

  ok Assemble(eq => <<END);
Hello World
END

=head2 Installation

The Intel Software Development Emulator will be required if you do not have a
computer with the avx512 instruction set and wish to execute code containing
these instructions. For details see:

L<https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2>


The Networkwide Assembler is required to assemble the code produced  For full
details see:

L<https://github.com/philiprbrenan/NasmX86/blob/main/.github/workflows/main.yml>

=head2 Execution Options

The L</Assemble(%)> function takes the keywords described below to
control assembly and execution of the assembled code:

L</Assemble(%)> runs the generated program after a successful assembly
unless the B<keep> option is specified. The output on B<stdout> is captured in
file B<zzzOut.txt> and that on B<stderr> is captured in file B<zzzErr.txt>.

The amount of output displayed is controlled by the B<debug> keyword.

The B<eq> keyword can be used to test that the output by the run.

The output produced by the program execution is returned as the result of the
L</Assemble(%)> function.

=head3 Keep

To produce a named executable without running it, specify:

 keep=>"executable file name"

=head3 Emulator

To run the executable produced by L</Assemble(%)> without the Intel
emulator, which is used by default if it is present, specify:

 emulator=>0

=head3 eq

The B<eq> keyword supplies the expected output from the execution of the
assembled program.  If the expected output is not obtained on B<stdout> then we
confess and stop further testing. Output on B<stderr> is ignored for test
purposes.

The point at which the wanted output diverges from the output actually got is
displayed to assist debugging as in:

  Comparing wanted with got failed at line: 4, character: 22
  Start:
      k7: 0000 0000 0000 0001
      k6: 0000 0000 0000 0003
      k5: 0000 0000 0000 0007
      k4: 0000 0000 000
  Want ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
  1 0002
      k3: 0000 0000 0000 0006
      k2: 0000 0000 0000 000E
      k1: 0000 0000
  Got  ________________________________________________________________________________
  0 0002
      k3: 0000 0000 0000 0006
      k2: 0000 0000 0000 000E
      k1: 0000 0000


=head3 Debug

The debug keyword controls how much output is printed after each assemble and
run.

  debug => 0

produces no output unless the B<eq> keyword was specified and the actual output
fails to match the expected output. If such a test fails we L<Carp::confess>.

  debug => 1

shows all the output produces and conducts the test specified by the B<eq> is
present. If the test fails we L<Carp::confess>.

  debug => 2

shows all the output produces and conducts the test specified by the B<eq> is
present. If the test fails we continue rather than calling L<Carp::confess>.

=head1 Description

Generate X86 assembler code using Perl as a macro pre-processor.


Version "20210528".


The following sections describe the methods in each functional area of this
module.  For an alphabetic listing of all methods by name see L<Index|/Index>.



=head1 Data

Layout data

=head2 SetLabel($l)

Set a label in the code section

     Parameter  Description
  1  $l         Label

B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;

    SetLabel $l;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head2 Ds(@d)

Layout bytes in memory and return their label

     Parameter  Description
  1  @d         Data to be laid out

B<Example:>


    my $q = Rs('a'..'z');

    Mov rax, Ds('0'x64);                                                          # Output area  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Vmovdqu32(xmm0, "[$q]");                                                      # Load
    Vprolq   (xmm0,   xmm0, 32);                                                  # Rotate double words in quad words
    Vmovdqu32("[rax]", xmm0);                                                     # Save
    Mov rdi, 16;
    PrintOutMemory;

    ok Assemble =~ m(efghabcdmnopijkl)s;


=head2 Rs(@d)

Layout bytes in read only memory and return their label

     Parameter  Description
  1  @d         Data to be laid out

B<Example:>


    Comment "Print a string from memory";
    my $s = "Hello World";

    Mov rax, Rs($s);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rdi, length $s;
    PrintOutMemory;

    ok Assemble =~ m(Hello World);


    my $q = Rs('abababab');  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov(rax, 1);
    Mov(rbx, 2);
    Mov(rcx, 3);
    Mov(rdx, 4);
    Mov(r8,  5);
    Lea r9,  "[rax+rbx]";
    PrintOutRegistersInHex;

    my $r = Assemble;
    ok $r =~ m( r8: 0000 0000 0000 0005.* r9: 0000 0000 0000 0003.*rax: 0000 0000 0000 0001)s;
    ok $r =~ m(rbx: 0000 0000 0000 0002.*rcx: 0000 0000 0000 0003.*rdx: 0000 0000 0000 0004)s;


=head2 Db(@bytes)

Layout bytes in the data segment and return their label

     Parameter  Description
  1  @bytes     Bytes to layout

B<Example:>


    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Dw(@words)

Layout words in the data segment and return their label

     Parameter  Description
  1  @words     Words to layout

B<Example:>


    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Dd(@dwords)

Layout double words in the data segment and return their label

     Parameter  Description
  1  @dwords    Double words to layout

B<Example:>


    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Dq(@qwords)

Layout quad words in the data segment and return their label

     Parameter  Description
  1  @qwords    Quad words to layout

B<Example:>


    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Rb(@bytes)

Layout bytes in the data segment and return their label

     Parameter  Description
  1  @bytes     Bytes to layout

B<Example:>



    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Rw(@words)

Layout words in the data segment and return their label

     Parameter  Description
  1  @words     Words to layout

B<Example:>



    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Rd(@dwords)

Layout double words in the data segment and return their label

     Parameter  Description
  1  @dwords    Double words to layout

B<Example:>



    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Rq(@qwords)

Layout quad words in the data segment and return their label

     Parameter  Description
  1  @qwords    Quad words to layout

B<Example:>



    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


=head2 Float32($float)

32 bit float

     Parameter  Description
  1  $float     Float

=head2 Float64($float)

64 bit float

     Parameter  Description
  1  $float     Float

=head1 Registers

Operations on registers

=head2 Save and Restore

Saving and restoring registers via the stack

=head3 SaveFirstFour(@keep)

Save the first 4 parameter registers making any parameter registers read only

     Parameter  Description
  1  @keep      Registers to mark as read only

B<Example:>


    Mov rax, 1;
    Mov rdi, 1;

    SaveFirstFour;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;


    SaveFirstFour;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;


    SaveFirstFour;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 RestoreFirstFour()

Restore the first 4 parameter registers


B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;

    RestoreFirstFour;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 RestoreFirstFourExceptRax()

Restore the first 4 parameter registers except rax so it can return its value


B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;

    RestoreFirstFourExceptRax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 RestoreFirstFourExceptRaxAndRdi()

Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values


B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    RestoreFirstFourExceptRaxAndRdi;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 SaveFirstSeven()

Save the first 7 parameter registers


B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;

    SaveFirstSeven;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;

    SaveFirstSeven;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;

    SaveFirstSeven;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 RestoreFirstSeven()

Restore the first 7 parameter registers


B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;

    RestoreFirstSeven;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 RestoreFirstSevenExceptRax()

Restore the first 7 parameter registers except rax which is being used to return the result


B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;

    RestoreFirstSevenExceptRax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 RestoreFirstSevenExceptRaxAndRdi()

Restore the first 7 parameter registers except rax and rdi which are being used to return the results


B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;

    RestoreFirstSevenExceptRaxAndRdi;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END

    ok 8 == RegisterSize rax;


=head3 ReorderSyscallRegisters(@registers)

Map the list of registers provided to the 64 bit system call sequence

     Parameter   Description
  1  @registers  Registers

B<Example:>


    Mov rax, 1;  Mov rdi, 2;  Mov rsi,  3;  Mov rdx,  4;
    Mov r8,  8;  Mov r9,  9;  Mov r10, 10;  Mov r11, 11;


    ReorderSyscallRegisters   r8,r9;                                              # Reorder the registers for syscall  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;

    UnReorderSyscallRegisters r8,r9;                                              # Unreorder the registers to recover their original values
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;

    ok Assemble =~ m(rax:.*08.*rdi:.*9.*rax:.*1.*rdi:.*2.*)s;


=head3 UnReorderSyscallRegisters(@registers)

Recover the initial values in registers that were reordered

     Parameter   Description
  1  @registers  Registers

B<Example:>


    Mov rax, 1;  Mov rdi, 2;  Mov rsi,  3;  Mov rdx,  4;
    Mov r8,  8;  Mov r9,  9;  Mov r10, 10;  Mov r11, 11;

    ReorderSyscallRegisters   r8,r9;                                              # Reorder the registers for syscall
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;


    UnReorderSyscallRegisters r8,r9;                                              # Unreorder the registers to recover their original values  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;

    ok Assemble =~ m(rax:.*08.*rdi:.*9.*rax:.*1.*rdi:.*2.*)s;


=head3 ReorderXmmRegisters(@registers) = map {"xmm$_"} @_;)

Map the list of xmm registers provided to 0-31

     Parameter                        Description
  1  @registers) = map {"xmm$_"} @_;  Registers

B<Example:>


    my $t = GenTree(2,2);                                                         # Tree description
    $t->node->();                                                                 # Root
    Movdqa xmm1, xmm0;                                                            # Root is in xmm1

    if (1)                                                                        # New left node
     {$t->node->();                                                               # Node in xmm0
      Movdqa xmm2, xmm0;                                                          # Left is in xmm2

      cxr {$t->insertLeft->()} 1,2;                                               # Insert left under root
      cxr {$t->dump->("Left")} 2;                                                 # Left node after insertion
     }

    if (1)                                                                        # New right node in xmm0
     {$t->node->();
      Movdqa xmm3, xmm0;                                                          # Right is in xmm3

      cxr {$t->insertRight->()} 1,3;                                              # Insert left under root
      cxr {$t->dump->("Right")} 3;                                                # Right node after insertion
     }

    cxr
     {$t->dump->("Root");                                                         # Root node after insertions
      $t->isRoot->();
      IfNz {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushRR xmm0;                                                                  # Dump underlying  byte string
    PopRR rdi, rax;
    $t->byteString->dump;

    Exit;                                                                         # Return to operating system

    is_deeply Assemble, <<END;                                                    # Test tree so produced
  Left
  ArenaTreeNode at: 0000 0000 0000 00B0
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Right
  ArenaTreeNode at: 0000 0000 0000 0150
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Root
  ArenaTreeNode at: 0000 0000 0000 0010
     up: 0000 0000 0000 0000
   left: 0000 0000 0000 00B0
  right: 0000 0000 0000 0150
  root
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 01E0
  END


=head3 UnReorderXmmRegisters(@registers)

Recover the initial values in the xmm registers that were reordered

     Parameter   Description
  1  @registers  Registers

B<Example:>


    my $t = GenTree(2,2);                                                         # Tree description
    $t->node->();                                                                 # Root
    Movdqa xmm1, xmm0;                                                            # Root is in xmm1

    if (1)                                                                        # New left node
     {$t->node->();                                                               # Node in xmm0
      Movdqa xmm2, xmm0;                                                          # Left is in xmm2

      cxr {$t->insertLeft->()} 1,2;                                               # Insert left under root
      cxr {$t->dump->("Left")} 2;                                                 # Left node after insertion
     }

    if (1)                                                                        # New right node in xmm0
     {$t->node->();
      Movdqa xmm3, xmm0;                                                          # Right is in xmm3

      cxr {$t->insertRight->()} 1,3;                                              # Insert left under root
      cxr {$t->dump->("Right")} 3;                                                # Right node after insertion
     }

    cxr
     {$t->dump->("Root");                                                         # Root node after insertions
      $t->isRoot->();
      IfNz {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushRR xmm0;                                                                  # Dump underlying  byte string
    PopRR rdi, rax;
    $t->byteString->dump;

    Exit;                                                                         # Return to operating system

    is_deeply Assemble, <<END;                                                    # Test tree so produced
  Left
  ArenaTreeNode at: 0000 0000 0000 00B0
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Right
  ArenaTreeNode at: 0000 0000 0000 0150
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Root
  ArenaTreeNode at: 0000 0000 0000 0010
     up: 0000 0000 0000 0000
   left: 0000 0000 0000 00B0
  right: 0000 0000 0000 0150
  root
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 01E0
  END


=head3 RegisterSize($r)

Return the size of a register

     Parameter  Description
  1  $r         Register

B<Example:>


    Mov rax, 1;
    Mov rdi, 1;
    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSeven;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFour;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRax;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRax;
    PrintOutRegisterInHex rax, rdi;

    SaveFirstFour;
    Mov rax, 2;
    Mov rdi, 2;
    SaveFirstSeven;
    Mov rax, 3;
    Mov rdi, 4;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstSevenExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;
    RestoreFirstFourExceptRaxAndRdi;
    PrintOutRegisterInHex rax, rdi;

    Bswap rax;
    PrintOutRegisterInHex rax;

    my $l = Label;
    Jmp $l;
    SetLabel $l;

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0002
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0001
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0001
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0000 0000 0000 0003
     rdi: 0000 0000 0000 0004
     rax: 0300 0000 0000 0000
  END


    ok 8 == RegisterSize rax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲



=head3 ClearRegisters(@registers)

Clear registers by setting them to zero

     Parameter   Description
  1  @registers  Registers

B<Example:>


    Mov rax,1;
    Kmovq k0,  rax;
    Kaddb k0,  k0, k0;
    Kaddb k0,  k0, k0;
    Kaddb k0,  k0, k0;
    Kmovq rax, k0;
    PushR k0;

    ClearRegisters k0;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Kmovq k1, k0;
    PopR  k0;
    PrintOutRegisterInHex k0;
    PrintOutRegisterInHex k1;

    ok Assemble =~ m(k0: 0000 0000 0000 0008.*k1: 0000 0000 0000 0000)s;


=head3 SetRegisterToMinusOne($register)

Set the specified register to -1

     Parameter  Description
  1  $register  Register to set

B<Example:>



    SetRegisterToMinusOne rax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    ok Assemble =~ m(rax: FFFF FFFF FFFF FFFF);


=head3 SetMaskRegister($mask, $start, $length)

Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

     Parameter  Description
  1  $mask      Mask register to set
  2  $start     Register containing start position or 0 for position 0
  3  $length    Register containing end position

B<Example:>


    Mov rax, 8;
    Mov rsi, -1;

    Inc rsi; SetMaskRegister(k0, rax, rsi); PrintOutRegisterInHex k0;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Inc rsi; SetMaskRegister(k1, rax, rsi); PrintOutRegisterInHex k1;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Inc rsi; SetMaskRegister(k2, rax, rsi); PrintOutRegisterInHex k2;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Inc rsi; SetMaskRegister(k3, rax, rsi); PrintOutRegisterInHex k3;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Inc rsi; SetMaskRegister(k4, rax, rsi); PrintOutRegisterInHex k4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Inc rsi; SetMaskRegister(k5, rax, rsi); PrintOutRegisterInHex k5;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Inc rsi; SetMaskRegister(k6, rax, rsi); PrintOutRegisterInHex k6;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Inc rsi; SetMaskRegister(k7, rax, rsi); PrintOutRegisterInHex k7;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    is_deeply Assemble, <<END;
      k0: 0000 0000 0000 0000
      k1: 0000 0000 0000 0100
      k2: 0000 0000 0000 0300
      k3: 0000 0000 0000 0700
      k4: 0000 0000 0000 0F00
      k5: 0000 0000 0000 1F00
      k6: 0000 0000 0000 3F00
      k7: 0000 0000 0000 7F00
  END


=head3 SetZF()

Set the zero flag


B<Example:>



    SetZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutZF;
    ClearZF;
    PrintOutZF;

    SetZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutZF;

    SetZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutZF;
    ClearZF;
    PrintOutZF;

    ok Assemble =~ m(ZF=1.*ZF=0.*ZF=1.*ZF=1.*ZF=0)s;


=head3 ClearZF()

Clear the zero flag


B<Example:>


    SetZF;
    PrintOutZF;

    ClearZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutZF;
    SetZF;
    PrintOutZF;
    SetZF;
    PrintOutZF;

    ClearZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutZF;

    ok Assemble =~ m(ZF=1.*ZF=0.*ZF=1.*ZF=1.*ZF=0)s;


=head2 Tracking

Track the use of registers so that we do not accidently use unset registers or write into registers that are already in use.

=head3 Keep(@target)

Mark free registers so that they are not updated until we Free them or complain if the register is already in use.

     Parameter  Description
  1  @target    Registers to keep

=head3 KeepSet($target)

Confirm that the specified registers are in use

     Parameter  Description
  1  $target    Registers to keep

=head3 KeepPush(@target)

Push the current status of the specified registers and then mark them as free

     Parameter  Description
  1  @target    Registers to keep

=head3 KeepPop(@target)

Reset the status of the specified registers to the status quo ante the last push

     Parameter  Description
  1  @target    Registers to keep

=head3 KeepReturn(@target)

Pop the specified register and mark it as in use to effect a subroutine return with this register.

     Parameter  Description
  1  @target    Registers to return

=head3 KeepFree(@target)

Free registers so that they can be reused

     Parameter  Description
  1  @target    Registers to free

=head2 Arithmetic

Arithmetic operations on registers

=head3 Copy($target, $source)

Copy the source to the target register

     Parameter  Description
  1  $target    Target register
  2  $source    Source expression

B<Example:>


    my $s = Rb(13, 1..13);
    my $t = Rb(1..64);
    my $source = rax;                                                             # Address to load from
    my $start  = rsi;                                                             # Start position in the zmm register
    my $length = rdi;                                                             # Length of copy


    Copy $source, $s;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    LoadShortStringFromMemoryToZmm 0, $s;                                         # Load a sample string
    KeepFree $source;
    PrintOutRegisterInHex xmm0;


    LoadZmmFromMemory 0, Increment(GetLengthOfShortString($start, 0)), Copy($length, 1), Copy($source, $t);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex xmm0;

    LoadZmmFromMemory 0, $start, $length, $source;
    PrintOutRegisterInHex xmm0;

    KeepFree $length;

    LoadZmmFromMemory 0, $start, Minus($length, Copy(r13, 56), $start), $source;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    SetLengthOfShortString 0, sil;                                                # Set current length of zmm0
    PrintOutRegisterInHex xmm0, zmm0;

    is_deeply Assemble, <<END;
    xmm0: 0000 0D0C 0B0A 0908   0706 0504 0302 010D
    xmm0: 0001 0D0C 0B0A 0908   0706 0504 0302 010D
    xmm0: 0201 0D0C 0B0A 0908   0706 0504 0302 010D
    xmm0: 0201 0D0C 0B0A 0908   0706 0504 0302 0138
    zmm0: 0000 0000 0000 0000   2A29 2827 2625 2423   2221 201F 1E1D 1C1B   1A19 1817 1615 1413   1211 100F 0E0D 0C0B   0A09 0807 0605 0403   0201 0D0C 0B0A 0908   0706 0504 0302 0138
  END


=head3 MaximumOfTwoRegisters($result, $first, $second)

Return in the specified register the value in the second register if it is greater than the value in the first register

     Parameter  Description
  1  $result    Result register
  2  $first     First register
  3  $second    Second register

B<Example:>


    Mov rax, 1;
    Mov rdi, 2;

    PrintOutRegisterInHex MaximumOfTwoRegisters r15, rax, rdi;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex MinimumOfTwoRegisters r14, rax, rdi;

    is_deeply Assemble, <<END;
     r15: 0000 0000 0000 0002
     r14: 0000 0000 0000 0001
  END


=head3 MinimumOfTwoRegisters($result, $first, $second)

Return in the specified register the value in the second register if it is less than the value in the first register

     Parameter  Description
  1  $result    Result register
  2  $first     First register
  3  $second    Second register

B<Example:>


    Mov rax, 1;
    Mov rdi, 2;
    PrintOutRegisterInHex MaximumOfTwoRegisters r15, rax, rdi;

    PrintOutRegisterInHex MinimumOfTwoRegisters r14, rax, rdi;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    is_deeply Assemble, <<END;
     r15: 0000 0000 0000 0002
     r14: 0000 0000 0000 0001
  END


=head3 Increment($target, $amount)

Increment the specified register

     Parameter  Description
  1  $target    Target register
  2  $amount    Optional amount if not 1

=head3 Decrement($target, $amount)

Decrement the specified register

     Parameter  Description
  1  $target    Target register
  2  $amount    Optional amount if not 1

=head3 Plus($target, @source)

Add the last operands and place the result in the first operand

     Parameter  Description
  1  $target    Target register
  2  @source    Source registers

B<Example:>


    Copy r15, 2;
    Copy r14, 3;
    KeepFree r15;

    Plus(r15, r15, r14);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex r15;
    Copy r13, 4;
    Minus(r12, r15, r13);
    PrintOutRegisterInHex r12;

    is_deeply Assemble, <<END;
     r15: 0000 0000 0000 0005
     r12: 0000 0000 0000 0001
  END


=head3 Minus($target, $s1, $s2)

Subtract the third operand from the second operand and place the result in the first operand

     Parameter  Description
  1  $target    Target register
  2  $s1        Register to subtract from
  3  $s2        Register to subtract

B<Example:>


    Copy r15, 2;
    Copy r14, 3;
    KeepFree r15;
    Plus(r15, r15, r14);
    PrintOutRegisterInHex r15;
    Copy r13, 4;

    Minus(r12, r15, r13);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex r12;

    is_deeply Assemble, <<END;
     r15: 0000 0000 0000 0005
     r12: 0000 0000 0000 0001
  END


=head2 Zmm

Operations on zmm registers

=head3 InsertIntoXyz($reg, $unit, $pos)

Shift and insert the specified word, double, quad from rax or the contents of xmm0 into the specified xyz register at the specified position shifting data above it to the left towards higher order bytes.

     Parameter  Description
  1  $reg       Register to insert into
  2  $unit      Width of insert
  3  $pos       Position of insert in units from least significant byte starting at 0

B<Example:>


    my $s    = Rb 0..63;
    Vmovdqu8 xmm0,"[$s]";                                                         # Number each byte
    Vmovdqu8 ymm1,"[$s]";
    Vmovdqu8 zmm2,"[$s]";
    Vmovdqu8 zmm3,"[$s]";

    SetRegisterToMinusOne rax;                                                    # Insert some ones

    InsertIntoXyz xmm0, 2, 4;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    InsertIntoXyz ymm1, 4, 5;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    InsertIntoXyz zmm2, 8, 6;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    PrintOutRegisterInHex xmm0;                                                   # Print the insertions
    PrintOutRegisterInHex ymm1;
    PrintOutRegisterInHex zmm2;

    ClearRegisters xmm0;                                                          # Insert some zeroes

    InsertIntoXyz zmm3, 16, 2;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex zmm3;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0D0C 0B0A 0908 FFFF   0706 0504 0302 0100);
    ok $r =~ m(ymm1: 1B1A 1918 1716 1514   FFFF FFFF 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);
    ok $r =~ m(zmm2: 3736 3534 3332 3130   FFFF FFFF FFFF FFFF   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);
    ok $r =~ m(zmm3: 2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   0000 0000 0000 0000   0000 0000 0000 0000   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);


=head3 LoadTargetZmmFromSourceZmm($target, $targetOffset, $source, $sourceOffset, $length)

Load bytes into the numbered target zmm register at a register specified offset with source bytes from a numbered source zmm register at a specified register offset for a specified register length.

     Parameter      Description
  1  $target        Number of zmm register to load
  2  $targetOffset  Register containing start or 0 if from the start
  3  $source        Numbered source zmm register
  4  $sourceOffset  Register containing length
  5  $length        Optional offset from stack top

B<Example:>


    my $s = Rb(17, 1..17);
    LoadShortStringFromMemoryToZmm 0, $s;                                         # Load a sample string
    Keep zmm0;
    PrintOutRegisterInHex xmm0;

    LoadTargetZmmFromSourceZmm 1, Copy(rdi, 3), 0, Copy(rdx, 8), Copy(rsi, 2);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex xmm1;
    KeepFree rdi;


    LoadTargetZmmFromSourceZmm 2, Copy(rdi, 4), 0, rdx, rsi;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex xmm2;

    Copy(zmm3, zmm0);
    PrintOutRegisterInHex xmm3;

    ClearRegisters zmm4;
    Lea rax, "[$s+4]";
    LoadZmmFromMemory 4, rdx, rsi, rax;
    Sub rax, 4;
    PrintOutRegisterInHex xmm4;

    is_deeply Assemble, <<END;
    xmm0: 0F0E 0D0C 0B0A 0908   0706 0504 0302 0111
    xmm1: 0000 0000 0000 0000   0000 0009 0800 0000
    xmm2: 0000 0000 0000 0000   0000 0908 0000 0000
    xmm3: 0F0E 0D0C 0B0A 0908   0706 0504 0302 0111
    xmm4: 0000 0000 0000 0504   0000 0000 0000 0000
  END

    my $s = Rb(13, 1..13);
    my $t = Rb(1..64);
    my $source = rax;                                                             # Address to load from
    my $start  = rsi;                                                             # Start position in the zmm register
    my $length = rdi;                                                             # Length of copy

    Copy $source, $s;
    LoadShortStringFromMemoryToZmm 0, $s;                                         # Load a sample string
    KeepFree $source;
    PrintOutRegisterInHex xmm0;

    LoadZmmFromMemory 0, Increment(GetLengthOfShortString($start, 0)), Copy($length, 1), Copy($source, $t);
    PrintOutRegisterInHex xmm0;

    LoadZmmFromMemory 0, $start, $length, $source;
    PrintOutRegisterInHex xmm0;

    KeepFree $length;
    LoadZmmFromMemory 0, $start, Minus($length, Copy(r13, 56), $start), $source;
    SetLengthOfShortString 0, sil;                                                # Set current length of zmm0
    PrintOutRegisterInHex xmm0, zmm0;

    is_deeply Assemble, <<END;
    xmm0: 0000 0D0C 0B0A 0908   0706 0504 0302 010D
    xmm0: 0001 0D0C 0B0A 0908   0706 0504 0302 010D
    xmm0: 0201 0D0C 0B0A 0908   0706 0504 0302 010D
    xmm0: 0201 0D0C 0B0A 0908   0706 0504 0302 0138
    zmm0: 0000 0000 0000 0000   2A29 2827 2625 2423   2221 201F 1E1D 1C1B   1A19 1817 1615 1413   1211 100F 0E0D 0C0B   0A09 0807 0605 0403   0201 0D0C 0B0A 0908   0706 0504 0302 0138
  END


=head3 LoadZmmFromMemory($target, $targetOffset, $length, $source)

Load bytes into the numbered target zmm register at a register specified offset with source bytes from memory addressed by a specified register for a specified register length from memory addressed by a specified register.

     Parameter      Description
  1  $target        Number of zmm register to load
  2  $targetOffset  Register containing start or 0 if from the start
  3  $length        Register containing length
  4  $source        Register addressing memory to load from

=head1 Structured Programming

Structured programming constructs

=head2 If($jump, $then, $else)

If

     Parameter  Description
  1  $jump      Jump op code of variable
  2  $then      Then - required
  3  $else      Else - optional

B<Example:>


    Mov rax, 0;
    Test rax,rax;
    IfNz
     {PrintOutRegisterInHex rax;
     } sub
     {PrintOutRegisterInHex rbx;
     };
    KeepFree rax;
    Mov rax, 1;
    Test rax,rax;
    IfNz
     {PrintOutRegisterInHex rcx;
     } sub
     {PrintOutRegisterInHex rdx;
     };

    ok Assemble =~ m(rbx.*rcx)s;


=head2 IfEq($then, $else)

If equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 IfNe($then, $else)

If not equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 IfNz($then, $else)

If not zero execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 IfLt($then, $else)

If less than execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 IfLe($then, $else)

If less than or equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 IfGt($then, $else)

If greater than execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 IfGe($then, $else)

If greater than or equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 For($body, $register, $limit, $increment)

For - iterate the body as long as register is less than limit incrementing by increment each time

     Parameter   Description
  1  $body       Body
  2  $register   Register
  3  $limit      Limit on loop
  4  $increment  Increment on each iteration

B<Example:>



    For  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {PrintOutRegisterInHex rax
     } rax, 16, 1;

    my $r = Assemble;
    ok $r =~ m(( 0000){3} 0000)i;
    ok $r =~ m(( 0000){3} 000F)i;


=head2 ForIn($full, $last, $register, $limit, $increment)

For - iterate the full body as long as register plus increment is less than than limit incrementing by increment each time then increment the last body for the last non full block.

     Parameter   Description
  1  $full       Body for full block
  2  $last       Body for last block
  3  $register   Register
  4  $limit      Limit on loop
  5  $increment  Increment on each iteration

=head2 ForEver($body)

Iterate for ever

     Parameter  Description
  1  $body      Body to iterate

=head2 Macro($body, %options)

Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub

     Parameter  Description
  1  $body      Body
  2  %options   Options.

=head2 Subroutine($body, %options)

Create a subroutine that can be called in assembler code

     Parameter  Description
  1  $body      Body
  2  %options   Options.

=head2 Nasm::X86::Sub::call($sub, @parameters)

Call a sub passing it some parameters

     Parameter    Description
  1  $sub         Subroutine descriptor
  2  @parameters  Parameter variables

=head2 cr($body, @registers)

Call a subroutine with a reordering of the registers.

     Parameter   Description
  1  $body       Code to execute with reordered registers
  2  @registers  Registers to reorder

=head2 cxr($body, @registers)

Call a subroutine with a reordering of the xmm registers.

     Parameter   Description
  1  $body       Code to execute with reordered registers
  2  @registers  Registers to reorder

B<Example:>


    my $t = GenTree(2,2);                                                         # Tree description
    $t->node->();                                                                 # Root
    Movdqa xmm1, xmm0;                                                            # Root is in xmm1

    if (1)                                                                        # New left node
     {$t->node->();                                                               # Node in xmm0
      Movdqa xmm2, xmm0;                                                          # Left is in xmm2


      cxr {$t->insertLeft->()} 1,2;                                               # Insert left under root  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


      cxr {$t->dump->("Left")} 2;                                                 # Left node after insertion  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     }

    if (1)                                                                        # New right node in xmm0
     {$t->node->();
      Movdqa xmm3, xmm0;                                                          # Right is in xmm3


      cxr {$t->insertRight->()} 1,3;                                              # Insert left under root  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


      cxr {$t->dump->("Right")} 3;                                                # Right node after insertion  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     }


    cxr  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {$t->dump->("Root");                                                         # Root node after insertions
      $t->isRoot->();
      IfNz {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushRR xmm0;                                                                  # Dump underlying  byte string
    PopRR rdi, rax;
    $t->byteString->dump;

    Exit;                                                                         # Return to operating system

    is_deeply Assemble, <<END;                                                    # Test tree so produced
  Left
  ArenaTreeNode at: 0000 0000 0000 00B0
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Right
  ArenaTreeNode at: 0000 0000 0000 0150
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Root
  ArenaTreeNode at: 0000 0000 0000 0010
     up: 0000 0000 0000 0000
   left: 0000 0000 0000 00B0
  right: 0000 0000 0000 0150
  root
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 01E0
  END


=head2 Comment(@comment)

Insert a comment into the assembly code

     Parameter  Description
  1  @comment   Text of comment

B<Example:>



    Comment "Print a string from memory";  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $s = "Hello World";
    Mov rax, Rs($s);
    Mov rdi, length $s;
    PrintOutMemory;

    ok Assemble =~ m(Hello World);


=head2 DComment(@comment)

Insert a comment into the data segment

     Parameter  Description
  1  @comment   Text of comment

=head2 RComment(@comment)

Insert a comment into the read only data segment

     Parameter  Description
  1  @comment   Text of comment

=head1 Print

Print

=head2 PrintNL($channel)

Print a new line to stdout  or stderr

     Parameter  Description
  1  $channel   Channel to write on

=head2 PrintErrNL()

Print a new line to stderr


=head2 PrintOutNL()

Print a new line to stderr


B<Example:>


    my $q = Rs('abababab');
    Mov(rax, "[$q]");
    PrintOutString "rax: ";
    PrintOutRaxInHex;

    PrintOutNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Xor rax, rax;
    PrintOutString "rax: ";
    PrintOutRaxInHex;

    PrintOutNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(rax: 6261 6261 6261 6261.*rax: 0000 0000 0000 0000)s;


=head2 PrintString($channel, @string)

Print a constant string to the specified channel

     Parameter  Description
  1  $channel   Channel
  2  @string    Strings

=head2 PrintErrString(@string)

Print a constant string to stderr.

     Parameter  Description
  1  @string    String

=head2 PrintOutString(@string)

Print a constant string to stdout.

     Parameter  Description
  1  @string    String

=head2 PrintErrStringNL(@string)

Print a constant string followed by a new line to stderr

     Parameter  Description
  1  @string    Strings

B<Example:>


    PrintOutStringNL "Hello World";
    PrintOutStringNL "Hello
World";

    PrintErrStringNL "Hello World";  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble(debug => 0, eq => <<END);
  Hello World
  Hello
  World
  END


=head2 PrintOutStringNL(@string)

Print a constant string followed by a new line to stdout

     Parameter  Description
  1  @string    Strings

B<Example:>



    PrintOutStringNL "Hello World";  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    PrintOutStringNL "Hello
World";  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintErrStringNL "Hello World";

    ok Assemble(debug => 0, eq => <<END);
  Hello World
  Hello
  World
  END

    my $t = GenTree(2,2);                                                         # Tree description
    $t->node->();                                                                 # Root
    Movdqa xmm1, xmm0;                                                            # Root is in xmm1

    if (1)                                                                        # New left node
     {$t->node->();                                                               # Node in xmm0
      Movdqa xmm2, xmm0;                                                          # Left is in xmm2

      cxr {$t->insertLeft->()} 1,2;                                               # Insert left under root
      cxr {$t->dump->("Left")} 2;                                                 # Left node after insertion
     }

    if (1)                                                                        # New right node in xmm0
     {$t->node->();
      Movdqa xmm3, xmm0;                                                          # Right is in xmm3

      cxr {$t->insertRight->()} 1,3;                                              # Insert left under root
      cxr {$t->dump->("Right")} 3;                                                # Right node after insertion
     }

    cxr
     {$t->dump->("Root");                                                         # Root node after insertions
      $t->isRoot->();

      IfNz {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     } 1;

    PushRR xmm0;                                                                  # Dump underlying  byte string
    PopRR rdi, rax;
    $t->byteString->dump;

    Exit;                                                                         # Return to operating system

    is_deeply Assemble, <<END;                                                    # Test tree so produced
  Left
  ArenaTreeNode at: 0000 0000 0000 00B0
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Right
  ArenaTreeNode at: 0000 0000 0000 0150
     up: 0000 0000 0000 0010
   left: 0000 0000 0000 0000
  right: 0000 0000 0000 0000
  Root
  ArenaTreeNode at: 0000 0000 0000 0010
     up: 0000 0000 0000 0000
   left: 0000 0000 0000 00B0
  right: 0000 0000 0000 0150
  root
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 01E0
  END


=head2 PrintRaxInHex($channel)

Write the content of register rax in hexadecimal in big endian notation to the specified channel

     Parameter  Description
  1  $channel   Channel

=head2 PrintErrRaxInHex()

Write the content of register rax in hexadecimal in big endian notation to stderr


=head2 PrintOutRaxInHex()

Write the content of register rax in hexadecimal in big endian notation to stderr


B<Example:>


    my $q = Rs('abababab');
    Mov(rax, "[$q]");
    PrintOutString "rax: ";

    PrintOutRaxInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;
    Xor rax, rax;
    PrintOutString "rax: ";

    PrintOutRaxInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;

    ok Assemble =~ m(rax: 6261 6261 6261 6261.*rax: 0000 0000 0000 0000)s;


=head2 PrintOutRaxInReverseInHex()

Write the content of register rax to stderr in hexadecimal in little endian notation


B<Example:>


    Mov rax, 0x07654321;
    Shl rax, 32;
    Or  rax, 0x07654321;
    PushR rax;

    PrintOutRaxInHex;
    PrintOutNL;

    PrintOutRaxInReverseInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;
    KeepFree rax;

    Mov rax, rsp;
    Mov rdi, 8;
    PrintOutMemoryInHex;
    PrintOutNL;
    PopR rax;
    KeepFree rax, rdi;

    Mov rax, 4096;
    PushR rax;
    Mov rax, rsp;
    Mov rdi, 8;
    PrintOutMemoryInHex;
    PrintOutNL;
    PopR rax;

    is_deeply Assemble, <<END;
  0765 4321 0765 4321
  2143 6507 2143 6507
  2143 6507 2143 6507
  0010 0000 0000 0000
  END


=head2 PrintRegisterInHex($channel, @r)

Print the named registers as hex strings

     Parameter  Description
  1  $channel   Channel to print on
  2  @r         Names of the registers to print

=head2 PrintErrRegisterInHex(@r)

Print the named registers as hex strings on stderr

     Parameter  Description
  1  @r         Names of the registers to print

=head2 PrintOutRegisterInHex(@r)

Print the named registers as hex strings on stdout

     Parameter  Description
  1  @r         Names of the registers to print

B<Example:>


    my $q = Rs(('a'..'p')x4);
    Mov r8,"[$q]";

    PrintOutRegisterInHex r8;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(r8: 6867 6665 6463 6261)s;


=head2 PrintOutRegistersInHex()

Print the general purpose registers in hex


B<Example:>


    my $q = Rs('abababab');
    Mov(rax, 1);
    Mov(rbx, 2);
    Mov(rcx, 3);
    Mov(rdx, 4);
    Mov(r8,  5);
    Lea r9,  "[rax+rbx]";

    PrintOutRegistersInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $r = Assemble;
    ok $r =~ m( r8: 0000 0000 0000 0005.* r9: 0000 0000 0000 0003.*rax: 0000 0000 0000 0001)s;
    ok $r =~ m(rbx: 0000 0000 0000 0002.*rcx: 0000 0000 0000 0003.*rdx: 0000 0000 0000 0004)s;


=head2 PrintOutZF()

Print the zero flag without disturbing it


B<Example:>


    SetZF;

    PrintOutZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    ClearZF;

    PrintOutZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    SetZF;

    PrintOutZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    SetZF;

    PrintOutZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    ClearZF;

    PrintOutZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(ZF=1.*ZF=0.*ZF=1.*ZF=1.*ZF=0)s;


=head1 Variables

Variable definitions and operations

=head2 Scopes

Each variable is contained in a scope in an effort to detect references to out of scope variables

=head3 Scope($name)

Create and stack a new scope and continue with it as the current scope

     Parameter  Description
  1  $name      Scope name

B<Example:>


  if (1)

   {my $start = Scope(start);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $s1    = Scope(s1);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $s2    = Scope(s2);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    is_deeply $s2->depth, 2;
    is_deeply $s2->name,  q(s2);
    ScopeEnd;


    my $t1    = Scope(t1);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $t2    = Scope(t2);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    is_deeply $t1->depth, 2;
    is_deeply $t1->name,  q(t1);
    is_deeply $t2->depth, 3;
    is_deeply $t2->name,  q(t2);

    ok  $s1->currentlyVisible;
    ok !$s2->currentlyVisible;

    ok  $s1->contains($t2);
    ok !$s2->contains($t2);

    ScopeEnd;

    is_deeply $s1->depth, 1;
    is_deeply $s1->name,  q(s1);
    ScopeEnd;
   }


=head3 ScopeEnd()

End the current scope and continue with the containing parent scope


B<Example:>


  if (1)
   {my $start = Scope(start);
    my $s1    = Scope(s1);
    my $s2    = Scope(s2);
    is_deeply $s2->depth, 2;
    is_deeply $s2->name,  q(s2);

    ScopeEnd;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $t1    = Scope(t1);
    my $t2    = Scope(t2);
    is_deeply $t1->depth, 2;
    is_deeply $t1->name,  q(t1);
    is_deeply $t2->depth, 3;
    is_deeply $t2->name,  q(t2);

    ok  $s1->currentlyVisible;
    ok !$s2->currentlyVisible;

    ok  $s1->contains($t2);
    ok !$s2->contains($t2);


    ScopeEnd;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    is_deeply $s1->depth, 1;
    is_deeply $s1->name,  q(s1);

    ScopeEnd;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

   }


=head3 Nasm::X86::Scope::contains($parent, $child)

Check that the named parent scope contains the specified child scope. If no child scope is supplied we use the current scope to check that the parent scope is currently visible

     Parameter  Description
  1  $parent    Parent scope
  2  $child     Child scope

=head3 Nasm::X86::Scope::currentlyVisible($scope)

Check that the named parent scope is currently visible

     Parameter  Description
  1  $scope     Scope to check for visibility

=head2 Definitions

Variable definitions

=head3 Variable($size, $name, $expr)

Create a new variable with the specified size and name initialized via an expression

     Parameter  Description
  1  $size      Size as a power of 2
  2  $name      Name of variable
  3  $expr      Optional expression initializing variable

=head3 Vb($name, $expr)

Define a byte variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression

=head3 Vw($name, $expr)

Define a word variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression

=head3 Vd($name, $expr)

Define a double word variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression

=head3 Vq($name, $expr)

Define a quad variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression

B<Example:>



    my $a = Vq(a, 3);   $a->print;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $c = $a +  2;    $c->print;
    my $d = $c -  $a;   $d->print;
    my $e = $d == 2;    $e->print;
    my $f = $d != 2;    $f->print;
    my $g = $a *  2;    $g->print;
    my $h = $g /  2;    $h->print;
    my $i = $a %  2;    $i->print;

    If ($a == 3, sub{PrintOutStringNL "a == 3"});

    is_deeply Assemble, <<END;
  0300 0000 0000 0000
  0500 0000 0000 0000
  0200 0000 0000 0000
  0100 0000 0000 0000
  0000 0000 0000 0000
  0600 0000 0000 0000
  0300 0000 0000 0000
  0100 0000 0000 0000
  a == 3
  END


=head3 VxyzInit($var, @expr)

Initialize an xyz register from general purpose registers

     Parameter  Description
  1  $var       Variable
  2  @expr      Initializing general purpose registers or undef

=head3 Vx($name, @expr)

Define an xmm variable

     Parameter  Description
  1  $name      Name of variable
  2  @expr      Initializing expression

=head3 Vy($name, @expr)

Define an ymm variable

     Parameter  Description
  1  $name      Name of variable
  2  @expr      Initializing expression

=head3 Vz($name, @expr)

Define an zmm variable

     Parameter  Description
  1  $name      Name of variable
  2  @expr      Initializing expression

=head3 Vr($name, $size)

Define a reference variable

     Parameter  Description
  1  $name      Name of variable
  2  $size      Variable being referenced

=head2 Operations

Variable operations

=head3 Nasm::X86::Variable::address($left, $offset)

Get the address of a variable with an optional offset

     Parameter  Description
  1  $left      Left variable
  2  $offset    Optional offset

=head3 Nasm::X86::Variable::copy($left, $right)

Copy one variable into another

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::copyRef($left, $right)

Copy one variable into an referenced variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::copyAddress($left, $right)

Copy a reference to a variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::equals($op, $left, $right)

Equals operator

     Parameter  Description
  1  $op        Operator
  2  $left      Left variable
  3  $right     Right variable

=head3 Nasm::X86::Variable::assign($left, $op, $right)

Assign to the left hand side the value of the right hand side

     Parameter  Description
  1  $left      Left variable
  2  $op        Operator
  3  $right     Right variable

=head3 Nasm::X86::Variable::plusAssign($left, $right)

Implement plus and assign

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::minusAssign($left, $right)

Implement minus and assign

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::arithmetic($op, $name, $left, $right)

Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables

     Parameter  Description
  1  $op        Operator
  2  $name      Operator name
  3  $left      Left variable
  4  $right     Right variable

=head3 Nasm::X86::Variable::add($left, $right)

Add the right hand variable to the left hand variable and return the result as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

B<Example:>


    my $a = Vq(a, 3);   $a->print;
    my $c = $a +  2;    $c->print;
    my $d = $c -  $a;   $d->print;
    my $e = $d == 2;    $e->print;
    my $f = $d != 2;    $f->print;
    my $g = $a *  2;    $g->print;
    my $h = $g /  2;    $h->print;
    my $i = $a %  2;    $i->print;

    If ($a == 3, sub{PrintOutStringNL "a == 3"});

    is_deeply Assemble, <<END;
  0300 0000 0000 0000
  0500 0000 0000 0000
  0200 0000 0000 0000
  0100 0000 0000 0000
  0000 0000 0000 0000
  0600 0000 0000 0000
  0300 0000 0000 0000
  0100 0000 0000 0000
  a == 3
  END


=head3 Nasm::X86::Variable::sub($left, $right)

Subtract the right hand variable from the left hand variable and return the result as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::times($left, $right)

Multiply the left hand variable by the right hand variable and return the result as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::division($op, $left, $right)

Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side

     Parameter  Description
  1  $op        Operator
  2  $left      Left variable
  3  $right     Right variable

=head3 Nasm::X86::Variable::divide($left, $right)

Divide the left hand variable by the right hand variable and return the result as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::mod($left, $right)

Divide the left hand variable by the right hand variable and return the remainder as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::boolean($sub, $op, $left, $right)

Combine the left hand variable with the right hand variable via a boolean operator

     Parameter  Description
  1  $sub       Operator
  2  $op        Operator name
  3  $left      Left variable
  4  $right     Right variable

=head3 Nasm::X86::Variable::eq($left, $right)

Check whether the left hand variable is equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::ne($left, $right)

Check whether the left hand variable is not equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::ge($left, $right)

Check whether the left hand variable is greater than or equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::gt($left, $right)

Check whether the left hand variable is greater than the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::le($left, $right)

Check whether the left hand variable is less than or equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::lt($left, $right)

Check whether the left hand variable is less than the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::print($left)

Write the value of a variable on stdout

     Parameter  Description
  1  $left      Left variable

B<Example:>


    my $a = Vq(a, 3);   $a->print;
    my $c = $a +  2;    $c->print;
    my $d = $c -  $a;   $d->print;
    my $e = $d == 2;    $e->print;
    my $f = $d != 2;    $f->print;
    my $g = $a *  2;    $g->print;
    my $h = $g /  2;    $h->print;
    my $i = $a %  2;    $i->print;

    If ($a == 3, sub{PrintOutStringNL "a == 3"});

    is_deeply Assemble, <<END;
  0300 0000 0000 0000
  0500 0000 0000 0000
  0200 0000 0000 0000
  0100 0000 0000 0000
  0000 0000 0000 0000
  0600 0000 0000 0000
  0300 0000 0000 0000
  0100 0000 0000 0000
  a == 3
  END

    my $a = Vq(a, 3); $a->outNL;
    my $b = Vq(b, 2); $b->outNL;
    my $c = $a +  $b; $c->outNL;
    my $d = $c -  $a; $d->outNL;
    my $e = $d == $b; $e->outNL;
    my $f = $d != $b; $f->outNL;
    my $g = $a *  $b; $g->outNL;
    my $h = $g /  $b; $h->outNL;
    my $i = $a %  $b; $i->outNL;
    is_deeply Assemble, <<END;
  a: 0000 0000 0000 0003
  b: 0000 0000 0000 0002
  (a add b): 0000 0000 0000 0005
  ((a add b) sub a): 0000 0000 0000 0002
  (((a add b) sub a) eq b): 0000 0000 0000 0001
  (((a add b) sub a) ne b): 0000 0000 0000 0000
  (a times b): 0000 0000 0000 0006
  ((a times b) / b): 0000 0000 0000 0003
  (a % b): 0000 0000 0000 0001
  END


=head3 Nasm::X86::Variable::dump($left, $channel, $newLine, $title1, $title2)

Dump the value of a variable to the specified channel adding an optional title and new line if requested

     Parameter  Description
  1  $left      Left variable
  2  $channel   Channel
  3  $newLine   New line required
  4  $title1    Optional leading title
  5  $title2    Optional trailing title

B<Example:>


    my $a = Vq(a, 3); $a->outNL;
    my $b = Vq(b, 2); $b->outNL;
    my $c = $a +  $b; $c->outNL;
    my $d = $c -  $a; $d->outNL;
    my $e = $d == $b; $e->outNL;
    my $f = $d != $b; $f->outNL;
    my $g = $a *  $b; $g->outNL;
    my $h = $g /  $b; $h->outNL;
    my $i = $a %  $b; $i->outNL;
    is_deeply Assemble, <<END;
  a: 0000 0000 0000 0003
  b: 0000 0000 0000 0002
  (a add b): 0000 0000 0000 0005
  ((a add b) sub a): 0000 0000 0000 0002
  (((a add b) sub a) eq b): 0000 0000 0000 0001
  (((a add b) sub a) ne b): 0000 0000 0000 0000
  (a times b): 0000 0000 0000 0006
  ((a times b) / b): 0000 0000 0000 0003
  (a % b): 0000 0000 0000 0001
  END


=head3 Nasm::X86::Variable::err($left, $title1, $title2)

Dump the value of a variable on stderr

     Parameter  Description
  1  $left      Left variable
  2  $title1    Optional leading title
  3  $title2    Optional trailing title

=head3 Nasm::X86::Variable::out($left, $title1, $title2)

Dump the value of a variable on stdout

     Parameter  Description
  1  $left      Left variable
  2  $title1    Optional leading title
  3  $title2    Optional trailing title

=head3 Nasm::X86::Variable::errNL($left, $title1, $title2)

Dump the value of a variable on stderr and append a new line

     Parameter  Description
  1  $left      Left variable
  2  $title1    Optional leading title
  3  $title2    Optional trailing title

=head3 Nasm::X86::Variable::outNL($left, $title1, $title2)

Dump the value of a variable on stdout and append a new line

     Parameter  Description
  1  $left      Left variable
  2  $title1    Optional leading title
  3  $title2    Optional trailing title

=head3 Nasm::X86::Variable::debug($left)

Dump the value of a variable on stdout with an indication of where the dump came from

     Parameter  Description
  1  $left      Left variable

=head3 Nasm::X86::Variable::isRef($variable)

Check whether the specified  variable is a reference to another variable

     Parameter  Description
  1  $variable  Variable

=head3 Nasm::X86::Variable::setReg($variable, $register, @registers)

Set the named registers from the content of the variable

     Parameter   Description
  1  $variable   Variable
  2  $register   Register to load
  3  @registers  Optional further registers to load

=head3 Nasm::X86::Variable::getReg($variable, $register, @registers)

Load the variable from the named registers

     Parameter   Description
  1  $variable   Variable
  2  $register   Register to load
  3  @registers  Optional further registers to load from

=head3 Nasm::X86::Variable::incDec($left, $op)

Increment or decrement a variable

     Parameter  Description
  1  $left      Left variable operator
  2  $op        Address of operator to perform inc or dec

=head3 Nasm::X86::Variable::inc($left)

Increment a variable

     Parameter  Description
  1  $left      Variable

=head3 Nasm::X86::Variable::dec($left)

Decrement a variable

     Parameter  Description
  1  $left      Variable

=head3 Nasm::X86::Variable::str($left)

The name of the variable

     Parameter  Description
  1  $left      Variable

=head3 Nasm::X86::Variable::min($left, $right)

Minimum of two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

B<Example:>


    my $a = Vq("a", 1);
    my $b = Vq("b", 2);
    my $c = $a->min($b);
    my $d = $a->max($b);
    $a->outNL;
    $b->outNL;
    $c->outNL;
    $d->outNL;

    is_deeply Assemble,<<END;
  a: 0000 0000 0000 0001
  b: 0000 0000 0000 0002
  Minimum(a, b): 0000 0000 0000 0001
  Maximum(a, b): 0000 0000 0000 0002
  END


=head3 Nasm::X86::Variable::max($left, $right)

Maximum of two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

B<Example:>


    my $a = Vq("a", 1);
    my $b = Vq("b", 2);
    my $c = $a->min($b);
    my $d = $a->max($b);
    $a->outNL;
    $b->outNL;
    $c->outNL;
    $d->outNL;

    is_deeply Assemble,<<END;
  a: 0000 0000 0000 0001
  b: 0000 0000 0000 0002
  Minimum(a, b): 0000 0000 0000 0001
  Maximum(a, b): 0000 0000 0000 0002
  END


=head3 Nasm::X86::Variable::and($left, $right)

And two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::or($left, $right)

Or two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Nasm::X86::Variable::setMask($start, $length, $mask)

Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

     Parameter  Description
  1  $start     Variable containing start of mask
  2  $length    Variable containing length of mask
  3  $mask      Mask register

B<Example:>


    my $start  = Vq("Start",  7);
    my $length = Vq("Length", 3);
    $start->setMask($length, k7);
    PrintOutRegisterInHex k7;

    is_deeply Assemble, <<END;
      k7: 0000 0000 0000 0380
  END

    my $z = Vq('zero', 0);
    my $o = Vq('one',  1);
    my $t = Vq('two',  2);
    $z->setMask($o,       k7); PrintOutRegisterInHex k7;
    $z->setMask($t,       k6); PrintOutRegisterInHex k6;
    $z->setMask($o+$t,    k5); PrintOutRegisterInHex k5;
    $o->setMask($o,       k4); PrintOutRegisterInHex k4;
    $o->setMask($t,       k3); PrintOutRegisterInHex k3;
    $o->setMask($o+$t,    k2); PrintOutRegisterInHex k2;

    $t->setMask($o,       k1); PrintOutRegisterInHex k1;
    $t->setMask($t,       k0); PrintOutRegisterInHex k0;


    ok Assemble(debug => 0, eq => <<END);
      k7: 0000 0000 0000 0001
      k6: 0000 0000 0000 0003
      k5: 0000 0000 0000 0007
      k4: 0000 0000 0000 0002
      k3: 0000 0000 0000 0006
      k2: 0000 0000 0000 000E
      k1: 0000 0000 0000 0004
      k0: 0000 0000 0000 000C
  END


=head3 Nasm::X86::Variable::setZmm($source, $zmm, $offset, $length)

Load bytes from the memory addressed by specified source variable into the numbered zmm register at the offset in the specified offset moving the number of bytes in the specified variable

     Parameter  Description
  1  $source    Variable containing the address of the source
  2  $zmm       Number of zmm to load
  3  $offset    Variable containing offset in zmm to move to
  4  $length    Variable containing length of move

B<Example:>


    my $s = Rb(0..128);
    my $source = Vq(Source, $s);

    if (1)                                                                        # First block
     {my $offset = Vq(Offset, 7);
      my $length = Vq(Length, 3);
      $source->setZmm(0, $offset, $length);
     }

    if (1)                                                                        # Second block
     {my $offset = Vq(Offset, 33);
      my $length = Vq(Length, 12);
      $source->setZmm(0, $offset, $length);
     }

    PrintOutRegisterInHex zmm0;

    is_deeply Assemble, <<END;
    zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 000B 0A09 0807   0605 0403 0201 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0201   0000 0000 0000 0000
  END

    my $a = Vz a, Rb((map {"0x${_}0"} 0..9, 'a'..'f')x4);
    my $b = Vz b, Rb((map {"0x0${_}"} 0..9, 'a'..'f')x4);

     $a      ->loadZmm(0);                                                        # Show variable in zmm0
     $b      ->loadZmm(1);                                                        # Show variable in zmm1

    ($a + $b)->loadZmm(2);                                                        # Add bytes      and show in zmm2
    ($a - $b)->loadZmm(3);                                                        # Subtract bytes and show in zmm3

    PrintOutRegisterInHex "zmm$_" for 0..3;

    is_deeply Assemble, <<END;
    zmm0: F0E0 D0C0 B0A0 9080   7060 5040 3020 1000   F0E0 D0C0 B0A0 9080   7060 5040 3020 1000   F0E0 D0C0 B0A0 9080   7060 5040 3020 1000   F0E0 D0C0 B0A0 9080   7060 5040 3020 1000
    zmm1: 0F0E 0D0C 0B0A 0908   0706 0504 0302 0100   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
    zmm2: FFEE DDCC BBAA 9988   7766 5544 3322 1100   FFEE DDCC BBAA 9988   7766 5544 3322 1100   FFEE DDCC BBAA 9988   7766 5544 3322 1100   FFEE DDCC BBAA 9988   7766 5544 3322 1100
    zmm3: E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00   E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00   E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00   E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00
  END


=head3 Nasm::X86::Variable::loadZmm($source, $zmm)

Load bytes from the memory addressed by the specified source variable into the numbered zmm register.

     Parameter  Description
  1  $source    Variable containing the address of the source
  2  $zmm       Number of zmm to get

=head3 Nasm::X86::Variable::saveZmm($target, $zmm)

Save bytes into the memory addressed by the target variable from the numbered zmm register.

     Parameter  Description
  1  $target    Variable containing the address of the source
  2  $zmm       Number of zmm to put

=head3 getBwdqFromMmAsVariable($size, $mm, $offset)

Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $size      Size of get
  2  $mm        Register
  3  $offset    Offset in bytes

=head3 getBFromXmmAsVariable($xmm, $offset)

Get the byte from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getWFromXmmAsVariable($xmm, $offset)

Get the word from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getDFromXmmAsVariable($xmm, $offset)

Get the double word from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getQFromXmmAsVariable($xmm, $offset)

Get the quad word from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getBFromZmmAsVariable($zmm, $offset)

Get the byte from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $zmm       Numbered zmm
  2  $offset    Offset in bytes

=head3 getWFromZmmAsVariable($zmm, $offset)

Get the word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $zmm       Numbered zmm
  2  $offset    Offset in bytes

=head3 getDFromZmmAsVariable($zmm, $offset)

Get the double word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $zmm       Numbered zmm
  2  $offset    Offset in bytes

B<Example:>


    my $s = Rb(0..8);
    my $c = Vq("Content",   "[$s]");
       $c->putBIntoZmm(0,  4);
       $c->putWIntoZmm(0,  6);
       $c->putDIntoZmm(0, 10);
       $c->putQIntoZmm(0, 16);
    PrintOutRegisterInHex zmm0;
    getBFromZmmAsVariable(0, 12)->outNL;
    getWFromZmmAsVariable(0, 12)->outNL;

    getDFromZmmAsVariable(0, 12)->outNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    getQFromZmmAsVariable(0, 12)->outNL;

    is_deeply Assemble, <<END;
    zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0706 0504 0302 0100   0000 0302 0100 0000   0100 0000 0000 0000
  b at offset 12 in zmm0: 0000 0000 0000 0002
  w at offset 12 in zmm0: 0000 0000 0000 0302
  d at offset 12 in zmm0: 0000 0000 0000 0302
  q at offset 12 in zmm0: 0302 0100 0000 0302
  END


=head3 getQFromZmmAsVariable($zmm, $offset)

Get the quad word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $zmm       Numbered zmm
  2  $offset    Offset in bytes

=head3 Nasm::X86::Variable::getBFromZmm($variable, $zmm, $offset)

Get the byte from the numbered zmm register and put it in a variable

     Parameter  Description
  1  $variable  Variable
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::getWFromZmm($variable, $zmm, $offset)

Get the word from the numbered zmm register and put it in a variable

     Parameter  Description
  1  $variable  Variable
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::getDFromZmm($variable, $zmm, $offset)

Get the double word from the numbered zmm register and put it in a variable

     Parameter  Description
  1  $variable  Variable
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::getQFromZmm($variable, $zmm, $offset)

Get the quad word from the numbered zmm register and put it in a variable

     Parameter  Description
  1  $variable  Variable
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putBwdqIntoMm($content, $size, $mm, $offset)

Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register

     Parameter  Description
  1  $content   Variable with content
  2  $size      Size of put
  3  $mm        Numbered zmm
  4  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putBIntoXmm($content, $xmm, $offset)

Place the value of the content variable at the byte in the numbered xmm register

     Parameter  Description
  1  $content   Variable with content
  2  $xmm       Numbered xmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putWIntoXmm($content, $xmm, $offset)

Place the value of the content variable at the word in the numbered xmm register

     Parameter  Description
  1  $content   Variable with content
  2  $xmm       Numbered xmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putDIntoXmm($content, $xmm, $offset)

Place the value of the content variable at the double word in the numbered xmm register

     Parameter  Description
  1  $content   Variable with content
  2  $xmm       Numbered xmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putQIntoXmm($content, $xmm, $offset)

Place the value of the content variable at the quad word in the numbered xmm register

     Parameter  Description
  1  $content   Variable with content
  2  $xmm       Numbered xmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putBIntoZmm($content, $zmm, $offset)

Place the value of the content variable at the byte in the numbered zmm register

     Parameter  Description
  1  $content   Variable with content
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putWIntoZmm($content, $zmm, $offset)

Place the value of the content variable at the word in the numbered zmm register

     Parameter  Description
  1  $content   Variable with content
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::putDIntoZmm($content, $zmm, $offset)

Place the value of the content variable at the double word in the numbered zmm register

     Parameter  Description
  1  $content   Variable with content
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

B<Example:>


    my $s = Rb(0..8);
    my $c = Vq("Content",   "[$s]");
       $c->putBIntoZmm(0,  4);
       $c->putWIntoZmm(0,  6);
       $c->putDIntoZmm(0, 10);
       $c->putQIntoZmm(0, 16);
    PrintOutRegisterInHex zmm0;
    getBFromZmmAsVariable(0, 12)->outNL;
    getWFromZmmAsVariable(0, 12)->outNL;
    getDFromZmmAsVariable(0, 12)->outNL;
    getQFromZmmAsVariable(0, 12)->outNL;

    is_deeply Assemble, <<END;
    zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0706 0504 0302 0100   0000 0302 0100 0000   0100 0000 0000 0000
  b at offset 12 in zmm0: 0000 0000 0000 0002
  w at offset 12 in zmm0: 0000 0000 0000 0302
  d at offset 12 in zmm0: 0000 0000 0000 0302
  q at offset 12 in zmm0: 0302 0100 0000 0302
  END


=head3 Nasm::X86::Variable::putQIntoZmm($content, $zmm, $offset)

Place the value of the content variable at the quad word in the numbered zmm register

     Parameter  Description
  1  $content   Variable with content
  2  $zmm       Numbered zmm
  3  $offset    Offset in bytes

=head3 Nasm::X86::Variable::clearMemory($memory)

Clear the memory described in this variable

     Parameter  Description
  1  $memory    Variable describing memory as returned by Allocate Memory

=head3 Nasm::X86::Variable::copyMemoryFrom($target, $source)

Copy from one block of memory to another

     Parameter  Description
  1  $target    Variable describing the target
  2  $source    Variable describing the source

=head3 Nasm::X86::Variable::printOutMemoryInHex($memory)

Print allocated memory in hex

     Parameter  Description
  1  $memory    Variable describing the memory

=head3 Nasm::X86::Variable::freeMemory($memory)

Free the memory described in this variable

     Parameter  Description
  1  $memory    Variable describing memory as returned by Allocate Memory

B<Example:>


    my $N = Vq(size, 2048);
    my $q = Rs('a'..'p');
    AllocateMemory($N, my $address = Vq(address));

    Vmovdqu8 xmm0, "[$q]";
    $address->setReg(rax);
    Vmovdqu8 "[rax]", xmm0;
    Mov rdi, 16;
    PrintOutMemory;
    PrintOutNL;

    FreeMemory(address => $address, size=> $N);

    ok Assemble(eq => <<END);
  abcdefghijklmnop
  END


=head3 Nasm::X86::Variable::for($limit, $body)

Iterate the body limit times.

     Parameter  Description
  1  $limit     Limit
  2  $body      Body

B<Example:>


    Vq(limit,10)->for(sub
     {my ($i, $start, $next, $end) = @_;
      $i->print;
     });

    is_deeply Assemble, <<END;
  0000 0000 0000 0000
  0100 0000 0000 0000
  0200 0000 0000 0000
  0300 0000 0000 0000
  0400 0000 0000 0000
  0500 0000 0000 0000
  0600 0000 0000 0000
  0700 0000 0000 0000
  0800 0000 0000 0000
  0900 0000 0000 0000
  END


=head1 Processes

Create and manage processes

=head2 Fork()

Fork


B<Example:>



    Fork;                                                                         # Fork  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Test rax,rax;
    IfNz                                                                          # Parent
     {Mov rbx, rax;
      WaitPid;
      PrintOutRegisterInHex rax;
      PrintOutRegisterInHex rbx;
      KeepFree rax;
      GetPid;                                                                     # Pid of parent as seen in parent
      Mov rcx,rax;
      PrintOutRegisterInHex rcx;
     }
    sub                                                                           # Child
     {Mov r8,rax;
      PrintOutRegisterInHex r8;
      KeepFree rax;
      GetPid;                                                                     # Child pid as seen in child
      Mov r9,rax;
      PrintOutRegisterInHex r9;
      KeepFree rax;
      GetPPid;                                                                    # Parent pid as seen in child
      Mov r10,rax;
      PrintOutRegisterInHex r10;
     };

    my $r = Assemble;

  #    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
  #    r9: 0000 0000 0003 0C63   #2 Pid of child
  #   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
  #   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
  #   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
  #   rcx: 0000 0000 0003 0C60   #6 Pid of parent

    if ($r =~ m(r8:( 0000){4}.*r9:(.*)\s{5,}r10:(.*)\s{5,}rax:(.*)\s{5,}rbx:(.*)\s{5,}rcx:(.*)\s{2,})s)
     {ok $2 eq $4;
      ok $2 eq $5;
      ok $3 eq $6;
      ok $2 gt $6;
     }


=head2 GetPid()

Get process identifier


B<Example:>


    Fork;                                                                         # Fork

    Test rax,rax;
    IfNz                                                                          # Parent
     {Mov rbx, rax;
      WaitPid;
      PrintOutRegisterInHex rax;
      PrintOutRegisterInHex rbx;
      KeepFree rax;

      GetPid;                                                                     # Pid of parent as seen in parent  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      Mov rcx,rax;
      PrintOutRegisterInHex rcx;
     }
    sub                                                                           # Child
     {Mov r8,rax;
      PrintOutRegisterInHex r8;
      KeepFree rax;

      GetPid;                                                                     # Child pid as seen in child  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      Mov r9,rax;
      PrintOutRegisterInHex r9;
      KeepFree rax;
      GetPPid;                                                                    # Parent pid as seen in child
      Mov r10,rax;
      PrintOutRegisterInHex r10;
     };

    my $r = Assemble;

  #    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
  #    r9: 0000 0000 0003 0C63   #2 Pid of child
  #   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
  #   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
  #   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
  #   rcx: 0000 0000 0003 0C60   #6 Pid of parent

    if ($r =~ m(r8:( 0000){4}.*r9:(.*)\s{5,}r10:(.*)\s{5,}rax:(.*)\s{5,}rbx:(.*)\s{5,}rcx:(.*)\s{2,})s)
     {ok $2 eq $4;
      ok $2 eq $5;
      ok $3 eq $6;
      ok $2 gt $6;
     }


=head2 GetPidInHex()

Get process identifier in hex as 8 zero terminated bytes in rax


B<Example:>



    GetPidInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    ok Assemble =~ m(rax: 00);


=head2 GetPPid()

Get parent process identifier


B<Example:>


    Fork;                                                                         # Fork

    Test rax,rax;
    IfNz                                                                          # Parent
     {Mov rbx, rax;
      WaitPid;
      PrintOutRegisterInHex rax;
      PrintOutRegisterInHex rbx;
      KeepFree rax;
      GetPid;                                                                     # Pid of parent as seen in parent
      Mov rcx,rax;
      PrintOutRegisterInHex rcx;
     }
    sub                                                                           # Child
     {Mov r8,rax;
      PrintOutRegisterInHex r8;
      KeepFree rax;
      GetPid;                                                                     # Child pid as seen in child
      Mov r9,rax;
      PrintOutRegisterInHex r9;
      KeepFree rax;

      GetPPid;                                                                    # Parent pid as seen in child  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      Mov r10,rax;
      PrintOutRegisterInHex r10;
     };

    my $r = Assemble;

  #    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
  #    r9: 0000 0000 0003 0C63   #2 Pid of child
  #   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
  #   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
  #   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
  #   rcx: 0000 0000 0003 0C60   #6 Pid of parent

    if ($r =~ m(r8:( 0000){4}.*r9:(.*)\s{5,}r10:(.*)\s{5,}rax:(.*)\s{5,}rbx:(.*)\s{5,}rcx:(.*)\s{2,})s)
     {ok $2 eq $4;
      ok $2 eq $5;
      ok $3 eq $6;
      ok $2 gt $6;
     }


=head2 GetUid()

Get userid of current process


B<Example:>



    GetUid;                                                                       # Userid  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    my $r = Assemble;
    ok $r =~ m(rax:( 0000){3});


=head2 WaitPid()

Wait for the pid in rax to complete


B<Example:>


    Fork;                                                                         # Fork

    Test rax,rax;
    IfNz                                                                          # Parent
     {Mov rbx, rax;

      WaitPid;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      PrintOutRegisterInHex rax;
      PrintOutRegisterInHex rbx;
      KeepFree rax;
      GetPid;                                                                     # Pid of parent as seen in parent
      Mov rcx,rax;
      PrintOutRegisterInHex rcx;
     }
    sub                                                                           # Child
     {Mov r8,rax;
      PrintOutRegisterInHex r8;
      KeepFree rax;
      GetPid;                                                                     # Child pid as seen in child
      Mov r9,rax;
      PrintOutRegisterInHex r9;
      KeepFree rax;
      GetPPid;                                                                    # Parent pid as seen in child
      Mov r10,rax;
      PrintOutRegisterInHex r10;
     };

    my $r = Assemble;

  #    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
  #    r9: 0000 0000 0003 0C63   #2 Pid of child
  #   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
  #   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
  #   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
  #   rcx: 0000 0000 0003 0C60   #6 Pid of parent

    if ($r =~ m(r8:( 0000){4}.*r9:(.*)\s{5,}r10:(.*)\s{5,}rax:(.*)\s{5,}rbx:(.*)\s{5,}rcx:(.*)\s{2,})s)
     {ok $2 eq $4;
      ok $2 eq $5;
      ok $3 eq $6;
      ok $2 gt $6;
     }


=head2 ReadTimeStampCounter()

Read the time stamp counter and return the time in nanoseconds in rax


B<Example:>


    for(1..10)

     {ReadTimeStampCounter;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      PrintOutRegisterInHex rax;
     }

    my @s = split /
/, Assemble;
    my @S = sort @s;
    is_deeply \@s, \@S;


=head1 Stack

Manage data on the stack

=head2 Push, Pop, Peek

Generic versions of push, pop, peek

=head3 PopR(@r)

Pop registers from the stack

     Parameter  Description
  1  @r         Register

B<Example:>


    Mov rax, 0x11111111;
    Mov rbx, 0x22222222;
    PushR my @save = (rax, rbx);
    Mov rax, 0x33333333;

    PopR @save;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;

    is_deeply Assemble,<<END;
     rax: 0000 0000 1111 1111
     rbx: 0000 0000 2222 2222
  END


=head3 PeekR($r)

Peek at register on stack

     Parameter  Description
  1  $r         Register

=head2 Declarations

Declare variables and structures

=head3 Structures

Declare a structure

=head4 Structure()

Create a structure addressed by a register


=head4 Nasm::X86::Structure::field($structure, $length, $comment)

Add a field of the specified length with an optional comment

     Parameter   Description
  1  $structure  Structure data descriptor
  2  $length     Length of data
  3  $comment    Optional comment

=head4 Nasm::X86::StructureField::addr($field, $register)

Address a field in a structure by either the default register or the named register

     Parameter  Description
  1  $field     Field
  2  $register  Optional address register else rax

=head4 All8Structure($N)

Create a structure consisting of 8 byte fields

     Parameter  Description
  1  $N         Number of variables required

=head3 Stack Frame

Declare local variables in a frame on the stack

=head4 LocalData()

Map local data


=head4 Nasm::X86::LocalData::start($local)

Start a local data area on the stack

     Parameter  Description
  1  $local     Local data descriptor

=head4 Nasm::X86::LocalData::free($local)

Free a local data area on the stack

     Parameter  Description
  1  $local     Local data descriptor

=head4 Nasm::X86::LocalData::variable($local, $length, $comment)

Add a local variable

     Parameter  Description
  1  $local     Local data descriptor
  2  $length    Length of data
  3  $comment   Optional comment

=head4 Nasm::X86::LocalVariable::stack($variable)

Address a local variable on the stack

     Parameter  Description
  1  $variable  Variable

=head4 Nasm::X86::LocalData::allocate8($local, @comments)

Add some 8 byte local variables and return an array of variable definitions

     Parameter  Description
  1  $local     Local data descriptor
  2  @comments  Optional comment

=head4 AllocateAll8OnStack($N)

Create a local data descriptor consisting of the specified number of 8 byte local variables and return an array: (local data descriptor,  variable definitions...)

     Parameter  Description
  1  $N         Number of variables required

=head1 Memory

Allocate and print memory

=head2 PrintMemoryInHex($channel)

Dump memory from the address in rax for the length in rdi on the specified channel

     Parameter  Description
  1  $channel   Channel

=head2 PrintErrMemoryInHex()

Dump memory from the address in rax for the length in rdi on stderr


=head2 PrintOutMemoryInHex()

Dump memory from the address in rax for the length in rdi on stdout


B<Example:>


    Mov rax, 0x07654321;
    Shl rax, 32;
    Or  rax, 0x07654321;
    PushR rax;

    PrintOutRaxInHex;
    PrintOutNL;
    PrintOutRaxInReverseInHex;
    PrintOutNL;
    KeepFree rax;

    Mov rax, rsp;
    Mov rdi, 8;

    PrintOutMemoryInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;
    PopR rax;
    KeepFree rax, rdi;

    Mov rax, 4096;
    PushR rax;
    Mov rax, rsp;
    Mov rdi, 8;

    PrintOutMemoryInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;
    PopR rax;

    is_deeply Assemble, <<END;
  0765 4321 0765 4321
  2143 6507 2143 6507
  2143 6507 2143 6507
  0010 0000 0000 0000
  END


=head2 PrintErrMemoryInHexNL()

Dump memory from the address in rax for the length in rdi and then print a new line


=head2 PrintOutMemoryInHexNL()

Dump memory from the address in rax for the length in rdi and then print a new line


B<Example:>


    my $N = 256;
    my $s = Rb 0..$N-1;
    AllocateMemory(Vq(size, $N), my $a = Vq(address));
    CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);

    AllocateMemory(Vq(size, $N), my $b = Vq(address));
    CopyMemory(source => $a, target => $b, Vq(size, $N));

    $b->setReg(rax);
    Mov rdi, $N;

    PrintOutMemoryInHexNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    is_deeply Assemble, <<END;
  0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
  END


=head2 PrintMemory()

Print the memory addressed by rax for a length of rdi on the specified channel


B<Example:>


    ReadFile(Vq(file, Rs($0)), (my $s = Vq(size)), my $a = Vq(address));          # Read file
    $a->setReg(rax);                                                              # Address of file in memory
    $s->setReg(rdi);                                                              # Length  of file in memory
    PrintOutMemory;                                                               # Print contents of memory to stdout

    my $r = Assemble;                                                             # Assemble and execute
    ok stringMd5Sum($r) eq fileMd5Sum($0);                                          # Output contains this file


=head2 PrintErrMemory()

Print the memory addressed by rax for a length of rdi on stderr


=head2 PrintOutMemory()

Print the memory addressed by rax for a length of rdi on stdout


B<Example:>


    Comment "Print a string from memory";
    my $s = "Hello World";
    Mov rax, Rs($s);
    Mov rdi, length $s;

    PrintOutMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(Hello World);


=head2 PrintErrMemoryNL()

Print the memory addressed by rax for a length of rdi followed by a new line on stderr


=head2 PrintOutMemoryNL()

Print the memory addressed by rax for a length of rdi followed by a new line on stdout


=head2 AllocateMemory(@variables)

Allocate the specified amount of memory via mmap and return its address

     Parameter   Description
  1  @variables  Parameters

B<Example:>


    my $N = Vq(size, 2048);
    my $q = Rs('a'..'p');

    AllocateMemory($N, my $address = Vq(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Vmovdqu8 xmm0, "[$q]";
    $address->setReg(rax);
    Vmovdqu8 "[rax]", xmm0;
    Mov rdi, 16;
    PrintOutMemory;
    PrintOutNL;

    FreeMemory(address => $address, size=> $N);

    ok Assemble(eq => <<END);
  abcdefghijklmnop
  END

    my $N = Vq(size, 4096);                                                       # Size of the initial allocation which should be one or more pages


    AllocateMemory($N, my $A = Vq(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ClearMemory($N, $A);

    $A->setReg(rax);
    $N->setReg(rdi);
    PrintOutMemoryInHexNL;

    FreeMemory($N, $A);

    ok Assemble(eq => <<END);
  0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END

    my $N = 256;
    my $s = Rb 0..$N-1;

    AllocateMemory(Vq(size, $N), my $a = Vq(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);


    AllocateMemory(Vq(size, $N), my $b = Vq(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CopyMemory(source => $a, target => $b, Vq(size, $N));

    $b->setReg(rax);
    Mov rdi, $N;
    PrintOutMemoryInHexNL;

    is_deeply Assemble, <<END;
  0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
  END


=head2 FreeMemory(@variables)

Free memory

     Parameter   Description
  1  @variables  Variables

B<Example:>


    my $N = Vq(size, 4096);                                                       # Size of the initial allocation which should be one or more pages

    AllocateMemory($N, my $A = Vq(address));

    ClearMemory($N, $A);

    $A->setReg(rax);
    $N->setReg(rdi);
    PrintOutMemoryInHexNL;


    FreeMemory($N, $A);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble(eq => <<END);
  0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head2 ClearMemory(@variables)

Clear memory - the address of the memory is in rax, the length in rdi

     Parameter   Description
  1  @variables  Variables

B<Example:>


    my $N = Vq(size, 4096);                                                       # Size of the initial allocation which should be one or more pages

    AllocateMemory($N, my $A = Vq(address));


    ClearMemory($N, $A);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    $A->setReg(rax);
    $N->setReg(rdi);
    PrintOutMemoryInHexNL;

    FreeMemory($N, $A);

    ok Assemble(eq => <<END);
  0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head2 CopyMemory(@variables)

Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi

     Parameter   Description
  1  @variables  Variables

B<Example:>


    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;
    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

    Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rdi, 16;
    Mov rsi, $s;

    CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);

    my $N = 256;
    my $s = Rb 0..$N-1;
    AllocateMemory(Vq(size, $N), my $a = Vq(address));

    CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    AllocateMemory(Vq(size, $N), my $b = Vq(address));

    CopyMemory(source => $a, target => $b, Vq(size, $N));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    $b->setReg(rax);
    Mov rdi, $N;
    PrintOutMemoryInHexNL;

    is_deeply Assemble, <<END;
  0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
  END


=head1 Files

Process a file

=head2 OpenRead()

Open a file, whose name is addressed by rax, for read and return the file descriptor in rax


B<Example:>


    Mov rax, Rs($0);                                                              # File to read

    OpenRead;                                                                     # Open file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    CloseFile;                                                                    # Close file
    PrintOutRegisterInHex rax;
    KeepFree rax, rdi;

    Mov rax, Rs(my $f = "zzzTemporaryFile.txt");                                  # File to write
    OpenWrite;                                                                    # Open file
    CloseFile;                                                                    # Close file

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rax: 0000 0000 0000 0000
  END
    ok -e $f;                                                                     # Created file
    unlink $f;


=head2 OpenWrite()

Create the file named by the terminated string addressed by rax for write


B<Example:>


    Mov rax, Rs($0);                                                              # File to read
    OpenRead;                                                                     # Open file
    PrintOutRegisterInHex rax;
    CloseFile;                                                                    # Close file
    PrintOutRegisterInHex rax;
    KeepFree rax, rdi;

    Mov rax, Rs(my $f = "zzzTemporaryFile.txt");                                  # File to write

    OpenWrite;                                                                    # Open file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CloseFile;                                                                    # Close file

    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rax: 0000 0000 0000 0000
  END
    ok -e $f;                                                                     # Created file
    unlink $f;


=head2 CloseFile()

Close the file whose descriptor is in rax


B<Example:>


    Mov rax, Rs($0);                                                              # File to read
    OpenRead;                                                                     # Open file
    PrintOutRegisterInHex rax;

    CloseFile;                                                                    # Close file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    KeepFree rax, rdi;

    Mov rax, Rs(my $f = "zzzTemporaryFile.txt");                                  # File to write
    OpenWrite;                                                                    # Open file

    CloseFile;                                                                    # Close file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    is_deeply Assemble, <<END;
     rax: 0000 0000 0000 0003
     rax: 0000 0000 0000 0000
  END
    ok -e $f;                                                                     # Created file
    unlink $f;


=head2 StatSize()

Stat a file whose name is addressed by rax to get its size in rax


B<Example:>


    Mov rax, Rs($0);                                                              # File to stat

    StatSize;                                                                     # Stat the file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    my $r = Assemble =~ s( ) ()gsr;
    if ($r =~ m(rax:([0-9a-f]{16}))is)                                            # Compare file size obtained with that from fileSize()
     {is_deeply $1, sprintf("%016X", fileSize($0));
     }


=head2 ReadFile(@variables)

Read a file whose name is addressed by rax into memory.  The address of the mapped memory and its length are returned in registers rax,rdi

     Parameter   Description
  1  @variables  Variables

B<Example:>



    ReadFile(Vq(file, Rs($0)), (my $s = Vq(size)), my $a = Vq(address));          # Read file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->setReg(rax);                                                              # Address of file in memory
    $s->setReg(rdi);                                                              # Length  of file in memory
    PrintOutMemory;                                                               # Print contents of memory to stdout

    my $r = Assemble;                                                             # Assemble and execute
    ok stringMd5Sum($r) eq fileMd5Sum($0);                                          # Output contains this file


=head1 Short Strings

Operations on Short Strings

=head2 LoadShortStringFromMemoryToZmm2($zmm)

Load the short string addressed by rax into the zmm register with the specified number

     Parameter  Description
  1  $zmm       Zmm register to load

=head2 LoadShortStringFromMemoryToZmm($zmm, $address)

Load the short string addressed by rax into the zmm register with the specified number

     Parameter  Description
  1  $zmm       Zmm register to load
  2  $address   Address of string in memory

B<Example:>


    my $s = Rb(3, 0x01, 0x02, 0x03);
    my $t = Rb(7, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a);


    LoadShortStringFromMemoryToZmm 0, $s;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    LoadShortStringFromMemoryToZmm 1, $t;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    ConcatenateShortStrings(0, 1);
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 000A 0908   0706 0504 0302 010A);
    ok $r =~ m(xmm1: 0000 0000 0000 0000   0A09 0807 0605 0407);


=head2 GetLengthOfShortString($reg, $zmm)

Get the length of the short string held in the numbered zmm register into the specified register

     Parameter  Description
  1  $reg       Register to hold length
  2  $zmm       Number of zmm register containing string

=head2 SetLengthOfShortString($zmm, $reg)

Set the length of the short string held in the numbered zmm register into the specified register

     Parameter  Description
  1  $zmm       Number of zmm register containing string
  2  $reg       Register to hold length

=head2 ConcatenateShortStrings($left, $right)

Concatenate the numbered source zmm containing a short string with the short string in the numbered target zmm.

     Parameter  Description
  1  $left      Target zmm
  2  $right     Source zmm

=head1 Hash functions

Hash functions

=head2 Hash()

Hash a string addressed by rax with length held in rdi and return the hash code in r15


B<Example:>


    Mov rax, "[rbp+24]";
    Cstrlen;                                                                      # Length of string to hash
    Mov rdi, r15;

    Hash();                                                                       # Hash string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    PrintOutRegisterInHex r15;

    my $e = Assemble keep=>'hash';                                                # Assemble to the specified file name
    ok qx($e "")  =~ m(r15: 0000 3F80 0000 3F80);                                 # Test well known hashes
    ok qx($e "a") =~ m(r15: 0000 3F80 C000 45B2);


    if (0 and $develop)                                                           # Hash various strings  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {my %r; my %f; my $count = 0;
      my $N = RegisterSize zmm0;

      if (1)                                                                      # Fixed blocks
       {for my $l(qw(a ab abc abcd), 'a a', 'a  a')
         {for my $i(1..$N)
           {my $t = $l x $i;
            last if $N < length $t;
            my $s = substr($t.(' ' x $N), 0, $N);
            next if $f{$s}++;
            my $r = qx($e "$s");
            say STDERR "$count  $r";
            if ($r =~ m(^.*r15:\s*(.*)$)m)
             {push $r{$1}->@*, $s;
              ++$count;
             }
           }
         }
       }

      if (1)                                                                      # Variable blocks
       {for my $l(qw(a ab abc abcd), '', 'a a', 'a  a')
         {for my $i(1..$N)
           {my $t = $l x $i;
            next if $f{$t}++;
            my $r = qx($e "$t");
            say STDERR "$count  $r";
            if ($r =~ m(^.*r15:\s*(.*)$)m)
             {push $r{$1}->@*, $t;
              ++$count;
             }
           }
         }
       }
      for my $r(keys %r)
       {delete $r{$r} if $r{$r}->@* < 2;
       }

      say STDERR dump(\%r);
      say STDERR "Keys hashed: ", $count;
      confess "Duplicates : ",  scalar keys(%r);
     }


=head1 Byte Strings

Operations on Byte Strings

=head2 Cstrlen()

Length of the C style string addressed by rax returning the length in r15


B<Example:>


    my $s = Rs("abcd");
    Mov rax, $s;

    Cstrlen;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex r15;
    ok Assemble =~ m(r15: 0000 0000 0000 0004);


=head2 CreateByteString(%options)

Create an relocatable string of bytes in an arena and returns its address in rax. Optionally add a chain header so that 64 byte blocks of memory can be freed and reused within the byte string.

     Parameter  Description
  1  %options   Free=>1 adds a free chain.

B<Example:>



    my $a = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('aa');
    $a->out;
    PrintOutNL;
    is_deeply Assemble, <<END;                                                    # Assemble and execute
  aa
  END


    my $a = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $b = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('aa');
    $b->q('bb');
    $a->out;
    PrintOutNL;
    $b->out;
    PrintOutNL;
    is_deeply Assemble, <<END;                                                    # Assemble and execute
  aa
  bb
  END


    my $a = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $b = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('aa');
    $a->q('AA');
    $a->out;
    PrintOutNL;
    is_deeply Assemble, <<END;                                                    # Assemble and execute
  aaAA
  END


    my $a = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $b = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('aa');
    $b->q('bb');
    $a->q('AA');
    $b->q('BB');
    $a->q('aa');
    $b->q('bb');
    $a->out;
    $b->out;
    PrintOutNL;
    is_deeply Assemble, <<END;                                                    # Assemble and execute
  aaAAaabbBBbb
  END


    my $a = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('ab');

    my $b = CreateByteString;                                                     # Create target byte string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->bs(r15);
    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);
    $a->append(source=>$b->bs);
    $b->append(source=>$a->bs);
    $a->append(source=>$b->bs);
    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);


    $a->out;   PrintOutNL;                                                        # Print byte string
    $b->out;   PrintOutNL;                                                        # Print byte string
    $a->length(my $sa = Vq(size)); $sa->outNL;
    $b->length(my $sb = Vq(size)); $sb->outNL;
    $a->clear;
    $a->length(my $sA = Vq(size)); $sA->outNL;
    $b->length(my $sB = Vq(size)); $sB->outNL;

    is_deeply Assemble, <<END;                                                    # Assemble and execute
  abababababababab
  ababababababababababababababababababababababababababababababababababababab
  size: 0000 0000 0000 0010
  size: 0000 0000 0000 004A
  size: 0000 0000 0000 0000
  size: 0000 0000 0000 004A
  END


=head2 Nasm::X86::ByteString::length($byteString, @variables)

Get the length of a byte string

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

=head2 Nasm::X86::ByteString::makeReadOnly($byteString)

Make a byte string read only

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 Nasm::X86::ByteString::makeWriteable($byteString)

Make a byte string writable

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 Nasm::X86::ByteString::allocate($byteString, @variables)

Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

=head2 Nasm::X86::ByteString::blockSize($byteString)

Size of a block

     Parameter    Description
  1  $byteString  Byte string

=head2 Nasm::X86::ByteString::allocBlock($byteString, @variables)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter    Description
  1  $byteString  Byte string
  2  @variables   Variables

B<Example:>


    my $a = CreateByteString;              $a->dump;
    $a->allocBlock(my $b1 = Vq(offset));   $a->dump;
    $a->allocBlock(my $b2 = Vq(offset));   $a->dump;
    $a->freeBlock($b2);                    $a->dump;
    $a->freeBlock($b1);                    $a->dump;

    ok Assemble(debug => 0, eq => <<END);
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0018
  0000: 0010 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0058
  0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head2 Nasm::X86::ByteString::freeBlock($byteString, @variables)

Free a block in a byte string by placing it on the free chain

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

B<Example:>


    my $a = CreateByteString;              $a->dump;
    $a->allocBlock(my $b1 = Vq(offset));   $a->dump;
    $a->allocBlock(my $b2 = Vq(offset));   $a->dump;
    $a->freeBlock($b2);                    $a->dump;
    $a->freeBlock($b1);                    $a->dump;

    ok Assemble(debug => 0, eq => <<END);
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0018
  0000: 0010 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0058
  0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head2 Nasm::X86::ByteString::getBlock($byteString, $bsa, $block, $zmm)

Get the block with the specified offset in the specified block string and return it in the numbered zmm

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $bsa         Byte string variable
  3  $block       Offset of the block as a variable
  4  $zmm         Number of zmm register to contain block

=head2 Nasm::X86::ByteString::putBlock($byteString, $bsa, $block, $zmm)

Write the numbered zmm to the block at the specified offset in the specified byte string

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $bsa         Byte string variable
  3  $block       Block in byte string
  4  $zmm         Content variable

=head2 Nasm::X86::ByteString::m($byteString, @variables)

Append the content with length rdi addressed by rsi to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

=head2 Nasm::X86::ByteString::q($byteString, $string)

Append a constant string to the byte string

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $string      String

=head2 Nasm::X86::ByteString::ql($byteString, $const)

Append a quoted string containing new line characters to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string
  2  $const       Constant

=head2 Nasm::X86::ByteString::char($byteString, $char)

Append a character expressed as a decimal number to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $char        Number of character to be appended

=head2 Nasm::X86::ByteString::nl($byteString)

Append a new line to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 Nasm::X86::ByteString::z($byteString)

Append a trailing zero to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 Nasm::X86::ByteString::rdiInHex()

Add the content of register rdi in hexadecimal in big endian notation to a byte string


=head2 Nasm::X86::ByteString::append($byteString, @variables)

Append one byte string to another

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

=head2 Nasm::X86::ByteString::clear($byteString)

Clear the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 Nasm::X86::ByteString::write($byteString, @variables)

Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

=head2 Nasm::X86::ByteString::read($byteString, @variables)

Read the named file (terminated with a zero byte) and place it into the named byte string.

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

=head2 Nasm::X86::ByteString::out($byteString)

Print the specified byte string addressed by rax on sysout

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 executeFileViaBash(@variables)

Execute the file named in the byte string addressed by rax with bash

     Parameter   Description
  1  @variables  Variables

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write         (my $f = Vq('file', Rs("zzz.sh")));                         # Write code to a file

    executeFileViaBash($f);                                                       # Execute the file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    unlinkFile        ($f);                                                       # Delete the file

    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);                                            # The Intel Software Development Emulator is way too slow on these operations.


=head2 unlinkFile(@variables)

Unlink the named file

     Parameter   Description
  1  @variables  Variables

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write         (my $f = Vq('file', Rs("zzz.sh")));                         # Write code to a file
    executeFileViaBash($f);                                                       # Execute the file

    unlinkFile        ($f);                                                       # Delete the file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);                                            # The Intel Software Development Emulator is way too slow on these operations.


=head2 Nasm::X86::ByteString::dump($byteString)

Dump details of a byte string

     Parameter    Description
  1  $byteString  Byte string descriptor

=head1 Block Strings

Strings made from zmm sized blocks of text

=head2 Nasm::X86::ByteString::CreateBlockString($byteString)

Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the byte string addressed by rax and return its descriptor

     Parameter    Description
  1  $byteString  Byte string description

=head2 Nasm::X86::BlockString::address($blockString)

Address of a block string

     Parameter     Description
  1  $blockString  Block string descriptor

=head2 Nasm::X86::BlockString::allocBlock($blockString, @variables)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter     Description
  1  $blockString  Block string descriptor
  2  @variables    Variables

=head2 Nasm::X86::BlockString::getBlockLengthInZmm($blockString, $zmm)

Get the block length of the numbered zmm and return it in a variable

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $zmm          Number of zmm register

=head2 Nasm::X86::BlockString::setBlockLengthInZmm($blockString, $length, $zmm)

Set the block length of the numbered zmm to the specified length

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $length       Length as a variable
  3  $zmm          Number of zmm register

=head2 Nasm::X86::BlockString::getBlock($blockString, $bsa, $block, $zmm)

Get the block with the specified offset in the specified block string and return it in the numbered zmm

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $bsa          Byte string variable
  3  $block        Offset of the block as a variable
  4  $zmm          Number of zmm register to contain block

=head2 Nasm::X86::BlockString::putBlock($blockString, $bsa, $block, $zmm)

Write the numbered zmm to the block at the specified offset in the specified byte string

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $bsa          Byte string variable
  3  $block        Block in byte string
  4  $zmm          Content variable

=head2 Nasm::X86::BlockString::getNextAndPrevBlockOffsetFromZmm($blockString, $zmm)

Get the offsets of the next and previous blocks as variables from the specified zmm

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $zmm          Zmm containing block

=head2 Nasm::X86::BlockString::putNextandPrevBlockOffsetIntoZmm($blockString, $zmm, $next, $prev)

Save next and prev offsets into a zmm representing a block

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $zmm          Zmm containing block
  3  $next         Next offset as a variable
  4  $prev         Prev offset as a variable

=head2 Nasm::X86::BlockString::dump($blockString)

Dump a block string to sysout

     Parameter     Description
  1  $blockString  Block string descriptor

=head2 Nasm::X86::BlockString::len($blockString, $size)

Find the length of a block string

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $size         Size variable

=head2 Nasm::X86::BlockString::concatenate($target, $source)

Concatenate two block strings by appending a copy of the source to the target block string.

     Parameter  Description
  1  $target    Target block string
  2  $source    Source block string

=head2 Nasm::X86::BlockString::insertChar($blockString, @variables)

Insert a character into a block string

     Parameter     Description
  1  $blockString  Block string
  2  @variables    Variables

=head2 Nasm::X86::BlockString::deleteChar($blockString, @variables)

Delete a character in a block string

     Parameter     Description
  1  $blockString  Block string
  2  @variables    Variables

=head2 Nasm::X86::BlockString::getCharacter($blockString, @variables)

Get a character from a block string

     Parameter     Description
  1  $blockString  Block string
  2  @variables    Variables

=head2 Nasm::X86::BlockString::append($blockString, @variables)

Append the specified content in memory to the specified block string

     Parameter     Description
  1  $blockString  Block string descriptor
  2  @variables    Variables

=head2 Nasm::X86::BlockString::clear($blockString)

Clear the block by freeing all but the first block

     Parameter     Description
  1  $blockString  Block string descriptor

=head1 Block Array

Array constructed as a tree of blocks in a byte string

=head2 Nasm::X86::ByteString::CreateBlockArray($byteString)

Create a block array in a byte string

     Parameter    Description
  1  $byteString  Byte string description

=head2 Nasm::X86::BlockArray::address($blockArray)

Address of a block string

     Parameter    Description
  1  $blockArray  Block array descriptor

=head2 Nasm::X86::BlockArray::allocBlock($blockArray, @variables)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter    Description
  1  $blockArray  Block array descriptor
  2  @variables   Variables

=head2 Nasm::X86::BlockArray::dump($blockArray, @variables)

Dump a block array

     Parameter    Description
  1  $blockArray  Block array descriptor
  2  @variables   Variables

=head2 Nasm::X86::BlockArray::push($blockArray, @variables)

Push an element onto the array

     Parameter    Description
  1  $blockArray  Block array descriptor
  2  @variables   Variables

=head2 Nasm::X86::BlockArray::pop($blockArray, @variables)

Pop an element from an array

     Parameter    Description
  1  $blockArray  Block array descriptor
  2  @variables   Variables

=head2 Nasm::X86::BlockArray::get($blockArray, @variables)

Get an element from the array

     Parameter    Description
  1  $blockArray  Block array descriptor
  2  @variables   Variables

=head2 Nasm::X86::BlockArray::put($blockArray, @variables)

Put an element into an array as long as it is with in its limits established by pushing.

     Parameter    Description
  1  $blockArray  Block array descriptor
  2  @variables   Variables

=head1 Assemble

Assemble generated code

=head2 CallC($sub, @parameters)

Call a C subroutine

     Parameter    Description
  1  $sub         Name of the sub to call
  2  @parameters  Parameters

B<Example:>


    my $format = Rs "Hello %s
";
    my $data   = Rs "World";

    Extern qw(printf exit malloc strcpy); Link 'c';


    CallC 'malloc', length($format)+1;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov r15, rax;

    CallC 'strcpy', r15, $format;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    CallC 'printf', r15, $data;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    CallC 'exit', 0;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble(eq => <<END);
  Hello World
  END


=head2 Extern(@externalReferences)

Name external references

     Parameter            Description
  1  @externalReferences  External references

B<Example:>


    my $format = Rs "Hello %s
";
    my $data   = Rs "World";


    Extern qw(printf exit malloc strcpy); Link 'c';  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    CallC 'malloc', length($format)+1;
    Mov r15, rax;
    CallC 'strcpy', r15, $format;
    CallC 'printf', r15, $data;
    CallC 'exit', 0;

    ok Assemble(eq => <<END);
  Hello World
  END


=head2 Link(@libraries)

Libraries to link with

     Parameter   Description
  1  @libraries  External references

B<Example:>


    my $format = Rs "Hello %s
";
    my $data   = Rs "World";


    Extern qw(printf exit malloc strcpy); Link 'c';  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    CallC 'malloc', length($format)+1;
    Mov r15, rax;
    CallC 'strcpy', r15, $format;
    CallC 'printf', r15, $data;
    CallC 'exit', 0;

    ok Assemble(eq => <<END);
  Hello World
  END


=head2 Start()

Initialize the assembler


=head2 Exit($c)

Exit with the specified return code or zero if no return code supplied.  Assemble() automatically adds a call to Exit(0) if the last operation in the program is not a call to Exit.

     Parameter  Description
  1  $c         Return code

=head2 Assemble(%options)

Assemble the generated code

     Parameter  Description
  1  %options   Options

B<Example:>


    PrintOutStringNL "Hello World";
    PrintOutStringNL "Hello
World";
    PrintErrStringNL "Hello World";


    ok Assemble(debug => 0, eq => <<END);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

  Hello World
  Hello
  World
  END



=head2 Nasm::X86 Definition


Block string definition




=head3 Output fields


=head4 bs

Bytes string definition

=head4 data

The first 8 bytes of the data

=head4 depth

Lexical depth of scope

=head4 expr

Expression that initializes the variable

=head4 first

Variable addressing first block in block string

=head4 free

Free chain offset

=head4 label

Address in memory

=head4 laneSize

Size of the lanes in this variable

=head4 length

Maximum length in a block

=head4 links

Location of links in bytes in zmm

=head4 name

Name of the variable

=head4 next

Location of next offset in block in bytes

=head4 number

Number of this scope

=head4 parent

Parent scope

=head4 prev

Location of prev offset in block in bytes

=head4 purpose

Purpose of this variable

=head4 reference

Reference to another variable

=head4 saturate

Computations should saturate rather then wrap if true

=head4 signed

Elements of x|y|zmm registers are signed if true

=head4 size

Size field details

=head4 slots1

Number of slots in first block

=head4 slots2

Number of slots in second and subsequent blocks

=head4 structure

Structure details

=head4 used

Used field details

=head4 width

Width of each element



=head1 Attributes


The following is a list of all the attributes in this package.  A method coded
with the same name in your package will over ride the method of the same name
in this package and thus provide your value for the attribute in place of the
default value supplied for this attribute by this package.

=head2 Replaceable Attribute List


Pi32 Pi64


=head2 Pi32

Pi as a 32 bit float


=head2 Pi64

Pi as a 64 bit float




=head1 Private Methods

=head2 Label()

Create a unique label


=head2 Dbwdq($s, @d)

Layout data

     Parameter  Description
  1  $s         Element size
  2  @d         Data to be laid out

=head2 Rbwdq($s, @d)

Layout data

     Parameter  Description
  1  $s         Element size
  2  @d         Data to be laid out

=head2 hexTranslateTable()

Create/address a hex translate table and return its label


=head2 PrintOutRipInHex()

Print the instruction pointer in hex


=head2 PrintOutRflagsInHex()

Print the flags register in hex


=head2 Nasm::X86::Variable::confirmIsMemory($memory, $address, $length)

Check that variable describes allocated memory and optionally load registers with its length and size

     Parameter  Description
  1  $memory    Variable describing memory as returned by Allocate Memory
  2  $address   Register to contain address
  3  $length    Register to contain size

=head2 PushRR(@r)

Push registers onto the stack without tracking

     Parameter  Description
  1  @r         Register

=head2 PushR(@r)

Push registers onto the stack

     Parameter  Description
  1  @r         Register

B<Example:>


    Mov rax, 0x11111111;
    Mov rbx, 0x22222222;

    PushR my @save = (rax, rbx);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 0x33333333;
    PopR @save;
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;

    is_deeply Assemble,<<END;
     rax: 0000 0000 1111 1111
     rbx: 0000 0000 2222 2222
  END


=head2 PopRR(@r)

Pop registers from the stack without tracking

     Parameter  Description
  1  @r         Register

=head2 Nasm::X86::ByteString::updateSpace($byteString, @variables)

Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  @variables   Variables

=head2 Nasm::X86::ByteString::firstFreeBlock($byteString)

Create and load a variable with the first free block on the free block chain or zero if no such block in the given byte string

     Parameter    Description
  1  $byteString  Byte string address as a variable

=head2 Nasm::X86::ByteString::setFirstFreeBlock($byteString, $offset)

Set the first free block field from a variable

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $offset      First free block offset as a variable

=head2 LocateIntelEmulator()

Locate the Intel Software Development Emulator


=head2 removeNonAsciiChars($string)

Return a copy of the specified string with all the non ascii characters removed

     Parameter  Description
  1  $string    String

=head2 totalBytesAssembled()

Total size in bytes of all files assembled during testing



=head1 Index


1 L<All8Structure|/All8Structure> - Create a structure consisting of 8 byte fields

2 L<AllocateAll8OnStack|/AllocateAll8OnStack> - Create a local data descriptor consisting of the specified number of 8 byte local variables and return an array: (local data descriptor,  variable definitions.

3 L<AllocateMemory|/AllocateMemory> - Allocate the specified amount of memory via mmap and return its address

4 L<Assemble|/Assemble> - Assemble the generated code

5 L<CallC|/CallC> - Call a C subroutine

6 L<ClearMemory|/ClearMemory> - Clear memory - the address of the memory is in rax, the length in rdi

7 L<ClearRegisters|/ClearRegisters> - Clear registers by setting them to zero

8 L<ClearZF|/ClearZF> - Clear the zero flag

9 L<CloseFile|/CloseFile> - Close the file whose descriptor is in rax

10 L<Comment|/Comment> - Insert a comment into the assembly code

11 L<ConcatenateShortStrings|/ConcatenateShortStrings> - Concatenate the numbered source zmm containing a short string with the short string in the numbered target zmm.

12 L<Copy|/Copy> - Copy the source to the target register

13 L<CopyMemory|/CopyMemory> - Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi

14 L<cr|/cr> - Call a subroutine with a reordering of the registers.

15 L<CreateByteString|/CreateByteString> - Create an relocatable string of bytes in an arena and returns its address in rax.

16 L<Cstrlen|/Cstrlen> - Length of the C style string addressed by rax returning the length in r15

17 L<cxr|/cxr> - Call a subroutine with a reordering of the xmm registers.

18 L<Db|/Db> - Layout bytes in the data segment and return their label

19 L<Dbwdq|/Dbwdq> - Layout data

20 L<DComment|/DComment> - Insert a comment into the data segment

21 L<Dd|/Dd> - Layout double words in the data segment and return their label

22 L<Decrement|/Decrement> - Decrement the specified register

23 L<Dq|/Dq> - Layout quad words in the data segment and return their label

24 L<Ds|/Ds> - Layout bytes in memory and return their label

25 L<Dw|/Dw> - Layout words in the data segment and return their label

26 L<executeFileViaBash|/executeFileViaBash> - Execute the file named in the byte string addressed by rax with bash

27 L<Exit|/Exit> - Exit with the specified return code or zero if no return code supplied.

28 L<Extern|/Extern> - Name external references

29 L<Float32|/Float32> - 32 bit float

30 L<Float64|/Float64> - 64 bit float

31 L<For|/For> - For - iterate the body as long as register is less than limit incrementing by increment each time

32 L<ForEver|/ForEver> - Iterate for ever

33 L<ForIn|/ForIn> - For - iterate the full body as long as register plus increment is less than than limit incrementing by increment each time then increment the last body for the last non full block.

34 L<Fork|/Fork> - Fork

35 L<FreeMemory|/FreeMemory> - Free memory

36 L<getBFromXmmAsVariable|/getBFromXmmAsVariable> - Get the byte from the numbered xmm register and return it in a variable

37 L<getBFromZmmAsVariable|/getBFromZmmAsVariable> - Get the byte from the numbered zmm register and return it in a variable

38 L<getBwdqFromMmAsVariable|/getBwdqFromMmAsVariable> - Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable

39 L<getDFromXmmAsVariable|/getDFromXmmAsVariable> - Get the double word from the numbered xmm register and return it in a variable

40 L<getDFromZmmAsVariable|/getDFromZmmAsVariable> - Get the double word from the numbered zmm register and return it in a variable

41 L<GetLengthOfShortString|/GetLengthOfShortString> - Get the length of the short string held in the numbered zmm register into the specified register

42 L<GetPid|/GetPid> - Get process identifier

43 L<GetPidInHex|/GetPidInHex> - Get process identifier in hex as 8 zero terminated bytes in rax

44 L<GetPPid|/GetPPid> - Get parent process identifier

45 L<getQFromXmmAsVariable|/getQFromXmmAsVariable> - Get the quad word from the numbered xmm register and return it in a variable

46 L<getQFromZmmAsVariable|/getQFromZmmAsVariable> - Get the quad word from the numbered zmm register and return it in a variable

47 L<GetUid|/GetUid> - Get userid of current process

48 L<getWFromXmmAsVariable|/getWFromXmmAsVariable> - Get the word from the numbered xmm register and return it in a variable

49 L<getWFromZmmAsVariable|/getWFromZmmAsVariable> - Get the word from the numbered zmm register and return it in a variable

50 L<Hash|/Hash> - Hash a string addressed by rax with length held in rdi and return the hash code in r15

51 L<hexTranslateTable|/hexTranslateTable> - Create/address a hex translate table and return its label

52 L<If|/If> - If

53 L<IfEq|/IfEq> - If equal execute the then body else the else body

54 L<IfGe|/IfGe> - If greater than or equal execute the then body else the else body

55 L<IfGt|/IfGt> - If greater than execute the then body else the else body

56 L<IfLe|/IfLe> - If less than or equal execute the then body else the else body

57 L<IfLt|/IfLt> - If less than execute the then body else the else body

58 L<IfNe|/IfNe> - If not equal execute the then body else the else body

59 L<IfNz|/IfNz> - If not zero execute the then body else the else body

60 L<Increment|/Increment> - Increment the specified register

61 L<InsertIntoXyz|/InsertIntoXyz> - Shift and insert the specified word, double, quad from rax or the contents of xmm0 into the specified xyz register at the specified position shifting data above it to the left towards higher order bytes.

62 L<Keep|/Keep> - Mark free registers so that they are not updated until we Free them or complain if the register is already in use.

63 L<KeepFree|/KeepFree> - Free registers so that they can be reused

64 L<KeepPop|/KeepPop> - Reset the status of the specified registers to the status quo ante the last push

65 L<KeepPush|/KeepPush> - Push the current status of the specified registers and then mark them as free

66 L<KeepReturn|/KeepReturn> - Pop the specified register and mark it as in use to effect a subroutine return with this register.

67 L<KeepSet|/KeepSet> - Confirm that the specified registers are in use

68 L<Label|/Label> - Create a unique label

69 L<Link|/Link> - Libraries to link with

70 L<LoadShortStringFromMemoryToZmm|/LoadShortStringFromMemoryToZmm> - Load the short string addressed by rax into the zmm register with the specified number

71 L<LoadShortStringFromMemoryToZmm2|/LoadShortStringFromMemoryToZmm2> - Load the short string addressed by rax into the zmm register with the specified number

72 L<LoadTargetZmmFromSourceZmm|/LoadTargetZmmFromSourceZmm> - Load bytes into the numbered target zmm register at a register specified offset with source bytes from a numbered source zmm register at a specified register offset for a specified register length.

73 L<LoadZmmFromMemory|/LoadZmmFromMemory> - Load bytes into the numbered target zmm register at a register specified offset with source bytes from memory addressed by a specified register for a specified register length from memory addressed by a specified register.

74 L<LocalData|/LocalData> - Map local data

75 L<LocateIntelEmulator|/LocateIntelEmulator> - Locate the Intel Software Development Emulator

76 L<Macro|/Macro> - Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub

77 L<MaximumOfTwoRegisters|/MaximumOfTwoRegisters> - Return in the specified register the value in the second register if it is greater than the value in the first register

78 L<MinimumOfTwoRegisters|/MinimumOfTwoRegisters> - Return in the specified register the value in the second register if it is less than the value in the first register

79 L<Minus|/Minus> - Subtract the third operand from the second operand and place the result in the first operand

80 L<Nasm::X86::BlockArray::address|/Nasm::X86::BlockArray::address> - Address of a block string

81 L<Nasm::X86::BlockArray::allocBlock|/Nasm::X86::BlockArray::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

82 L<Nasm::X86::BlockArray::dump|/Nasm::X86::BlockArray::dump> - Dump a block array

83 L<Nasm::X86::BlockArray::get|/Nasm::X86::BlockArray::get> - Get an element from the array

84 L<Nasm::X86::BlockArray::pop|/Nasm::X86::BlockArray::pop> - Pop an element from an array

85 L<Nasm::X86::BlockArray::push|/Nasm::X86::BlockArray::push> - Push an element onto the array

86 L<Nasm::X86::BlockArray::put|/Nasm::X86::BlockArray::put> - Put an element into an array as long as it is with in its limits established by pushing.

87 L<Nasm::X86::BlockString::address|/Nasm::X86::BlockString::address> - Address of a block string

88 L<Nasm::X86::BlockString::allocBlock|/Nasm::X86::BlockString::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

89 L<Nasm::X86::BlockString::append|/Nasm::X86::BlockString::append> - Append the specified content in memory to the specified block string

90 L<Nasm::X86::BlockString::clear|/Nasm::X86::BlockString::clear> - Clear the block by freeing all but the first block

91 L<Nasm::X86::BlockString::concatenate|/Nasm::X86::BlockString::concatenate> - Concatenate two block strings by appending a copy of the source to the target block string.

92 L<Nasm::X86::BlockString::deleteChar|/Nasm::X86::BlockString::deleteChar> - Delete a character in a block string

93 L<Nasm::X86::BlockString::dump|/Nasm::X86::BlockString::dump> - Dump a block string to sysout

94 L<Nasm::X86::BlockString::getBlock|/Nasm::X86::BlockString::getBlock> - Get the block with the specified offset in the specified block string and return it in the numbered zmm

95 L<Nasm::X86::BlockString::getBlockLengthInZmm|/Nasm::X86::BlockString::getBlockLengthInZmm> - Get the block length of the numbered zmm and return it in a variable

96 L<Nasm::X86::BlockString::getCharacter|/Nasm::X86::BlockString::getCharacter> - Get a character from a block string

97 L<Nasm::X86::BlockString::getNextAndPrevBlockOffsetFromZmm|/Nasm::X86::BlockString::getNextAndPrevBlockOffsetFromZmm> - Get the offsets of the next and previous blocks as variables from the specified zmm

98 L<Nasm::X86::BlockString::insertChar|/Nasm::X86::BlockString::insertChar> - Insert a character into a block string

99 L<Nasm::X86::BlockString::len|/Nasm::X86::BlockString::len> - Find the length of a block string

100 L<Nasm::X86::BlockString::putBlock|/Nasm::X86::BlockString::putBlock> - Write the numbered zmm to the block at the specified offset in the specified byte string

101 L<Nasm::X86::BlockString::putNextandPrevBlockOffsetIntoZmm|/Nasm::X86::BlockString::putNextandPrevBlockOffsetIntoZmm> - Save next and prev offsets into a zmm representing a block

102 L<Nasm::X86::BlockString::setBlockLengthInZmm|/Nasm::X86::BlockString::setBlockLengthInZmm> - Set the block length of the numbered zmm to the specified length

103 L<Nasm::X86::ByteString::allocate|/Nasm::X86::ByteString::allocate> - Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi

104 L<Nasm::X86::ByteString::allocBlock|/Nasm::X86::ByteString::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

105 L<Nasm::X86::ByteString::append|/Nasm::X86::ByteString::append> - Append one byte string to another

106 L<Nasm::X86::ByteString::blockSize|/Nasm::X86::ByteString::blockSize> - Size of a block

107 L<Nasm::X86::ByteString::char|/Nasm::X86::ByteString::char> - Append a character expressed as a decimal number to the byte string addressed by rax

108 L<Nasm::X86::ByteString::clear|/Nasm::X86::ByteString::clear> - Clear the byte string addressed by rax

109 L<Nasm::X86::ByteString::CreateBlockArray|/Nasm::X86::ByteString::CreateBlockArray> - Create a block array in a byte string

110 L<Nasm::X86::ByteString::CreateBlockString|/Nasm::X86::ByteString::CreateBlockString> - Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the byte string addressed by rax and return its descriptor

111 L<Nasm::X86::ByteString::dump|/Nasm::X86::ByteString::dump> - Dump details of a byte string

112 L<Nasm::X86::ByteString::firstFreeBlock|/Nasm::X86::ByteString::firstFreeBlock> - Create and load a variable with the first free block on the free block chain or zero if no such block in the given byte string

113 L<Nasm::X86::ByteString::freeBlock|/Nasm::X86::ByteString::freeBlock> - Free a block in a byte string by placing it on the free chain

114 L<Nasm::X86::ByteString::getBlock|/Nasm::X86::ByteString::getBlock> - Get the block with the specified offset in the specified block string and return it in the numbered zmm

115 L<Nasm::X86::ByteString::length|/Nasm::X86::ByteString::length> - Get the length of a byte string

116 L<Nasm::X86::ByteString::m|/Nasm::X86::ByteString::m> - Append the content with length rdi addressed by rsi to the byte string addressed by rax

117 L<Nasm::X86::ByteString::makeReadOnly|/Nasm::X86::ByteString::makeReadOnly> - Make a byte string read only

118 L<Nasm::X86::ByteString::makeWriteable|/Nasm::X86::ByteString::makeWriteable> - Make a byte string writable

119 L<Nasm::X86::ByteString::nl|/Nasm::X86::ByteString::nl> - Append a new line to the byte string addressed by rax

120 L<Nasm::X86::ByteString::out|/Nasm::X86::ByteString::out> - Print the specified byte string addressed by rax on sysout

121 L<Nasm::X86::ByteString::putBlock|/Nasm::X86::ByteString::putBlock> - Write the numbered zmm to the block at the specified offset in the specified byte string

122 L<Nasm::X86::ByteString::q|/Nasm::X86::ByteString::q> - Append a constant string to the byte string

123 L<Nasm::X86::ByteString::ql|/Nasm::X86::ByteString::ql> - Append a quoted string containing new line characters to the byte string addressed by rax

124 L<Nasm::X86::ByteString::rdiInHex|/Nasm::X86::ByteString::rdiInHex> - Add the content of register rdi in hexadecimal in big endian notation to a byte string

125 L<Nasm::X86::ByteString::read|/Nasm::X86::ByteString::read> - Read the named file (terminated with a zero byte) and place it into the named byte string.

126 L<Nasm::X86::ByteString::setFirstFreeBlock|/Nasm::X86::ByteString::setFirstFreeBlock> - Set the first free block field from a variable

127 L<Nasm::X86::ByteString::updateSpace|/Nasm::X86::ByteString::updateSpace> - Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi

128 L<Nasm::X86::ByteString::write|/Nasm::X86::ByteString::write> - Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file

129 L<Nasm::X86::ByteString::z|/Nasm::X86::ByteString::z> - Append a trailing zero to the byte string addressed by rax

130 L<Nasm::X86::LocalData::allocate8|/Nasm::X86::LocalData::allocate8> - Add some 8 byte local variables and return an array of variable definitions

131 L<Nasm::X86::LocalData::free|/Nasm::X86::LocalData::free> - Free a local data area on the stack

132 L<Nasm::X86::LocalData::start|/Nasm::X86::LocalData::start> - Start a local data area on the stack

133 L<Nasm::X86::LocalData::variable|/Nasm::X86::LocalData::variable> - Add a local variable

134 L<Nasm::X86::LocalVariable::stack|/Nasm::X86::LocalVariable::stack> - Address a local variable on the stack

135 L<Nasm::X86::Scope::contains|/Nasm::X86::Scope::contains> - Check that the named parent scope contains the specified child scope.

136 L<Nasm::X86::Scope::currentlyVisible|/Nasm::X86::Scope::currentlyVisible> - Check that the named parent scope is currently visible

137 L<Nasm::X86::Structure::field|/Nasm::X86::Structure::field> - Add a field of the specified length with an optional comment

138 L<Nasm::X86::StructureField::addr|/Nasm::X86::StructureField::addr> - Address a field in a structure by either the default register or the named register

139 L<Nasm::X86::Sub::call|/Nasm::X86::Sub::call> - Call a sub passing it some parameters

140 L<Nasm::X86::Variable::add|/Nasm::X86::Variable::add> - Add the right hand variable to the left hand variable and return the result as a new variable

141 L<Nasm::X86::Variable::address|/Nasm::X86::Variable::address> - Get the address of a variable with an optional offset

142 L<Nasm::X86::Variable::and|/Nasm::X86::Variable::and> - And two variables

143 L<Nasm::X86::Variable::arithmetic|/Nasm::X86::Variable::arithmetic> - Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables

144 L<Nasm::X86::Variable::assign|/Nasm::X86::Variable::assign> - Assign to the left hand side the value of the right hand side

145 L<Nasm::X86::Variable::boolean|/Nasm::X86::Variable::boolean> - Combine the left hand variable with the right hand variable via a boolean operator

146 L<Nasm::X86::Variable::clearMemory|/Nasm::X86::Variable::clearMemory> - Clear the memory described in this variable

147 L<Nasm::X86::Variable::confirmIsMemory|/Nasm::X86::Variable::confirmIsMemory> - Check that variable describes allocated memory and optionally load registers with its length and size

148 L<Nasm::X86::Variable::copy|/Nasm::X86::Variable::copy> - Copy one variable into another

149 L<Nasm::X86::Variable::copyAddress|/Nasm::X86::Variable::copyAddress> - Copy a reference to a variable

150 L<Nasm::X86::Variable::copyMemoryFrom|/Nasm::X86::Variable::copyMemoryFrom> - Copy from one block of memory to another

151 L<Nasm::X86::Variable::copyRef|/Nasm::X86::Variable::copyRef> - Copy one variable into an referenced variable

152 L<Nasm::X86::Variable::debug|/Nasm::X86::Variable::debug> - Dump the value of a variable on stdout with an indication of where the dump came from

153 L<Nasm::X86::Variable::dec|/Nasm::X86::Variable::dec> - Decrement a variable

154 L<Nasm::X86::Variable::divide|/Nasm::X86::Variable::divide> - Divide the left hand variable by the right hand variable and return the result as a new variable

155 L<Nasm::X86::Variable::division|/Nasm::X86::Variable::division> - Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side

156 L<Nasm::X86::Variable::dump|/Nasm::X86::Variable::dump> - Dump the value of a variable to the specified channel adding an optional title and new line if requested

157 L<Nasm::X86::Variable::eq|/Nasm::X86::Variable::eq> - Check whether the left hand variable is equal to the right hand variable

158 L<Nasm::X86::Variable::equals|/Nasm::X86::Variable::equals> - Equals operator

159 L<Nasm::X86::Variable::err|/Nasm::X86::Variable::err> - Dump the value of a variable on stderr

160 L<Nasm::X86::Variable::errNL|/Nasm::X86::Variable::errNL> - Dump the value of a variable on stderr and append a new line

161 L<Nasm::X86::Variable::for|/Nasm::X86::Variable::for> - Iterate the body limit times.

162 L<Nasm::X86::Variable::freeMemory|/Nasm::X86::Variable::freeMemory> - Free the memory described in this variable

163 L<Nasm::X86::Variable::ge|/Nasm::X86::Variable::ge> - Check whether the left hand variable is greater than or equal to the right hand variable

164 L<Nasm::X86::Variable::getBFromZmm|/Nasm::X86::Variable::getBFromZmm> - Get the byte from the numbered zmm register and put it in a variable

165 L<Nasm::X86::Variable::getDFromZmm|/Nasm::X86::Variable::getDFromZmm> - Get the double word from the numbered zmm register and put it in a variable

166 L<Nasm::X86::Variable::getQFromZmm|/Nasm::X86::Variable::getQFromZmm> - Get the quad word from the numbered zmm register and put it in a variable

167 L<Nasm::X86::Variable::getReg|/Nasm::X86::Variable::getReg> - Load the variable from the named registers

168 L<Nasm::X86::Variable::getWFromZmm|/Nasm::X86::Variable::getWFromZmm> - Get the word from the numbered zmm register and put it in a variable

169 L<Nasm::X86::Variable::gt|/Nasm::X86::Variable::gt> - Check whether the left hand variable is greater than the right hand variable

170 L<Nasm::X86::Variable::inc|/Nasm::X86::Variable::inc> - Increment a variable

171 L<Nasm::X86::Variable::incDec|/Nasm::X86::Variable::incDec> - Increment or decrement a variable

172 L<Nasm::X86::Variable::isRef|/Nasm::X86::Variable::isRef> - Check whether the specified  variable is a reference to another variable

173 L<Nasm::X86::Variable::le|/Nasm::X86::Variable::le> - Check whether the left hand variable is less than or equal to the right hand variable

174 L<Nasm::X86::Variable::loadZmm|/Nasm::X86::Variable::loadZmm> - Load bytes from the memory addressed by the specified source variable into the numbered zmm register.

175 L<Nasm::X86::Variable::lt|/Nasm::X86::Variable::lt> - Check whether the left hand variable is less than the right hand variable

176 L<Nasm::X86::Variable::max|/Nasm::X86::Variable::max> - Maximum of two variables

177 L<Nasm::X86::Variable::min|/Nasm::X86::Variable::min> - Minimum of two variables

178 L<Nasm::X86::Variable::minusAssign|/Nasm::X86::Variable::minusAssign> - Implement minus and assign

179 L<Nasm::X86::Variable::mod|/Nasm::X86::Variable::mod> - Divide the left hand variable by the right hand variable and return the remainder as a new variable

180 L<Nasm::X86::Variable::ne|/Nasm::X86::Variable::ne> - Check whether the left hand variable is not equal to the right hand variable

181 L<Nasm::X86::Variable::or|/Nasm::X86::Variable::or> - Or two variables

182 L<Nasm::X86::Variable::out|/Nasm::X86::Variable::out> - Dump the value of a variable on stdout

183 L<Nasm::X86::Variable::outNL|/Nasm::X86::Variable::outNL> - Dump the value of a variable on stdout and append a new line

184 L<Nasm::X86::Variable::plusAssign|/Nasm::X86::Variable::plusAssign> - Implement plus and assign

185 L<Nasm::X86::Variable::print|/Nasm::X86::Variable::print> - Write the value of a variable on stdout

186 L<Nasm::X86::Variable::printOutMemoryInHex|/Nasm::X86::Variable::printOutMemoryInHex> - Print allocated memory in hex

187 L<Nasm::X86::Variable::putBIntoXmm|/Nasm::X86::Variable::putBIntoXmm> - Place the value of the content variable at the byte in the numbered xmm register

188 L<Nasm::X86::Variable::putBIntoZmm|/Nasm::X86::Variable::putBIntoZmm> - Place the value of the content variable at the byte in the numbered zmm register

189 L<Nasm::X86::Variable::putBwdqIntoMm|/Nasm::X86::Variable::putBwdqIntoMm> - Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register

190 L<Nasm::X86::Variable::putDIntoXmm|/Nasm::X86::Variable::putDIntoXmm> - Place the value of the content variable at the double word in the numbered xmm register

191 L<Nasm::X86::Variable::putDIntoZmm|/Nasm::X86::Variable::putDIntoZmm> - Place the value of the content variable at the double word in the numbered zmm register

192 L<Nasm::X86::Variable::putQIntoXmm|/Nasm::X86::Variable::putQIntoXmm> - Place the value of the content variable at the quad word in the numbered xmm register

193 L<Nasm::X86::Variable::putQIntoZmm|/Nasm::X86::Variable::putQIntoZmm> - Place the value of the content variable at the quad word in the numbered zmm register

194 L<Nasm::X86::Variable::putWIntoXmm|/Nasm::X86::Variable::putWIntoXmm> - Place the value of the content variable at the word in the numbered xmm register

195 L<Nasm::X86::Variable::putWIntoZmm|/Nasm::X86::Variable::putWIntoZmm> - Place the value of the content variable at the word in the numbered zmm register

196 L<Nasm::X86::Variable::saveZmm|/Nasm::X86::Variable::saveZmm> - Save bytes into the memory addressed by the target variable from the numbered zmm register.

197 L<Nasm::X86::Variable::setMask|/Nasm::X86::Variable::setMask> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

198 L<Nasm::X86::Variable::setReg|/Nasm::X86::Variable::setReg> - Set the named registers from the content of the variable

199 L<Nasm::X86::Variable::setZmm|/Nasm::X86::Variable::setZmm> - Load bytes from the memory addressed by specified source variable into the numbered zmm register at the offset in the specified offset moving the number of bytes in the specified variable

200 L<Nasm::X86::Variable::str|/Nasm::X86::Variable::str> - The name of the variable

201 L<Nasm::X86::Variable::sub|/Nasm::X86::Variable::sub> - Subtract the right hand variable from the left hand variable and return the result as a new variable

202 L<Nasm::X86::Variable::times|/Nasm::X86::Variable::times> - Multiply the left hand variable by the right hand variable and return the result as a new variable

203 L<OpenRead|/OpenRead> - Open a file, whose name is addressed by rax, for read and return the file descriptor in rax

204 L<OpenWrite|/OpenWrite> - Create the file named by the terminated string addressed by rax for write

205 L<PeekR|/PeekR> - Peek at register on stack

206 L<Plus|/Plus> - Add the last operands and place the result in the first operand

207 L<PopR|/PopR> - Pop registers from the stack

208 L<PopRR|/PopRR> - Pop registers from the stack without tracking

209 L<PrintErrMemory|/PrintErrMemory> - Print the memory addressed by rax for a length of rdi on stderr

210 L<PrintErrMemoryInHex|/PrintErrMemoryInHex> - Dump memory from the address in rax for the length in rdi on stderr

211 L<PrintErrMemoryInHexNL|/PrintErrMemoryInHexNL> - Dump memory from the address in rax for the length in rdi and then print a new line

212 L<PrintErrMemoryNL|/PrintErrMemoryNL> - Print the memory addressed by rax for a length of rdi followed by a new line on stderr

213 L<PrintErrNL|/PrintErrNL> - Print a new line to stderr

214 L<PrintErrRaxInHex|/PrintErrRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to stderr

215 L<PrintErrRegisterInHex|/PrintErrRegisterInHex> - Print the named registers as hex strings on stderr

216 L<PrintErrString|/PrintErrString> - Print a constant string to stderr.

217 L<PrintErrStringNL|/PrintErrStringNL> - Print a constant string followed by a new line to stderr

218 L<PrintMemory|/PrintMemory> - Print the memory addressed by rax for a length of rdi on the specified channel

219 L<PrintMemoryInHex|/PrintMemoryInHex> - Dump memory from the address in rax for the length in rdi on the specified channel

220 L<PrintNL|/PrintNL> - Print a new line to stdout  or stderr

221 L<PrintOutMemory|/PrintOutMemory> - Print the memory addressed by rax for a length of rdi on stdout

222 L<PrintOutMemoryInHex|/PrintOutMemoryInHex> - Dump memory from the address in rax for the length in rdi on stdout

223 L<PrintOutMemoryInHexNL|/PrintOutMemoryInHexNL> - Dump memory from the address in rax for the length in rdi and then print a new line

224 L<PrintOutMemoryNL|/PrintOutMemoryNL> - Print the memory addressed by rax for a length of rdi followed by a new line on stdout

225 L<PrintOutNL|/PrintOutNL> - Print a new line to stderr

226 L<PrintOutRaxInHex|/PrintOutRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to stderr

227 L<PrintOutRaxInReverseInHex|/PrintOutRaxInReverseInHex> - Write the content of register rax to stderr in hexadecimal in little endian notation

228 L<PrintOutRegisterInHex|/PrintOutRegisterInHex> - Print the named registers as hex strings on stdout

229 L<PrintOutRegistersInHex|/PrintOutRegistersInHex> - Print the general purpose registers in hex

230 L<PrintOutRflagsInHex|/PrintOutRflagsInHex> - Print the flags register in hex

231 L<PrintOutRipInHex|/PrintOutRipInHex> - Print the instruction pointer in hex

232 L<PrintOutString|/PrintOutString> - Print a constant string to stdout.

233 L<PrintOutStringNL|/PrintOutStringNL> - Print a constant string followed by a new line to stdout

234 L<PrintOutZF|/PrintOutZF> - Print the zero flag without disturbing it

235 L<PrintRaxInHex|/PrintRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to the specified channel

236 L<PrintRegisterInHex|/PrintRegisterInHex> - Print the named registers as hex strings

237 L<PrintString|/PrintString> - Print a constant string to the specified channel

238 L<PushR|/PushR> - Push registers onto the stack

239 L<PushRR|/PushRR> - Push registers onto the stack without tracking

240 L<Rb|/Rb> - Layout bytes in the data segment and return their label

241 L<Rbwdq|/Rbwdq> - Layout data

242 L<RComment|/RComment> - Insert a comment into the read only data segment

243 L<Rd|/Rd> - Layout double words in the data segment and return their label

244 L<ReadFile|/ReadFile> - Read a file whose name is addressed by rax into memory.

245 L<ReadTimeStampCounter|/ReadTimeStampCounter> - Read the time stamp counter and return the time in nanoseconds in rax

246 L<RegisterSize|/RegisterSize> - Return the size of a register

247 L<removeNonAsciiChars|/removeNonAsciiChars> - Return a copy of the specified string with all the non ascii characters removed

248 L<ReorderSyscallRegisters|/ReorderSyscallRegisters> - Map the list of registers provided to the 64 bit system call sequence

249 L<ReorderXmmRegisters|/ReorderXmmRegisters> - Map the list of xmm registers provided to 0-31

250 L<RestoreFirstFour|/RestoreFirstFour> - Restore the first 4 parameter registers

251 L<RestoreFirstFourExceptRax|/RestoreFirstFourExceptRax> - Restore the first 4 parameter registers except rax so it can return its value

252 L<RestoreFirstFourExceptRaxAndRdi|/RestoreFirstFourExceptRaxAndRdi> - Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values

253 L<RestoreFirstSeven|/RestoreFirstSeven> - Restore the first 7 parameter registers

254 L<RestoreFirstSevenExceptRax|/RestoreFirstSevenExceptRax> - Restore the first 7 parameter registers except rax which is being used to return the result

255 L<RestoreFirstSevenExceptRaxAndRdi|/RestoreFirstSevenExceptRaxAndRdi> - Restore the first 7 parameter registers except rax and rdi which are being used to return the results

256 L<Rq|/Rq> - Layout quad words in the data segment and return their label

257 L<Rs|/Rs> - Layout bytes in read only memory and return their label

258 L<Rw|/Rw> - Layout words in the data segment and return their label

259 L<SaveFirstFour|/SaveFirstFour> - Save the first 4 parameter registers making any parameter registers read only

260 L<SaveFirstSeven|/SaveFirstSeven> - Save the first 7 parameter registers

261 L<Scope|/Scope> - Create and stack a new scope and continue with it as the current scope

262 L<ScopeEnd|/ScopeEnd> - End the current scope and continue with the containing parent scope

263 L<SetLabel|/SetLabel> - Set a label in the code section

264 L<SetLengthOfShortString|/SetLengthOfShortString> - Set the length of the short string held in the numbered zmm register into the specified register

265 L<SetMaskRegister|/SetMaskRegister> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

266 L<SetRegisterToMinusOne|/SetRegisterToMinusOne> - Set the specified register to -1

267 L<SetZF|/SetZF> - Set the zero flag

268 L<Start|/Start> - Initialize the assembler

269 L<StatSize|/StatSize> - Stat a file whose name is addressed by rax to get its size in rax

270 L<Structure|/Structure> - Create a structure addressed by a register

271 L<Subroutine|/Subroutine> - Create a subroutine that can be called in assembler code

272 L<totalBytesAssembled|/totalBytesAssembled> - Total size in bytes of all files assembled during testing

273 L<unlinkFile|/unlinkFile> - Unlink the named file

274 L<UnReorderSyscallRegisters|/UnReorderSyscallRegisters> - Recover the initial values in registers that were reordered

275 L<UnReorderXmmRegisters|/UnReorderXmmRegisters> - Recover the initial values in the xmm registers that were reordered

276 L<Variable|/Variable> - Create a new variable with the specified size and name initialized via an expression

277 L<Vb|/Vb> - Define a byte variable

278 L<Vd|/Vd> - Define a double word variable

279 L<Vq|/Vq> - Define a quad variable

280 L<Vr|/Vr> - Define a reference variable

281 L<Vw|/Vw> - Define a word variable

282 L<Vx|/Vx> - Define an xmm variable

283 L<VxyzInit|/VxyzInit> - Initialize an xyz register from general purpose registers

284 L<Vy|/Vy> - Define an ymm variable

285 L<Vz|/Vz> - Define an zmm variable

286 L<WaitPid|/WaitPid> - Wait for the pid in rax to complete

=head1 Installation

This module is written in 100% Pure Perl and, thus, it is easy to read,
comprehend, use, modify and install via B<cpan>:

  sudo cpan install Nasm::X86

=head1 Author

L<philiprbrenan@gmail.com|mailto:philiprbrenan@gmail.com>

L<http://www.appaapps.com|http://www.appaapps.com>

=head1 Copyright

Copyright (c) 2016-2021 Philip R Brenan.

This module is free software. It may be used, redistributed and/or modified
under the same terms as Perl itself.

=cut



# Tests and documentation

sub test
 {my $p = __PACKAGE__;
  binmode($_, ":utf8") for *STDOUT, *STDERR;
  return if eval "eof(${p}::DATA)";
  my $s = eval "join('', <${p}::DATA>)";
  $@ and die $@;
  eval $s;
  $@ and die $@;
  1
 }

test unless caller;

1;
# podDocumentation
__DATA__
use Time::HiRes qw(time);
use Test::Most;

bail_on_fail;

my $develop   = -e q(/home/phil/);                                              # Developing
my $localTest = ((caller(1))[0]//'Nasm::X86') eq "Nasm::X86";                   # Local testing mode

Test::More->builder->output("/dev/null") if $localTest;                         # Reduce number of confirmation messages during testing

if ($^O =~ m(bsd|linux|cygwin)i)                                                # Supported systems
 {if (confirmHasCommandLineCommand(q(nasm)) and LocateIntelEmulator)            # Network assembler and Intel Software Development emulator
   {plan tests => 109;
   }
  else
   {plan skip_all => qq(Nasm or Intel 64 emulator not available);
   }
 }
else
 {plan skip_all => qq(Not supported on: $^O);
 }

my $start = time;                                                               # Tests

eval {goto latest} if !caller(0) and -e "/home/phil";                           # Go to latest test if specified

if (1) {                                                                        #TPrintOutStringNL #TPrintErrStringNL #TAssemble
  PrintOutStringNL "Hello World";
  PrintOutStringNL "Hello\nWorld";
  PrintErrStringNL "Hello World";

  ok Assemble(debug => 0, eq => <<END);
Hello World
Hello
World
END
 }

if (1) {                                                                        #TMov #TComment #TRs #TPrintOutMemory
  Comment "Print a string from memory";
  my $s = "Hello World";
  Mov rax, Rs($s);
  Mov rdi, length $s;
  PrintOutMemory;

  ok Assemble =~ m(Hello World);
 }

if (1) {                                                                        #TPrintOutRaxInHex #TPrintOutNL
  my $q = Rs('abababab');
  Mov(rax, "[$q]");
  PrintOutString "rax: ";
  PrintOutRaxInHex;
  PrintOutNL;
  Xor rax, rax;
  PrintOutString "rax: ";
  PrintOutRaxInHex;
  PrintOutNL;

  ok Assemble =~ m(rax: 6261 6261 6261 6261.*rax: 0000 0000 0000 0000)s;
 }

if (1) {                                                                        #TPrintOutRegistersInHex #TRs
  my $q = Rs('abababab');
  Mov(rax, 1);
  Mov(rbx, 2);
  Mov(rcx, 3);
  Mov(rdx, 4);
  Mov(r8,  5);
  Lea r9,  "[rax+rbx]";
  PrintOutRegistersInHex;

  my $r = Assemble;
  ok $r =~ m( r8: 0000 0000 0000 0005.* r9: 0000 0000 0000 0003.*rax: 0000 0000 0000 0001)s;
  ok $r =~ m(rbx: 0000 0000 0000 0002.*rcx: 0000 0000 0000 0003.*rdx: 0000 0000 0000 0004)s;
 }

if (1) {                                                                        #TDs
  my $q = Rs('a'..'z');
  Mov rax, Ds('0'x64);                                                          # Output area
  Vmovdqu32(xmm0, "[$q]");                                                      # Load
  Vprolq   (xmm0,   xmm0, 32);                                                  # Rotate double words in quad words
  Vmovdqu32("[rax]", xmm0);                                                     # Save
  Mov rdi, 16;
  PrintOutMemory;

  ok Assemble =~ m(efghabcdmnopijkl)s;
 }

if (1) {
  my $q = Rs(('a'..'p')x2);
  Mov rax, Ds('0'x64);
  Vmovdqu32(ymm0, "[$q]");
  Vprolq   (ymm0,   ymm0, 32);
  Vmovdqu32("[rax]", ymm0);
  Mov rdi, 32;
  PrintOutMemory;

  ok Assemble =~ m(efghabcdmnopijklefghabcdmnopijkl)s;
 }

if (1) {
  my $q = Rs my $s = join '', ('a'..'p')x4;                                     # Sample string
  Mov rax, Ds('0'x128);

  Vmovdqu64 zmm0, "[$q]";                                                       # Load zmm0 with sample string
  Vprolq    zmm1, zmm0, 32;                                                     # Rotate left 32 bits in lanes
  Vmovdqu64 "[rax]", zmm1;                                                      # Save results

  Mov rdi, length $s;                                                           # Print results
  PrintOutMemoryNL;

  is_deeply "$s\n", <<END;                                                      # Initial string
abcdefghijklmnopabcdefghijklmnopabcdefghijklmnopabcdefghijklmnop
END

  is_deeply Assemble, <<END;                                                    # Assemble and run
efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl
END
 }

if (1) {                                                                        #TPrintOutRegisterInHex
  my $q = Rs(('a'..'p')x4);
  Mov r8,"[$q]";
  PrintOutRegisterInHex r8;

  ok Assemble =~ m(r8: 6867 6665 6463 6261)s;
 }

if (1) {
  my $q = Rs('a'..'p');
  Vmovdqu8 xmm0, "[$q]";
  PrintOutRegisterInHex xmm0;

  ok Assemble =~ m(xmm0: 706F 6E6D 6C6B 6A69   6867 6665 6463 6261)s;
 }

if (1) {
  my $q = Rs('a'..'p', 'A'..'P', );
  Vmovdqu8 ymm0, "[$q]";
  PrintOutRegisterInHex ymm0;

  ok Assemble =~ m(ymm0: 504F 4E4D 4C4B 4A49   4847 4645 4443 4241   706F 6E6D 6C6B 6A69   6867 6665 6463 6261)s;
 }

if (1) {
  my $q = Rs(('a'..'p', 'A'..'P') x 2);
  Vmovdqu8 zmm0, "[$q]";
  PrintOutRegisterInHex zmm0;

  ok Assemble =~ m(zmm0: 504F 4E4D 4C4B 4A49   4847 4645 4443 4241   706F 6E6D 6C6B 6A69   6867 6665 6463 6261   504F 4E4D 4C4B 4A49   4847 4645 4443 4241   706F 6E6D 6C6B 6A69   6867 6665 6463 6261)s;
 }

if (1) {                                                                        #TAllocateMemory #TNasm::X86::Variable::freeMemory
  my $N = Vq(size, 2048);
  my $q = Rs('a'..'p');
  AllocateMemory($N, my $address = Vq(address));

  Vmovdqu8 xmm0, "[$q]";
  $address->setReg(rax);
  Vmovdqu8 "[rax]", xmm0;
  Mov rdi, 16;
  PrintOutMemory;
  PrintOutNL;

  FreeMemory(address => $address, size=> $N);

  ok Assemble(eq => <<END);
abcdefghijklmnop
END
 }

if (1) {                                                                        #TReadTimeStampCounter
  for(1..10)
   {ReadTimeStampCounter;
    PrintOutRegisterInHex rax;
   }

  my @s = split /\n/, Assemble;
  my @S = sort @s;
  is_deeply \@s, \@S;
 }

if (1) {                                                                        #TIf
  Mov rax, 0;
  Test rax,rax;
  IfNz
   {PrintOutRegisterInHex rax;
   } sub
   {PrintOutRegisterInHex rbx;
   };
  KeepFree rax;
  Mov rax, 1;
  Test rax,rax;
  IfNz
   {PrintOutRegisterInHex rcx;
   } sub
   {PrintOutRegisterInHex rdx;
   };

  ok Assemble =~ m(rbx.*rcx)s;
 }

if (1) {                                                                        #TFork #TGetPid #TGetPPid #TWaitPid
  Fork;                                                                         # Fork

  Test rax,rax;
  IfNz                                                                          # Parent
   {Mov rbx, rax;
    WaitPid;
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;
    KeepFree rax;
    GetPid;                                                                     # Pid of parent as seen in parent
    Mov rcx,rax;
    PrintOutRegisterInHex rcx;
   }
  sub                                                                           # Child
   {Mov r8,rax;
    PrintOutRegisterInHex r8;
    KeepFree rax;
    GetPid;                                                                     # Child pid as seen in child
    Mov r9,rax;
    PrintOutRegisterInHex r9;
    KeepFree rax;
    GetPPid;                                                                    # Parent pid as seen in child
    Mov r10,rax;
    PrintOutRegisterInHex r10;
   };

  my $r = Assemble;

#    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
#    r9: 0000 0000 0003 0C63   #2 Pid of child
#   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
#   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
#   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
#   rcx: 0000 0000 0003 0C60   #6 Pid of parent

  if ($r =~ m(r8:( 0000){4}.*r9:(.*)\s{5,}r10:(.*)\s{5,}rax:(.*)\s{5,}rbx:(.*)\s{5,}rcx:(.*)\s{2,})s)
   {ok $2 eq $4;
    ok $2 eq $5;
    ok $3 eq $6;
    ok $2 gt $6;
   }
 }

if (1) {                                                                        #TGetUid
  GetUid;                                                                       # Userid
  PrintOutRegisterInHex rax;

  my $r = Assemble;
  ok $r =~ m(rax:( 0000){3});
 }

if (1) {                                                                        #TStatSize
  Mov rax, Rs($0);                                                              # File to stat
  StatSize;                                                                     # Stat the file
  PrintOutRegisterInHex rax;

  my $r = Assemble =~ s( ) ()gsr;
  if ($r =~ m(rax:([0-9a-f]{16}))is)                                            # Compare file size obtained with that from fileSize()
   {is_deeply $1, sprintf("%016X", fileSize($0));
   }
 }

if (1) {                                                                        #TOpenRead #TCloseFile #TOpenWrite
  Mov rax, Rs($0);                                                              # File to read
  OpenRead;                                                                     # Open file
  PrintOutRegisterInHex rax;
  CloseFile;                                                                    # Close file
  PrintOutRegisterInHex rax;
  KeepFree rax, rdi;

  Mov rax, Rs(my $f = "zzzTemporaryFile.txt");                                  # File to write
  OpenWrite;                                                                    # Open file
  CloseFile;                                                                    # Close file

  is_deeply Assemble, <<END;
   rax: 0000 0000 0000 0003
   rax: 0000 0000 0000 0000
END
  ok -e $f;                                                                     # Created file
  unlink $f;
 }

if (1) {                                                                        #TFor
  For
   {PrintOutRegisterInHex rax
   } rax, 16, 1;

  my $r = Assemble;
  ok $r =~ m(( 0000){3} 0000)i;
  ok $r =~ m(( 0000){3} 000F)i;
 }

if (1) {                                                                        #TPrintOutRaxInReverseInHex #TPrintOutMemoryInHex
  Mov rax, 0x07654321;
  Shl rax, 32;
  Or  rax, 0x07654321;
  PushR rax;

  PrintOutRaxInHex;
  PrintOutNL;
  PrintOutRaxInReverseInHex;
  PrintOutNL;
  KeepFree rax;

  Mov rax, rsp;
  Mov rdi, 8;
  PrintOutMemoryInHex;
  PrintOutNL;
  PopR rax;
  KeepFree rax, rdi;

  Mov rax, 4096;
  PushR rax;
  Mov rax, rsp;
  Mov rdi, 8;
  PrintOutMemoryInHex;
  PrintOutNL;
  PopR rax;

  is_deeply Assemble, <<END;
0765 4321 0765 4321
2143 6507 2143 6507
2143 6507 2143 6507
0010 0000 0000 0000
END
 }

if (1) {                                                                        #TPushR #TPopR
  Mov rax, 0x11111111;
  Mov rbx, 0x22222222;
  PushR my @save = (rax, rbx);
  Mov rax, 0x33333333;
  PopR @save;
  PrintOutRegisterInHex rax;
  PrintOutRegisterInHex rbx;

  is_deeply Assemble,<<END;
   rax: 0000 0000 1111 1111
   rbx: 0000 0000 2222 2222
END
 }

if (1) {                                                                        #TAllocateMemory #TFreeMemory #TClearMemory
  my $N = Vq(size, 4096);                                                       # Size of the initial allocation which should be one or more pages

  AllocateMemory($N, my $A = Vq(address));

  ClearMemory($N, $A);

  $A->setReg(rax);
  $N->setReg(rdi);
  PrintOutMemoryInHexNL;

  FreeMemory($N, $A);

  ok Assemble(eq => <<END);
0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

if (1) {                                                                        #TCall #TS
  Mov rax, 0x44332211;
  PrintOutRegisterInHex rax;

  my $s = Macro
   {PrintOutRegisterInHex rax;
    Inc rax;
    PrintOutRegisterInHex rax;
   };

  Call $s;

  PrintOutRegisterInHex rax;

  my $r = Assemble;
  ok $r =~ m(0000 0000 4433 2211.*2211.*2212.*0000 0000 4433 2212)s;
 }

if (1) {                                                                        #TReadFile #TPrintMemory
  ReadFile(Vq(file, Rs($0)), (my $s = Vq(size)), my $a = Vq(address));          # Read file
  $a->setReg(rax);                                                              # Address of file in memory
  $s->setReg(rdi);                                                              # Length  of file in memory
  PrintOutMemory;                                                               # Print contents of memory to stdout

  my $r = Assemble;                                                             # Assemble and execute
  ok stringMd5Sum($r) eq fileMd5Sum($0);                                          # Output contains this file
 }

if (1) {                                                                        #TCreateByteString #TByteString::clear #TByteString::out #TByteString::copy #TByteString::nl
  my $a = CreateByteString;                                                     # Create a string
  $a->q('aa');
  $a->out;
  PrintOutNL;
  is_deeply Assemble, <<END;                                                    # Assemble and execute
aa
END
 }

if (1) {                                                                        #TCreateByteString #TByteString::clear #TByteString::out #TByteString::copy #TByteString::nl
  my $a = CreateByteString;                                                     # Create a string
  my $b = CreateByteString;                                                     # Create a string
  $a->q('aa');
  $b->q('bb');
  $a->out;
  PrintOutNL;
  $b->out;
  PrintOutNL;
  is_deeply Assemble, <<END;                                                    # Assemble and execute
aa
bb
END
 }

if (1) {                                                                        #TCreateByteString #TByteString::clear #TByteString::out #TByteString::copy #TByteString::nl
  my $a = CreateByteString;                                                     # Create a string
  my $b = CreateByteString;                                                     # Create a string
  $a->q('aa');
  $a->q('AA');
  $a->out;
  PrintOutNL;
  is_deeply Assemble, <<END;                                                    # Assemble and execute
aaAA
END
 }

if (1) {                                                                        #TCreateByteString #TByteString::clear #TByteString::out #TByteString::copy #TByteString::nl
  my $a = CreateByteString;                                                     # Create a string
  my $b = CreateByteString;                                                     # Create a string
  $a->q('aa');
  $b->q('bb');
  $a->q('AA');
  $b->q('BB');
  $a->q('aa');
  $b->q('bb');
  $a->out;
  $b->out;
  PrintOutNL;
  is_deeply Assemble, <<END;                                                    # Assemble and execute
aaAAaabbBBbb
END
 }

if (1) {                                                                        #TCreateByteString #TByteString::clear #TByteString::out #TByteString::copy #TByteString::nl
  my $a = CreateByteString;                                                     # Create a string
  $a->q('ab');
  my $b = CreateByteString;                                                     # Create target byte string
  $a->bs(r15);
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);
  $a->append(source=>$b->bs);
  $b->append(source=>$a->bs);
  $a->append(source=>$b->bs);
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);


  $a->out;   PrintOutNL;                                                        # Print byte string
  $b->out;   PrintOutNL;                                                        # Print byte string
  $a->length(my $sa = Vq(size)); $sa->outNL;
  $b->length(my $sb = Vq(size)); $sb->outNL;
  $a->clear;
  $a->length(my $sA = Vq(size)); $sA->outNL;
  $b->length(my $sB = Vq(size)); $sB->outNL;

  is_deeply Assemble, <<END;                                                    # Assemble and execute
abababababababab
ababababababababababababababababababababababababababababababababababababab
size: 0000 0000 0000 0010
size: 0000 0000 0000 004A
size: 0000 0000 0000 0000
size: 0000 0000 0000 004A
END
 }

if (1) {                                                                        #TReorderSyscallRegisters #TUnReorderSyscallRegisters
  Mov rax, 1;  Mov rdi, 2;  Mov rsi,  3;  Mov rdx,  4;
  Mov r8,  8;  Mov r9,  9;  Mov r10, 10;  Mov r11, 11;

  ReorderSyscallRegisters   r8,r9;                                              # Reorder the registers for syscall
  PrintOutRegisterInHex rax;
  PrintOutRegisterInHex rdi;

  UnReorderSyscallRegisters r8,r9;                                              # Unreorder the registers to recover their original values
  PrintOutRegisterInHex rax;
  PrintOutRegisterInHex rdi;

  ok Assemble =~ m(rax:.*08.*rdi:.*9.*rax:.*1.*rdi:.*2.*)s;
 }

if (1) {                                                                        # Mask register instructions #TClearRegisters
  Mov rax,1;
  Kmovq k0,  rax;
  Kaddb k0,  k0, k0;
  Kaddb k0,  k0, k0;
  Kaddb k0,  k0, k0;
  Kmovq rax, k0;
  PushR k0;
  ClearRegisters k0;
  Kmovq k1, k0;
  PopR  k0;
  PrintOutRegisterInHex k0;
  PrintOutRegisterInHex k1;

  ok Assemble =~ m(k0: 0000 0000 0000 0008.*k1: 0000 0000 0000 0000)s;
 }

if (1) {                                                                        # Count leading zeros
  Mov   rax, 8;                                                                 # Append a constant to the byte string
  Lzcnt rax, rax;                                                               # New line
  PrintOutRegisterInHex rax;
  KeepFree rax;

  Mov   rax, 8;                                                                 # Append a constant to the byte string
  Tzcnt rax, rax;                                                               # New line
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: 0000 0000 0000 003C.*rax: 0000 0000 0000 0003)s;
 }

if (1) {                                                                        #TByteString::nl
  my $s = CreateByteString;
  $s->q("A");
  $s->nl;
  $s->q("B");
  $s->out;
  PrintOutNL;

  is_deeply Assemble, <<END;
A
B
END
 }

if (1) {                                                                        # Print this file  #TByteString::read #TByteString::z #TByteString::q
  my $s = CreateByteString;                                                     # Create a string
  $s->read(Vq(file, Rs($0)));
  $s->out;

  my $r = Assemble;
  is_deeply stringMd5Sum($r), fileMd5Sum($0);                                   # Output contains this file
 }

if (0) {                                                                        # Print rdi in hex into a byte string #TByteString::rdiInHex
  my $s = CreateByteString;                                                     # Create a string
  Mov rdi, 0x88776655;
  Shl rdi, 32;
  Or  rdi, 0x44332211;

  $s->rdiInHex;                                                                 # Append a constant to the byte string
  $s->out;

  ok Assemble =~ m(8877665544332211);
 }

if (1) {                                                                        # Print rdi in hex into a byte string #TGetPidInHex
  GetPidInHex;
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: 00);
 }

if (0) {                                                                        # Write a hex string to a temporary file
  my $s = CreateByteString;                                                     # Create a string
  Mov rdi, 0x88776655;                                                          # Write into string
  Shl rdi, 32;
  Or  rdi, 0x44332211;
  $s->rdiInHex;                                                                 # Append a constant to the byte string
  $s->write;                                                                    # Write the byte string to a temporary file
  $s->out;                                                                      # Write the name of the temporary file

  ok Assemble =~ m(tmp);
 }

if (1) {                                                                        # Execute the content of a byte string #TexecuteFileViaBash #TByteString::write #TByteString::out #TunlinkFile #TByteString::ql
  my $s = CreateByteString;                                                     # Create a string
  $s->ql(<<END);                                                                # Write code to execute
#!/usr/bin/bash
whoami
ls -la
pwd
END
  $s->write         (my $f = Vq('file', Rs("zzz.sh")));                         # Write code to a file
  executeFileViaBash($f);                                                       # Execute the file
  unlinkFile        ($f);                                                       # Delete the file

  my $u = qx(whoami); chomp($u);
  ok Assemble(emulator=>0) =~ m($u);                                            # The Intel Software Development Emulator is way too slow on these operations.
 }

if (1) {                                                                        # Make a byte string readonly
  my $s = CreateByteString;                                                     # Create a byte string
  $s->q("Hello");                                                               # Write code to byte string
  $s->makeReadOnly;                                                             # Make byte string read only
  $s->q(" World");                                                              # Try to write to byte string

  ok Assemble(debug=>2) =~ m(SDE ERROR: DEREFERENCING BAD MEMORY POINTER.*mov byte ptr .rax.rdx.1., r8b);
 }

if (1) {                                                                        # Make a read only byte string writable  #TByteString::makeReadOnly #TByteString::makeWriteable
  my $s = CreateByteString;                                                     # Create a byte string
  $s->q("Hello");                                                               # Write data to byte string
  $s->makeReadOnly;                                                             # Make byte string read only - tested above
  $s->makeWriteable;                                                            # Make byte string writable again
  $s->q(" World");                                                              # Try to write to byte string
  $s->out;

  ok Assemble =~ m(Hello World);
 }

if (1) {                                                                        # Allocate some space in byte string #TByteString::allocate
  my $s = CreateByteString;                                                     # Create a byte string
  $s->allocate(Vq(size, 0x20), my $o1 = Vq(offset));                            # Allocate space wanted
  $s->allocate(Vq(size, 0x30), my $o2 = Vq(offset));
  $s->allocate(Vq(size, 0x10), my $o3 = Vq(offset));
  $o1->outNL;
  $o2->outNL;
  $o3->outNL;

  is_deeply Assemble, <<END;
offset: 0000 0000 0000 0018
offset: 0000 0000 0000 0038
offset: 0000 0000 0000 0068
END
 }

if (1) {                                                                        #TSetRegisterToMinusOne
  SetRegisterToMinusOne rax;
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: FFFF FFFF FFFF FFFF);
 }

# It is one of the happiest characteristics of this glorious country that official utterances are invariably regarded as unanswerable

if (1) {                                                                        #TPrintOutZF #TSetZF #TClearZF
  SetZF;
  PrintOutZF;
  ClearZF;
  PrintOutZF;
  SetZF;
  PrintOutZF;
  SetZF;
  PrintOutZF;
  ClearZF;
  PrintOutZF;

  ok Assemble =~ m(ZF=1.*ZF=0.*ZF=1.*ZF=1.*ZF=0)s;
 }

if (1) {                                                                        #TSetLabel #TRegisterSize #TSaveFirstFour #TSaveFirstSeven #TRestoreFirstFour #TRestoreFirstSeven #TRestoreFirstFourExceptRax #TRestoreFirstSevenExceptRax #TRestoreFirstFourExceptRaxAndRdi #TRestoreFirstSevenExceptRaxAndRdi #TReverseBytesInRax
  Mov rax, 1;
  Mov rdi, 1;
  SaveFirstFour;
  Mov rax, 2;
  Mov rdi, 2;
  SaveFirstSeven;
  Mov rax, 3;
  Mov rdi, 4;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstSeven;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstFour;
  PrintOutRegisterInHex rax, rdi;

  SaveFirstFour;
  Mov rax, 2;
  Mov rdi, 2;
  SaveFirstSeven;
  Mov rax, 3;
  Mov rdi, 4;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstSevenExceptRax;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstFourExceptRax;
  PrintOutRegisterInHex rax, rdi;

  SaveFirstFour;
  Mov rax, 2;
  Mov rdi, 2;
  SaveFirstSeven;
  Mov rax, 3;
  Mov rdi, 4;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstSevenExceptRaxAndRdi;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstFourExceptRaxAndRdi;
  PrintOutRegisterInHex rax, rdi;

  Bswap rax;
  PrintOutRegisterInHex rax;

  my $l = Label;
  Jmp $l;
  SetLabel $l;

  is_deeply Assemble, <<END;
   rax: 0000 0000 0000 0003
   rdi: 0000 0000 0000 0004
   rax: 0000 0000 0000 0002
   rdi: 0000 0000 0000 0002
   rax: 0000 0000 0000 0001
   rdi: 0000 0000 0000 0001
   rax: 0000 0000 0000 0003
   rdi: 0000 0000 0000 0004
   rax: 0000 0000 0000 0003
   rdi: 0000 0000 0000 0002
   rax: 0000 0000 0000 0003
   rdi: 0000 0000 0000 0001
   rax: 0000 0000 0000 0003
   rdi: 0000 0000 0000 0004
   rax: 0000 0000 0000 0003
   rdi: 0000 0000 0000 0004
   rax: 0000 0000 0000 0003
   rdi: 0000 0000 0000 0004
   rax: 0300 0000 0000 0000
END

  ok 8 == RegisterSize rax;
 }

if (0) {                                                                        #TGenTree #TUnReorderXmmRegisters #TReorderXmmRegisters #TPrintOutStringNL #Tcxr #TByteString::dump
  my $t = GenTree(2,2);                                                         # Tree description
  $t->node->();                                                                 # Root
  Movdqa xmm1, xmm0;                                                            # Root is in xmm1

  if (1)                                                                        # New left node
   {$t->node->();                                                               # Node in xmm0
    Movdqa xmm2, xmm0;                                                          # Left is in xmm2

    cxr {$t->insertLeft->()} 1,2;                                               # Insert left under root
    cxr {$t->dump->("Left")} 2;                                                 # Left node after insertion
   }

  if (1)                                                                        # New right node in xmm0
   {$t->node->();
    Movdqa xmm3, xmm0;                                                          # Right is in xmm3

    cxr {$t->insertRight->()} 1,3;                                              # Insert left under root
    cxr {$t->dump->("Right")} 3;                                                # Right node after insertion
   }

  cxr
   {$t->dump->("Root");                                                         # Root node after insertions
    $t->isRoot->();
    IfNz {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
   } 1;

  PushRR xmm0;                                                                  # Dump underlying  byte string
  PopRR rdi, rax;
  $t->byteString->dump;

  Exit;                                                                         # Return to operating system

  is_deeply Assemble, <<END;                                                    # Test tree so produced
Left
ArenaTreeNode at: 0000 0000 0000 00B0
   up: 0000 0000 0000 0010
 left: 0000 0000 0000 0000
right: 0000 0000 0000 0000
Right
ArenaTreeNode at: 0000 0000 0000 0150
   up: 0000 0000 0000 0010
 left: 0000 0000 0000 0000
right: 0000 0000 0000 0000
Root
ArenaTreeNode at: 0000 0000 0000 0010
   up: 0000 0000 0000 0000
 left: 0000 0000 0000 00B0
right: 0000 0000 0000 0150
root
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 01E0
END
 }
else
 {ok 1;
 }

if (1) {                                                                        #TRb #TRd #TRq #TRw #TDb #TDd #TDq #TDw #TCopyMemory
  my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;
  my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

  Vmovdqu8 xmm0, "[$s]";
  Vmovdqu8 xmm1, "[$t]";
  PrintOutRegisterInHex xmm0;
  PrintOutRegisterInHex xmm1;
  Sub rsp, 16;

  Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
  Mov rdi, 16;
  Mov rsi, $s;
  CopyMemory(Vq(source, rsi), Vq(target, rax), Vq(size, rdi));
  PrintOutMemoryInHex;

  my $r = Assemble;
  ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
  ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
  ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);
 }

if (1) {                                                                        #TAllocateMemory #TPrintOutMemoryInHexNL #TCopyMemory
  my $N = 256;
  my $s = Rb 0..$N-1;
  AllocateMemory(Vq(size, $N), my $a = Vq(address));
  CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);

  AllocateMemory(Vq(size, $N), my $b = Vq(address));
  CopyMemory(source => $a, target => $b, Vq(size, $N));

  $b->setReg(rax);
  Mov rdi, $N;
  PrintOutMemoryInHexNL;

  is_deeply Assemble, <<END;
0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
END
 }

if (1) {                                                                        # Variable length shift
  Mov rax, -1;
  Mov cl, 30;
  Shl rax, cl;
  Kmovq k0, rax;
  PrintOutRegisterInHex k0;

  ok Assemble =~ m(k0: FFFF FFFF C000 0000)s;
 }

if (1) {                                                                        #
  ClearRegisters rax;
  Bts rax, 14;
  Not rax;
  PrintOutRegisterInHex rax;
  Kmovq k1, rax;
  PrintOutRegisterInHex k1;
  KeepFree rax;

  Mov rax, 1;
  Vpbroadcastb zmm0, rax;
  PrintOutRegisterInHex zmm0;

  Vpexpandd "zmm1{k1}", zmm0;
  PrintOutRegisterInHex zmm1;

  is_deeply Assemble, <<END;
   rax: FFFF FFFF FFFF BFFF
    k1: FFFF FFFF FFFF BFFF
  zmm0: 0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101
  zmm1: 0101 0101 0000 0000   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101   0101 0101 0101 0101
END
 }

if (1) {                                                                        #TInsertIntoXyz
  my $s    = Rb 0..63;
  Vmovdqu8 xmm0,"[$s]";                                                         # Number each byte
  Vmovdqu8 ymm1,"[$s]";
  Vmovdqu8 zmm2,"[$s]";
  Vmovdqu8 zmm3,"[$s]";

  SetRegisterToMinusOne rax;                                                    # Insert some ones
  InsertIntoXyz xmm0, 2, 4;
  InsertIntoXyz ymm1, 4, 5;
  InsertIntoXyz zmm2, 8, 6;

  PrintOutRegisterInHex xmm0;                                                   # Print the insertions
  PrintOutRegisterInHex ymm1;
  PrintOutRegisterInHex zmm2;

  ClearRegisters xmm0;                                                          # Insert some zeroes
  InsertIntoXyz zmm3, 16, 2;
  PrintOutRegisterInHex zmm3;

  my $r = Assemble;
  ok $r =~ m(xmm0: 0D0C 0B0A 0908 FFFF   0706 0504 0302 0100);
  ok $r =~ m(ymm1: 1B1A 1918 1716 1514   FFFF FFFF 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);
  ok $r =~ m(zmm2: 3736 3534 3332 3130   FFFF FFFF FFFF FFFF   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);
  ok $r =~ m(zmm3: 2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   0000 0000 0000 0000   0000 0000 0000 0000   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);
 }

if (1) {
  my $P = "2F";                                                                 # Value to test for
  my $l = Rb 0;  Rb $_ for 1..RegisterSize zmm0;                                # 0..63
  Vmovdqu8 zmm0, "[$l]";                                                        # Load data to test
  PrintOutRegisterInHex zmm0;

  Mov rax, "0x$P";                                                              # Broadcast the value to be tested
  Vpbroadcastb zmm1, rax;
  PrintOutRegisterInHex zmm1;

  for my $c(0..7)                                                               # Each possible test
   {my $m = "k$c";
    Vpcmpub $m, zmm1, zmm0, $c;
    PrintOutRegisterInHex $m;
   }

  Kmovq rax, k0;                                                                # Count the number of trailing zeros in k0
  Tzcnt rax, rax;
  PrintOutRegisterInHex rax;

  is_deeply [split //, Assemble], [split //, <<END];                            # Assemble and test
  zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  zmm1: 2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F
    k0: 0000 8000 0000 0000
    k1: FFFF 0000 0000 0000
    k2: FFFF 8000 0000 0000
    k3: 0000 0000 0000 0000
    k4: FFFF 7FFF FFFF FFFF
    k5: 0000 FFFF FFFF FFFF
    k6: 0000 7FFF FFFF FFFF
    k7: FFFF FFFF FFFF FFFF
   rax: 0000 0000 0000 00$P
END
 }

if (1) {                                                                        #TCstrlen
  my $s = Rs("abcd");
  Mov rax, $s;
  Cstrlen;
  PrintOutRegisterInHex r15;
  ok Assemble =~ m(r15: 0000 0000 0000 0004);
 }

if (1) {                                                                        # Hash a string #THash
  Mov rax, "[rbp+24]";
  Cstrlen;                                                                      # Length of string to hash
  Mov rdi, r15;
  Hash();                                                                       # Hash string

  PrintOutRegisterInHex r15;

  my $e = Assemble keep=>'hash';                                                # Assemble to the specified file name
  ok qx($e "")  =~ m(r15: 0000 3F80 0000 3F80);                                 # Test well known hashes
  ok qx($e "a") =~ m(r15: 0000 3F80 C000 45B2);

  if (0 and $develop)                                                           # Hash various strings
   {my %r; my %f; my $count = 0;
    my $N = RegisterSize zmm0;

    if (1)                                                                      # Fixed blocks
     {for my $l(qw(a ab abc abcd), 'a a', 'a  a')
       {for my $i(1..$N)
         {my $t = $l x $i;
          last if $N < length $t;
          my $s = substr($t.(' ' x $N), 0, $N);
          next if $f{$s}++;
          my $r = qx($e "$s");
          say STDERR "$count  $r";
          if ($r =~ m(^.*r15:\s*(.*)$)m)
           {push $r{$1}->@*, $s;
            ++$count;
           }
         }
       }
     }

    if (1)                                                                      # Variable blocks
     {for my $l(qw(a ab abc abcd), '', 'a a', 'a  a')
       {for my $i(1..$N)
         {my $t = $l x $i;
          next if $f{$t}++;
          my $r = qx($e "$t");
          say STDERR "$count  $r";
          if ($r =~ m(^.*r15:\s*(.*)$)m)
           {push $r{$1}->@*, $t;
            ++$count;
           }
         }
       }
     }
    for my $r(keys %r)
     {delete $r{$r} if $r{$r}->@* < 2;
     }

    say STDERR dump(\%r);
    say STDERR "Keys hashed: ", $count;
    confess "Duplicates : ",  scalar keys(%r);
   }
 }

if (1) {                                                                        #TLoadShortStringFromMemoryToZmm
  my $s = Rb(3, 0x01, 0x02, 0x03);
  my $t = Rb(7, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a);

  LoadShortStringFromMemoryToZmm 0, $s;
  LoadShortStringFromMemoryToZmm 1, $t;
  ConcatenateShortStrings(0, 1);
  PrintOutRegisterInHex xmm0;
  PrintOutRegisterInHex xmm1;

  my $r = Assemble;
  ok $r =~ m(xmm0: 0000 0000 000A 0908   0706 0504 0302 010A);
  ok $r =~ m(xmm1: 0000 0000 0000 0000   0A09 0807 0605 0407);
 }

if (1) {                                                                        # Concatenate empty string to itself 4 times
  my $s = Rb(0);
  LoadShortStringFromMemoryToZmm 0, $s;
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);
  PrintOutRegisterInHex xmm0;

  ok Assemble =~ m(xmm0: 0000 0000 0000 0000   0000 0000 0000 0000);
 }

if (1) {                                                                        #Tif #TifEq #TifNe #TifLe #TifLt #TifGe #TifGt
  my $cmp = sub
   {my ($a, $b) = @_;

    for my $op(qw(eq ne lt le gt ge))
     {Mov rax, $a;
      Cmp rax, $b;
      KeepFree rax;
      my $Op = ucfirst $op;
      eval qq(If$Op {PrintOutStringNL("$a $op $b")} sub {PrintOutStringNL("$a NOT $op $b")});
     }
   };
  &$cmp(1,1);
  &$cmp(1,2);
  &$cmp(3,2);
  is_deeply Assemble, <<END;
1 eq 1
1 NOT ne 1
1 NOT lt 1
1 le 1
1 NOT gt 1
1 ge 1
1 NOT eq 2
1 ne 2
1 lt 2
1 le 2
1 NOT gt 2
1 NOT ge 2
3 NOT eq 2
3 ne 2
3 NOT lt 2
3 NOT le 2
3 gt 2
3 ge 2
END
 }

if (0) {                                                                        # Concatenate string of length 1 to itself 4 times
  my $s = Rb(4, 1..4);
  LoadShortStringFromMemoryToZmm 0, $s;
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);

  my $b = CreateByteString;                                                     # Create a string
  $b->allocBlock;
  $b->putBlock(0);
  $b->getBlock(1);
  PrintOutRegisterInHex ymm0;
  PrintOutRegisterInHex ymm1;

  is_deeply Assemble, <<END;
  ymm0: 0302 0104 0302 0104   0302 0104 0302 0104   0302 0104 0302 0104   0302 0104 0302 0120
  ymm1: 0302 0104 0302 0104   0302 0104 0302 0104   0302 0104 0302 0104   0302 0104 0302 0120
END
 }
else
 {ok 1;
 }

if (1) {                                                                        #TSetMaskRegister
  Mov rax, 8;
  Mov rsi, -1;
  Inc rsi; SetMaskRegister(k0, rax, rsi); PrintOutRegisterInHex k0;
  Inc rsi; SetMaskRegister(k1, rax, rsi); PrintOutRegisterInHex k1;
  Inc rsi; SetMaskRegister(k2, rax, rsi); PrintOutRegisterInHex k2;
  Inc rsi; SetMaskRegister(k3, rax, rsi); PrintOutRegisterInHex k3;
  Inc rsi; SetMaskRegister(k4, rax, rsi); PrintOutRegisterInHex k4;
  Inc rsi; SetMaskRegister(k5, rax, rsi); PrintOutRegisterInHex k5;
  Inc rsi; SetMaskRegister(k6, rax, rsi); PrintOutRegisterInHex k6;
  Inc rsi; SetMaskRegister(k7, rax, rsi); PrintOutRegisterInHex k7;

  is_deeply Assemble, <<END;
    k0: 0000 0000 0000 0000
    k1: 0000 0000 0000 0100
    k2: 0000 0000 0000 0300
    k3: 0000 0000 0000 0700
    k4: 0000 0000 0000 0F00
    k5: 0000 0000 0000 1F00
    k6: 0000 0000 0000 3F00
    k7: 0000 0000 0000 7F00
END
 }

if (1) {                                                                        #TMaximumOfTwoRegisters #TMinimumOfTwoRegisters
  Mov rax, 1;
  Mov rdi, 2;
  PrintOutRegisterInHex MaximumOfTwoRegisters r15, rax, rdi;
  PrintOutRegisterInHex MinimumOfTwoRegisters r14, rax, rdi;

  is_deeply Assemble, <<END;
   r15: 0000 0000 0000 0002
   r14: 0000 0000 0000 0001
END
 }

if (1) {                                                                        #TPlus #TMinus #TFree
  Copy r15, 2;
  Copy r14, 3;
  KeepFree r15;
  Plus(r15, r15, r14);
  PrintOutRegisterInHex r15;
  Copy r13, 4;
  Minus(r12, r15, r13);
  PrintOutRegisterInHex r12;

  is_deeply Assemble, <<END;
   r15: 0000 0000 0000 0005
   r12: 0000 0000 0000 0001
END
 }

if (1) {                                                                        #TLoadTargetZmmFromSourceZmm #TCopyZmm
  my $s = Rb(17, 1..17);
  LoadShortStringFromMemoryToZmm 0, $s;                                         # Load a sample string
  Keep zmm0;
  PrintOutRegisterInHex xmm0;
  LoadTargetZmmFromSourceZmm 1, Copy(rdi, 3), 0, Copy(rdx, 8), Copy(rsi, 2);
  PrintOutRegisterInHex xmm1;
  KeepFree rdi;

  LoadTargetZmmFromSourceZmm 2, Copy(rdi, 4), 0, rdx, rsi;
  PrintOutRegisterInHex xmm2;

  Copy(zmm3, zmm0);
  PrintOutRegisterInHex xmm3;

  ClearRegisters zmm4;
  Lea rax, "[$s+4]";
  LoadZmmFromMemory 4, rdx, rsi, rax;
  Sub rax, 4;
  PrintOutRegisterInHex xmm4;

  is_deeply Assemble, <<END;
  xmm0: 0F0E 0D0C 0B0A 0908   0706 0504 0302 0111
  xmm1: 0000 0000 0000 0000   0000 0009 0800 0000
  xmm2: 0000 0000 0000 0000   0000 0908 0000 0000
  xmm3: 0F0E 0D0C 0B0A 0908   0706 0504 0302 0111
  xmm4: 0000 0000 0000 0504   0000 0000 0000 0000
END
 }

if (1) {                                                                        #TLoadTargetZmmFromSourceZmm #TCopy
  my $s = Rb(13, 1..13);
  my $t = Rb(1..64);
  my $source = rax;                                                             # Address to load from
  my $start  = rsi;                                                             # Start position in the zmm register
  my $length = rdi;                                                             # Length of copy

  Copy $source, $s;
  LoadShortStringFromMemoryToZmm 0, $s;                                         # Load a sample string
  KeepFree $source;
  PrintOutRegisterInHex xmm0;

  LoadZmmFromMemory 0, Increment(GetLengthOfShortString($start, 0)), Copy($length, 1), Copy($source, $t);
  PrintOutRegisterInHex xmm0;

  LoadZmmFromMemory 0, $start, $length, $source;
  PrintOutRegisterInHex xmm0;

  KeepFree $length;
  LoadZmmFromMemory 0, $start, Minus($length, Copy(r13, 56), $start), $source;
  SetLengthOfShortString 0, sil;                                                # Set current length of zmm0
  PrintOutRegisterInHex xmm0, zmm0;

  is_deeply Assemble, <<END;
  xmm0: 0000 0D0C 0B0A 0908   0706 0504 0302 010D
  xmm0: 0001 0D0C 0B0A 0908   0706 0504 0302 010D
  xmm0: 0201 0D0C 0B0A 0908   0706 0504 0302 010D
  xmm0: 0201 0D0C 0B0A 0908   0706 0504 0302 0138
  zmm0: 0000 0000 0000 0000   2A29 2827 2625 2423   2221 201F 1E1D 1C1B   1A19 1817 1615 1413   1211 100F 0E0D 0C0B   0A09 0807 0605 0403   0201 0D0C 0B0A 0908   0706 0504 0302 0138
END
 }

if (1)                                                                          #TScope #TScopeEnd  #TScope::contains #TScope::currentlyVisible
 {my $start = Scope(start);
  my $s1    = Scope(s1);
  my $s2    = Scope(s2);
  is_deeply $s2->depth, 2;
  is_deeply $s2->name,  q(s2);
  ScopeEnd;

  my $t1    = Scope(t1);
  my $t2    = Scope(t2);
  is_deeply $t1->depth, 2;
  is_deeply $t1->name,  q(t1);
  is_deeply $t2->depth, 3;
  is_deeply $t2->name,  q(t2);

  ok  $s1->currentlyVisible;
  ok !$s2->currentlyVisible;

  ok  $s1->contains($t2);
  ok !$s2->contains($t2);

  ScopeEnd;

  is_deeply $s1->depth, 1;
  is_deeply $s1->name,  q(s1);
  ScopeEnd;
 }

if (1) {                                                                        #TVq  #TNasm::X86::Variable::print #TNasm::X86::Variable::add
  my $a = Vq(a, 3);   $a->print;
  my $c = $a +  2;    $c->print;
  my $d = $c -  $a;   $d->print;
  my $e = $d == 2;    $e->print;
  my $f = $d != 2;    $f->print;
  my $g = $a *  2;    $g->print;
  my $h = $g /  2;    $h->print;
  my $i = $a %  2;    $i->print;

  If ($a == 3, sub{PrintOutStringNL "a == 3"});

  is_deeply Assemble, <<END;
0300 0000 0000 0000
0500 0000 0000 0000
0200 0000 0000 0000
0100 0000 0000 0000
0000 0000 0000 0000
0600 0000 0000 0000
0300 0000 0000 0000
0100 0000 0000 0000
a == 3
END
 }

if (1) {                                                                        #TNasm::X86::Variable::dump  #TNasm::X86::Variable::print
  my $a = Vq(a, 3); $a->outNL;
  my $b = Vq(b, 2); $b->outNL;
  my $c = $a +  $b; $c->outNL;
  my $d = $c -  $a; $d->outNL;
  my $e = $d == $b; $e->outNL;
  my $f = $d != $b; $f->outNL;
  my $g = $a *  $b; $g->outNL;
  my $h = $g /  $b; $h->outNL;
  my $i = $a %  $b; $i->outNL;
  is_deeply Assemble, <<END;
a: 0000 0000 0000 0003
b: 0000 0000 0000 0002
(a add b): 0000 0000 0000 0005
((a add b) sub a): 0000 0000 0000 0002
(((a add b) sub a) eq b): 0000 0000 0000 0001
(((a add b) sub a) ne b): 0000 0000 0000 0000
(a times b): 0000 0000 0000 0006
((a times b) / b): 0000 0000 0000 0003
(a % b): 0000 0000 0000 0001
END
 }

if (1) {                                                                        #TNasm::X86::Variable::for
  Vq(limit,10)->for(sub
   {my ($i, $start, $next, $end) = @_;
    $i->print;
   });

  is_deeply Assemble, <<END;
0000 0000 0000 0000
0100 0000 0000 0000
0200 0000 0000 0000
0300 0000 0000 0000
0400 0000 0000 0000
0500 0000 0000 0000
0600 0000 0000 0000
0700 0000 0000 0000
0800 0000 0000 0000
0900 0000 0000 0000
END
 }

if (1) {                                                                        #T
  Mov rax, 2;
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: 0000 0000 0000 0002);
 }

if (1) {                                                                        #TNasm::X86::Variable::min #TNasm::X86::Variable::max
  my $a = Vq("a", 1);
  my $b = Vq("b", 2);
  my $c = $a->min($b);
  my $d = $a->max($b);
  $a->outNL;
  $b->outNL;
  $c->outNL;
  $d->outNL;

  is_deeply Assemble,<<END;
a: 0000 0000 0000 0001
b: 0000 0000 0000 0002
Minimum(a, b): 0000 0000 0000 0001
Maximum(a, b): 0000 0000 0000 0002
END
 }

if (1) {                                                                        #TNasm::X86::Variable::setMask
  my $start  = Vq("Start",  7);
  my $length = Vq("Length", 3);
  $start->setMask($length, k7);
  PrintOutRegisterInHex k7;

  is_deeply Assemble, <<END;
    k7: 0000 0000 0000 0380
END
 }

if (1) {                                                                        #TNasm::X86::Variable::setZmm
  my $s = Rb(0..128);
  my $source = Vq(Source, $s);

  if (1)                                                                        # First block
   {my $offset = Vq(Offset, 7);
    my $length = Vq(Length, 3);
    $source->setZmm(0, $offset, $length);
   }

  if (1)                                                                        # Second block
   {my $offset = Vq(Offset, 33);
    my $length = Vq(Length, 12);
    $source->setZmm(0, $offset, $length);
   }

  PrintOutRegisterInHex zmm0;

  is_deeply Assemble, <<END;
  zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 000B 0A09 0807   0605 0403 0201 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0201   0000 0000 0000 0000
END
 }

if (1) {                                                                        #TNasm::X86::Variable::getZmm  #TNasm::X86::Variable::setZmm
  my $a = Vz a, Rb((map {"0x${_}0"} 0..9, 'a'..'f')x4);
  my $b = Vz b, Rb((map {"0x0${_}"} 0..9, 'a'..'f')x4);

   $a      ->loadZmm(0);                                                        # Show variable in zmm0
   $b      ->loadZmm(1);                                                        # Show variable in zmm1

  ($a + $b)->loadZmm(2);                                                        # Add bytes      and show in zmm2
  ($a - $b)->loadZmm(3);                                                        # Subtract bytes and show in zmm3

  PrintOutRegisterInHex "zmm$_" for 0..3;

  is_deeply Assemble, <<END;
  zmm0: F0E0 D0C0 B0A0 9080   7060 5040 3020 1000   F0E0 D0C0 B0A0 9080   7060 5040 3020 1000   F0E0 D0C0 B0A0 9080   7060 5040 3020 1000   F0E0 D0C0 B0A0 9080   7060 5040 3020 1000
  zmm1: 0F0E 0D0C 0B0A 0908   0706 0504 0302 0100   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  zmm2: FFEE DDCC BBAA 9988   7766 5544 3322 1100   FFEE DDCC BBAA 9988   7766 5544 3322 1100   FFEE DDCC BBAA 9988   7766 5544 3322 1100   FFEE DDCC BBAA 9988   7766 5544 3322 1100
  zmm3: E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00   E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00   E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00   E1D2 C3B4 A596 8778   695A 4B3C 2D1E 0F00
END
 }

if (1) {                                                                        #TgetDFromZmmAsVariable #TNasm::X86::Variable::putDIntoZmm
  my $s = Rb(0..8);
  my $c = Vq("Content",   "[$s]");
     $c->putBIntoZmm(0,  4);
     $c->putWIntoZmm(0,  6);
     $c->putDIntoZmm(0, 10);
     $c->putQIntoZmm(0, 16);
  PrintOutRegisterInHex zmm0;
  getBFromZmmAsVariable(0, 12)->outNL;
  getWFromZmmAsVariable(0, 12)->outNL;
  getDFromZmmAsVariable(0, 12)->outNL;
  getQFromZmmAsVariable(0, 12)->outNL;

  is_deeply Assemble, <<END;
  zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0706 0504 0302 0100   0000 0302 0100 0000   0100 0000 0000 0000
b at offset 12 in zmm0: 0000 0000 0000 0002
w at offset 12 in zmm0: 0000 0000 0000 0302
d at offset 12 in zmm0: 0000 0000 0000 0302
q at offset 12 in zmm0: 0302 0100 0000 0302
END
 }

#latest:;
if (1) {                                                                        #TCreateBlockString
  my $s = Rb(0..255);
  my $B =     CreateByteString;
  my $b = $B->CreateBlockString;
  $b->append(Vq(source, $s), Vq(size,  3)); $b->dump;
  $b->append(Vq(source, $s), Vq(size,  4)); $b->dump;
  $b->append(Vq(source, $s), Vq(size,  5)); $b->dump;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0201 0003

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0007
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0302 0100 0201 0007

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 000C
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0004 0302 0100   0302 0100 0201 000C

END
 }

if (1) {                                                                        #TCreateBlockString
  my $s = Rb(0..255);
  my $B =     CreateByteString;
  my $b = $B->CreateBlockString;
  $b->append(Vq(source, $s), Vq(size, 165)); $b->dump;
  $b->append(Vq(source, $s), Vq(size,   2)); $b->dump;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 0018 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 00D8   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 00D8 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37
Offset: 0000 0000 0000 00D8   Length: 0000 0000 0000 0002
 zmm31: 0000 0018 0000 0098   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0001 0002

END
 }

if (1) {                                                                        #TCreateBlockString
  my $s = Rb(0..255);
  my $B =     CreateByteString;
  my $b = $B->CreateBlockString;
  $b->append(Vq(source, $s), Vq(size,  56)); $b->dump;
  $b->append(Vq(source, $s), Vq(size,   4)); $b->dump;
  $b->append(Vq(source, $s), Vq(size,   5)); $b->dump;
  $b->append(Vq(source, $s), Vq(size,   0)); $b->dump;
  $b->append(Vq(source, $s), Vq(size, 256)); $b->dump;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0001
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 3701

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0005
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0302 0100 3705

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 000A
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0004 0302   0100 0302 0100 370A

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 000A
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0004 0302   0100 0302 0100 370A

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0158   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   2C2B 2A29 2827 2625   2423 2221 201F 1E1D   1C1B 1A19 1817 1615   1413 1211 100F 0E0D   0C0B 0A09 0807 0605   0403 0201 0004 0302   0100 0302 0100 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 00D8 0000 0058   6362 6160 5F5E 5D5C   5B5A 5958 5756 5554   5352 5150 4F4E 4D4C   4B4A 4948 4746 4544   4342 4140 3F3E 3D3C   3B3A 3938 3736 3534   3332 3130 2F2E 2D37
Offset: 0000 0000 0000 00D8   Length: 0000 0000 0000 0037
 zmm31: 0000 0118 0000 0098   9A99 9897 9695 9493   9291 908F 8E8D 8C8B   8A89 8887 8685 8483   8281 807F 7E7D 7C7B   7A79 7877 7675 7473   7271 706F 6E6D 6C6B   6A69 6867 6665 6437
Offset: 0000 0000 0000 0118   Length: 0000 0000 0000 0037
 zmm31: 0000 0158 0000 00D8   D1D0 CFCE CDCC CBCA   C9C8 C7C6 C5C4 C3C2   C1C0 BFBE BDBC BBBA   B9B8 B7B6 B5B4 B3B2   B1B0 AFAE ADAC ABAA   A9A8 A7A6 A5A4 A3A2   A1A0 9F9E 9D9C 9B37
Offset: 0000 0000 0000 0158   Length: 0000 0000 0000 002E
 zmm31: 0000 0018 0000 0118   0000 0000 0000 0000   00FF FEFD FCFB FAF9   F8F7 F6F5 F4F3 F2F1   F0EF EEED ECEB EAE9   E8E7 E6E5 E4E3 E2E1   E0DF DEDD DCDB DAD9   D8D7 D6D5 D4D3 D22E

END
 }

if (1) {
  my $s = Rb(0..255);
  my $B = CreateByteString;
  my $b = $B->CreateBlockString;

  $b->append(source=>Vq(source, $s), Vq(size, 256));
  $b->len(my $size = Vq(size));
  $size->outNL;
  $b->clear;

  $b->append(Vq(source, $s), size => Vq(size,  16)); $b->dump;
  $b->len(my $size2 = Vq(size));
  $size2->outNL;

  is_deeply Assemble, <<END;
size: 0000 0000 0000 0100
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0010
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 000F   0E0D 0C0B 0A09 0807   0605 0403 0201 0010

size: 0000 0000 0000 0010
END
 }

#latest:;
if (1) {
  my $c = Rb(0..255);
  my $S = CreateByteString;   my $s = $S->CreateBlockString;
  my $T = CreateByteString;   my $t = $T->CreateBlockString;

  $s->append(source=>Vq(source, $c), Vq(size, 256));
  $t->concatenate($s);
  $t->dump;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0000
 zmm31: 0000 0058 0000 0158   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 00D8 0000 0058   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 00D8   Length: 0000 0000 0000 0037
 zmm31: 0000 0118 0000 0098   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37
Offset: 0000 0000 0000 0118   Length: 0000 0000 0000 0037
 zmm31: 0000 0158 0000 00D8   DBDA D9D8 D7D6 D5D4   D3D2 D1D0 CFCE CDCC   CBCA C9C8 C7C6 C5C4   C3C2 C1C0 BFBE BDBC   BBBA B9B8 B7B6 B5B4   B3B2 B1B0 AFAE ADAC   ABAA A9A8 A7A6 A537
Offset: 0000 0000 0000 0158   Length: 0000 0000 0000 0024
 zmm31: 0000 0018 0000 0118   0000 0000 0000 0000   0000 0000 0000 0000   0000 00FF FEFD FCFB   FAF9 F8F7 F6F5 F4F3   F2F1 F0EF EEED ECEB   EAE9 E8E7 E6E5 E4E3   E2E1 E0DF DEDD DC24

END
 }

#latest:;
if (1) {                                                                        # Insert char in a one block string
  my $c = Rb(0..255);
  my $S = CreateByteString;   my $s = $S->CreateBlockString;

  $s->append(source=>Vq(source, $c), Vq(size, 3));
  $s->dump;

  $s->insertChar(character=>Vq(source, 0x44), position => Vq(size, 2));
  $s->dump;

  $s->insertChar(character=>Vq(source, 0x88), position => Vq(size, 2));
  $s->dump;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0201 0003

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0004
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0002 4401 0004

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0005
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0244 8801 0005

END
 }

#latest:;

if (1) {                                                                        # Insert char in a multi block string at position 22
  my $c = Rb(0..255);
  my $S = CreateByteString;   my $s = $S->CreateBlockString;

  $s->append(source=>Vq(source, $c), Vq(size, 58));
  $s->dump;

  $s->insertChar(Vq(character, 0x44), Vq(position, 22));
  $s->dump;

  $s->insertChar(Vq(character, 0x88), Vq(position, 22));
  $s->dump;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 3938 3703

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0016
 zmm31: 0000 0098 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0016
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0022
 zmm31: 0000 0058 0000 0058   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 5836 3534   3332 3130 2F2E 2D2C   2B2A 2928 2726 2524   2322 2120 1F1E 1D1C   1B1A 1918 1716 4422
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 3938 3703

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0017
 zmm31: 0000 0098 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   8815 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0017
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0022
 zmm31: 0000 0058 0000 0058   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 5836 3534   3332 3130 2F2E 2D2C   2B2A 2928 2726 2524   2322 2120 1F1E 1D1C   1B1A 1918 1716 4422
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 3938 3703

END
 }

if (1) {                                                                        #BlockString::insertChar
  my $c = Rb(0..255);
  my $S = CreateByteString;   my $s = $S->CreateBlockString;

  $s->append(source=>Vq(source, $c), Vq(size, 166));
  $s->dump;

  $s->insertChar(Vq(character, 0x44), Vq(position, 64));
  $s->dump;

  $s->insertChar(Vq(character, 0x88), Vq(position, 64));
  $s->dump;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 00D8   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 00D8 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37
Offset: 0000 0000 0000 00D8   Length: 0000 0000 0000 0001
 zmm31: 0000 0018 0000 0098   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 A501

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 00D8   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0009
 zmm31: 0000 0118 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3709
Offset: 0000 0000 0000 0118   Length: 0000 0000 0000 002F
 zmm31: 0000 0098 0000 0058   0000 0000 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 442F
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 00D8 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37
Offset: 0000 0000 0000 00D8   Length: 0000 0000 0000 0001
 zmm31: 0000 0018 0000 0098   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 A501

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 00D8   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0158 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0158   Length: 0000 0000 0000 0001
 zmm31: 0000 0118 0000 0058   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0018 8801
Offset: 0000 0000 0000 0118   Length: 0000 0000 0000 002F
 zmm31: 0000 0098 0000 0058   0000 0000 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 442F
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 00D8 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37
Offset: 0000 0000 0000 00D8   Length: 0000 0000 0000 0001
 zmm31: 0000 0018 0000 0098   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 A501

END
 }

if (1) {                                                                        # Append a char
  my $c = Rb(0..255);
  my $S = CreateByteString;   my $s = $S->CreateBlockString;

  $s->append(source=>Vq(source, $c),  Vq(size, 3));      $s->dump;
  $s->insertChar(Vq(character, 0x44), Vq(position, 64)); $s->dump;
  $s->len(my $size = Vq(size));                          $size->outNL;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0201 0003

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0004
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0044 0201 0004

size: 0000 0000 0000 0004
END
 }

if (1) {                                                                        #TBlockString::deleteChar #TBlockString::len
  my $c = Rb(0..255);
  my $S = CreateByteString;   my $s = $S->CreateBlockString;

  $s->append(source=>Vq(source, $c),  Vq(size, 165)); $s->dump;
  $s->deleteChar(Vq(position, 0x44));                 $s->dump;
  $s->len(my $size = Vq(size));                       $size->outNL;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 0018 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37

Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0036
 zmm31: 0000 0098 0000 0018   186D 6C6B 6A69 6867   6665 6463 6261 605F   5E5D 5C5B 5A59 5857   5655 5453 5251 504F   4E4D 4C4B 4A49 4847   4645 4342 4140 3F3E   3D3C 3B3A 3938 3736
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 0018 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37

size: 0000 0000 0000 00A4
END
 }

#latest:;

if (1) {                                                                        #TBlockString::getChar
  my $c = Rb(0..255);
  my $S = CreateByteString;   my $s = $S->CreateBlockString;

  $s->append(source=>Vq(source, $c),  Vq(size, 110)); $s->dump;
  $s->getCharacter(Vq(position, 0x44), my $out = Vq(out)); $out->outNL;

  ok Assemble(debug => 0, eq => <<END);
Block String Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0018 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737

out: 0000 0000 0000 0044
END
 }

#latest:;

if (1) {                                                                        #TNasm::X86::Variable::setMask
  my $z = Vq('zero', 0);
  my $o = Vq('one',  1);
  my $t = Vq('two',  2);
  $z->setMask($o,       k7); PrintOutRegisterInHex k7;
  $z->setMask($t,       k6); PrintOutRegisterInHex k6;
  $z->setMask($o+$t,    k5); PrintOutRegisterInHex k5;
  $o->setMask($o,       k4); PrintOutRegisterInHex k4;
  $o->setMask($t,       k3); PrintOutRegisterInHex k3;
  $o->setMask($o+$t,    k2); PrintOutRegisterInHex k2;

  $t->setMask($o,       k1); PrintOutRegisterInHex k1;
  $t->setMask($t,       k0); PrintOutRegisterInHex k0;


  ok Assemble(debug => 0, eq => <<END);
    k7: 0000 0000 0000 0001
    k6: 0000 0000 0000 0003
    k5: 0000 0000 0000 0007
    k4: 0000 0000 0000 0002
    k3: 0000 0000 0000 0006
    k2: 0000 0000 0000 000E
    k1: 0000 0000 0000 0004
    k0: 0000 0000 0000 000C
END
 }

#latest:;

if (1) {                                                                        #TCreateBlockArray  #TBlockArray::push
  my $c = Rb(0..255);
  my $A = CreateByteString;  my $a = $A->CreateBlockArray;

  $a->push(element => Vq($_, $_)) for 1..15;  $A->dump;
  $a->push(element => Vq($_, $_)) for 0xff;   $A->dump;
  $a->push(element => Vq($_, $_)) for 17..31; $A->dump;
  $a->push(element => Vq($_, $_)) for 0xee;   $A->dump;
  $a->push(element => Vq($_, $_)) for 33..36; $A->dump;

  ok Assemble(debug => 0, eq => <<END);
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0058
0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000F00 0000 0100 00000200 0000 0300 00000400 0000 0500 00000600 0000 0700 00000800 0000 0900 0000
0040: 0A00 0000 0B00 00000C00 0000 0D00 00000E00 0000 0F00 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00001000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 00D8
0000: 0010 0000 0000 0000D800 0000 0000 00000000 0000 0000 00001F00 0000 5800 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00001100 0000 1200 00001300 0000 1400 00001500 0000 1600 00001700 0000 1800 00001900 0000 1A00 0000
00C0: 1B00 0000 1C00 00001D00 0000 1E00 00001F00 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 00D8
0000: 0010 0000 0000 0000D800 0000 0000 00000000 0000 0000 00002000 0000 5800 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00001100 0000 1200 00001300 0000 1400 00001500 0000 1600 00001700 0000 1800 00001900 0000 1A00 0000
00C0: 1B00 0000 1C00 00001D00 0000 1E00 00001F00 0000 EE00 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0118
0000: 0010 0000 0000 00001801 0000 0000 00000000 0000 0000 00002400 0000 5800 00009800 0000 D800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00001100 0000 1200 00001300 0000 1400 00001500 0000 1600 00001700 0000 1800 00001900 0000 1A00 0000
00C0: 1B00 0000 1C00 00001D00 0000 1E00 00001F00 0000 EE00 00002100 0000 2200 00002300 0000 2400 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

#latest:;
if (1) {                                                                        #TCreateBlockArray  #TBlockArray::push #TBlockArray::pop #TBlockArray::put #TBlockArray::get
  my $c = Rb(0..255);
  my $A = CreateByteString;  my $a = $A->CreateBlockArray;
  my $l = Vq(limit, 15);
  my $L = $l + 5;

  my sub put                                                                    # Put a constant or a variable
   {my ($e) = @_;
    $a->push(element => (ref($e) ? $e : Vq($e, $e)));
   };

  my sub get                                                                    # Get a constant or a variable
   {my ($i) = @_;
    $a->get(index=>(my $v = ref($i) ? $i : Vq('index', $i)), my $e = Vq(element));
    $v->out("index: ", "  "); $e->outNL;
   };

  $l->for(sub                                                                   # Loop to the limit pushing
   {my ($index, $start, $next, $end) = @_;
    put($index+1);
   });

  $l->for(sub                                                                   # Loop to the limit getting
   {my ($index, $start, $next, $end) = @_;
    get($index);
   });

  put(16);
  get(15);

  $L->for(sub
   {my ($index, $start, $next, $end) = @_;
    put($index+$l+2);
   });

  $L->for(sub
   {my ($index, $start, $next, $end) = @_;
    get($index + $l + 1);
   });

  if (1)
   {$a->put(my $i = Vq('index',  9), my $e = Vq(element, 0xFFF9));
    get(9);
   }

  if (1)
   {$a->put(my $i = Vq('index', 19), my $e = Vq(element, 0xEEE9));
    get(19);
   }

  $a->dump;
  ($l+$L+1)->for(sub
   {my ($i, $start, $next, $end) = @_;
    $a->pop(my $e = Vq(element));
    $e->outNL;
    If (($e == 33)|($e == 32)|($e == 17)|($e == 16)|($e == 15)|($e == 14)|($e == 1)|($e == 0), sub
     {$a->dump;
     });
   });

  Vq(limit, 38)->for(sub                                                        # Push using a loop and reusing the freed space
   {my ($index, $start, $next, $end) = @_;
    $a->push(element=>$index*2);
   });

  $a->dump;

  Vq(limit, 38)->for(sub                                                        # Push using a loop and reusing the freed space
   {my ($index, $start, $next, $end) = @_;
    $a->pop(my $e = Vq(element));
    $e->outNL;
   });

  $a->dump;

  ok Assemble(debug => 0, eq => <<END);
index: 0000 0000 0000 0000  element: 0000 0000 0000 0001
index: 0000 0000 0000 0001  element: 0000 0000 0000 0002
index: 0000 0000 0000 0002  element: 0000 0000 0000 0003
index: 0000 0000 0000 0003  element: 0000 0000 0000 0004
index: 0000 0000 0000 0004  element: 0000 0000 0000 0005
index: 0000 0000 0000 0005  element: 0000 0000 0000 0006
index: 0000 0000 0000 0006  element: 0000 0000 0000 0007
index: 0000 0000 0000 0007  element: 0000 0000 0000 0008
index: 0000 0000 0000 0008  element: 0000 0000 0000 0009
index: 0000 0000 0000 0009  element: 0000 0000 0000 000A
index: 0000 0000 0000 000A  element: 0000 0000 0000 000B
index: 0000 0000 0000 000B  element: 0000 0000 0000 000C
index: 0000 0000 0000 000C  element: 0000 0000 0000 000D
index: 0000 0000 0000 000D  element: 0000 0000 0000 000E
index: 0000 0000 0000 000E  element: 0000 0000 0000 000F
index: 0000 0000 0000 000F  element: 0000 0000 0000 0010
index: 0000 0000 0000 0010  element: 0000 0000 0000 0011
index: 0000 0000 0000 0011  element: 0000 0000 0000 0012
index: 0000 0000 0000 0012  element: 0000 0000 0000 0013
index: 0000 0000 0000 0013  element: 0000 0000 0000 0014
index: 0000 0000 0000 0014  element: 0000 0000 0000 0015
index: 0000 0000 0000 0015  element: 0000 0000 0000 0016
index: 0000 0000 0000 0016  element: 0000 0000 0000 0017
index: 0000 0000 0000 0017  element: 0000 0000 0000 0018
index: 0000 0000 0000 0018  element: 0000 0000 0000 0019
index: 0000 0000 0000 0019  element: 0000 0000 0000 001A
index: 0000 0000 0000 001A  element: 0000 0000 0000 001B
index: 0000 0000 0000 001B  element: 0000 0000 0000 001C
index: 0000 0000 0000 001C  element: 0000 0000 0000 001D
index: 0000 0000 0000 001D  element: 0000 0000 0000 001E
index: 0000 0000 0000 001E  element: 0000 0000 0000 001F
index: 0000 0000 0000 001F  element: 0000 0000 0000 0020
index: 0000 0000 0000 0020  element: 0000 0000 0000 0021
index: 0000 0000 0000 0021  element: 0000 0000 0000 0022
index: 0000 0000 0000 0022  element: 0000 0000 0000 0023
index: 0000 0000 0000 0023  element: 0000 0000 0000 0024
index: 0000 0000 0000 0009  element: 0000 0000 0000 FFF9
index: 0000 0000 0000 0013  element: 0000 0000 0000 EEE9
Block Array
Size: 0000 0000 0000 0024   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 00D8 0000 0098   0000 0058 0000 0024
Full: 0000 0000 0000 0058   zmm30: 0000 0010 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 FFF9 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
Full: 0000 0000 0000 0098   zmm30: 0000 0020 0000 001F   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 EEE9 0000 0013   0000 0012 0000 0011
Last: 0000 0000 0000 00D8   zmm30: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0024 0000 0023   0000 0022 0000 0021
element: 0000 0000 0000 0024
element: 0000 0000 0000 0023
element: 0000 0000 0000 0022
element: 0000 0000 0000 0021
Block Array
Size: 0000 0000 0000 0020   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0098   0000 0058 0000 0020
Full: 0000 0000 0000 0058   zmm30: 0000 0010 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 FFF9 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
Full: 0000 0000 0000 0098   zmm30: 0000 0020 0000 001F   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 EEE9 0000 0013   0000 0012 0000 0011
element: 0000 0000 0000 0020
Block Array
Size: 0000 0000 0000 001F   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0098   0000 0058 0000 001F
Full: 0000 0000 0000 0058   zmm30: 0000 0010 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 FFF9 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
Last: 0000 0000 0000 0098   zmm30: 0000 0020 0000 001F   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 EEE9 0000 0013   0000 0012 0000 0011
element: 0000 0000 0000 001F
element: 0000 0000 0000 001E
element: 0000 0000 0000 001D
element: 0000 0000 0000 001C
element: 0000 0000 0000 001B
element: 0000 0000 0000 001A
element: 0000 0000 0000 0019
element: 0000 0000 0000 0018
element: 0000 0000 0000 0017
element: 0000 0000 0000 0016
element: 0000 0000 0000 0015
element: 0000 0000 0000 EEE9
element: 0000 0000 0000 0013
element: 0000 0000 0000 0012
element: 0000 0000 0000 0011
Block Array
Size: 0000 0000 0000 0010   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0058 0000 0010
Full: 0000 0000 0000 0058   zmm30: 0000 0010 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 FFF9 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
element: 0000 0000 0000 0010
Block Array
Size: 0000 0000 0000 000F   zmm31: 0000 000F 0000 000E   0000 000D 0000 000C   0000 000B 0000 FFF9   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 000F
element: 0000 0000 0000 000F
Block Array
Size: 0000 0000 0000 000E   zmm31: 0000 000F 0000 000E   0000 000D 0000 000C   0000 000B 0000 FFF9   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 000E
element: 0000 0000 0000 000E
Block Array
Size: 0000 0000 0000 000D   zmm31: 0000 000F 0000 000E   0000 000D 0000 000C   0000 000B 0000 FFF9   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 000D
element: 0000 0000 0000 000D
element: 0000 0000 0000 000C
element: 0000 0000 0000 000B
element: 0000 0000 0000 FFF9
element: 0000 0000 0000 0009
element: 0000 0000 0000 0008
element: 0000 0000 0000 0007
element: 0000 0000 0000 0006
element: 0000 0000 0000 0005
element: 0000 0000 0000 0004
element: 0000 0000 0000 0003
element: 0000 0000 0000 0002
element: 0000 0000 0000 0001
Block Array
Size: 0000 0000 0000 0000   zmm31: 0000 000F 0000 000E   0000 000D 0000 000C   0000 000B 0000 FFF9   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 0000
Block Array
Size: 0000 0000 0000 0026   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 00D8 0000 0098   0000 0058 0000 0026
Full: 0000 0000 0000 0058   zmm30: 0000 001E 0000 001C   0000 001A 0000 0018   0000 0016 0000 0014   0000 0012 0000 0010   0000 000E 0000 000C   0000 000A 0000 0008   0000 0006 0000 0004   0000 0002 0000 0000
Full: 0000 0000 0000 0098   zmm30: 0000 003E 0000 003C   0000 003A 0000 0038   0000 0036 0000 0034   0000 0032 0000 0030   0000 002E 0000 002C   0000 002A 0000 0028   0000 0026 0000 0024   0000 0022 0000 0020
Last: 0000 0000 0000 00D8   zmm30: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 004A 0000 0048   0000 0046 0000 0044   0000 0042 0000 0040
element: 0000 0000 0000 004A
element: 0000 0000 0000 0048
element: 0000 0000 0000 0046
element: 0000 0000 0000 0044
element: 0000 0000 0000 0042
element: 0000 0000 0000 0040
element: 0000 0000 0000 003E
element: 0000 0000 0000 003C
element: 0000 0000 0000 003A
element: 0000 0000 0000 0038
element: 0000 0000 0000 0036
element: 0000 0000 0000 0034
element: 0000 0000 0000 0032
element: 0000 0000 0000 0030
element: 0000 0000 0000 002E
element: 0000 0000 0000 002C
element: 0000 0000 0000 002A
element: 0000 0000 0000 0028
element: 0000 0000 0000 0026
element: 0000 0000 0000 0024
element: 0000 0000 0000 0022
element: 0000 0000 0000 0020
element: 0000 0000 0000 001E
element: 0000 0000 0000 001C
element: 0000 0000 0000 001A
element: 0000 0000 0000 0018
element: 0000 0000 0000 0016
element: 0000 0000 0000 0014
element: 0000 0000 0000 0012
element: 0000 0000 0000 0010
element: 0000 0000 0000 000E
element: 0000 0000 0000 000C
element: 0000 0000 0000 000A
element: 0000 0000 0000 0008
element: 0000 0000 0000 0006
element: 0000 0000 0000 0004
element: 0000 0000 0000 0002
element: 0000 0000 0000 0000
Block Array
Size: 0000 0000 0000 0000   zmm31: 0000 001C 0000 001A   0000 0018 0000 0016   0000 0014 0000 0012   0000 0010 0000 000E   0000 000C 0000 000A   0000 0008 0000 0006   0000 0004 0000 0002   0000 0000 0000 0000
END
 }
#exit if $develop;

#latest:;
if (1) {                                                                        #TNasm::X86::ByteString::allocBlock #TNasm::X86::ByteString::freeBlock
  my $a = CreateByteString;              $a->dump;
  $a->allocBlock(my $b1 = Vq(offset));   $a->dump;
  $a->allocBlock(my $b2 = Vq(offset));   $a->dump;
  $a->freeBlock($b2);                    $a->dump;
  $a->freeBlock($b1);                    $a->dump;

  ok Assemble(debug => 0, eq => <<END);
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0018
0000: 0010 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0058
0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

#latest:;

if (1) {                                                                        #TCreateBlockArray  #TBlockArray::push
  my $c = Rb(0..255);
  my $A = CreateByteString;  my $a = $A->CreateBlockArray;

  my sub put
   {my ($e) = @_;
    $a->push(element => Vq($e, $e));
   };

  my sub get
   {my ($i) = @_;                                                               # Parameters
    $a->get(my $v = Vq('index', $i), my $e = Vq(element));
    $v->out; PrintOutString "  "; $e->outNL;
   };

  put($_) for 1..15;  get(15);

  ok Assemble(debug => 2, eq => <<END);
Index out of bounds on get from array, Index: 0000 0000 0000 000F  Size: 0000 0000 0000 000F
END
 }

#latest:
if (1) {                                                                        #TExtern #TLink #TCallC
  my $format = Rs "Hello %s\n";
  my $data   = Rs "World";

  Extern qw(printf exit malloc strcpy); Link 'c';

  CallC 'malloc', length($format)+1;
  Mov r15, rax;
  CallC 'strcpy', r15, $format;
  CallC 'printf', r15, $data;
  CallC 'exit', 0;

  ok Assemble(eq => <<END);
Hello World
END
 }

latest:
if (1) {
  Mov rax, 0x77777701;
  Popcnt rax, rax;
  PrintOutRegisterInHex rax;

  ok Assemble(eq => <<END);
   rax: 0000 0000 0000 0013
END
 }

if (0) {
  is_deeply Assemble(debug=>1), <<END;
END
 }

unlink $_ for qw(hash print2 sde-log.txt sde-ptr-check.out.txt z.txt);          # Remove incidental files

lll "Finished:", time - $start,  "bytes assembled:",   totalBytesAssembled;
