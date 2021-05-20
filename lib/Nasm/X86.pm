#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I. -I/home/phil/perl/cpan/AsmC/lib/
#-------------------------------------------------------------------------------
# Generate Nasm X86 code from Perl.  v1
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation
package Nasm::X86;
our $VERSION = "20210514";
use warnings FATAL => qw(all);
use strict;
use Carp qw(confess cluck);
use Data::Dump qw(dump);
use Data::Table::Text qw(confirmHasCommandLineCommand currentDirectory fff fileSize findFiles fpe fpf genHash lll owf pad readFile stringsAreNotEqual);
use Asm::C qw(:all);
use feature qw(say current_sub);

# Parameter passing mechanism
# AllocateAll8OnStack - replace with variables
# Labels should be settable via $label->set
# Register expressions via op overloading - register size and ability to add offsets, peek, pop, push clear register
# Indent opcodes by call depth, - replace push @text with a method call

my %rodata;                                                                     # Read only data already written
my %rodatas;                                                                    # Read only string already written
my %subroutines;                                                                # Subroutines generated
my @rodata;                                                                     # Read only data
my @data;                                                                       # Data
my @bss;                                                                        # Block started by symbol
my @text;                                                                       # Code

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
or shl shr sub test tzcnt
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
  return $_ if $_ = $rodatas{$d};                                               # Data already exists so return it
  my $l = Label;
  $rodatas{$d} = $l;                                                            # Record label
  push @rodata, <<END;                                                          # Define bytes
  $l: db  '$d',0;
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
  $N * 1*RegisterSize(rax);                                                       # Space occupied by push
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

sub ForIn(&$$$$)                                                                # For - iterate the body as long as register plus increment is less than than limit incrementing by increment each time
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

my @subroutinesCreated = ('');                                                  # Number of subroutines created

sub S(&%)                                                                       # Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub
 {my ($body, %options) = @_;                                                    # Body, options.

  @_ >= 1 or confess;
  my $name = $options{name} // [caller(1)]->[3];                                # Optional name for subroutine reuse
  if ($name and !$options{keepOut} and my $n = $subroutines{$name}) {return $n} # Return the label of a pre-existing copy of the code
  push @subroutinesCreated, $name;
  my $start = Label;
  my $end   = Label;
  Jmp $end;
  SetLabel $start;
  &$body;
  Ret;
  SetLabel $end;
  $subroutines{$name} = $start if $name;                                        # Cache a reference to the generated code if a name was supplied
  pop @subroutinesCreated;

  $start
 }

sub S2(&%)                                                                      # Create a sub with a specified name, comment, in and out parameters
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
    confess "Invalid size $size for parameter: $name" unless $size =~ m(\A3\Z);
    $p{$name} = Vr($name);                                                      # Make a reference
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
confess unless $n;
    my $v = ref($p) ? $p       : shift @parameters;
    confess "Invalid parameter: '$n'" unless $sub->in->{$n} or $sub->out->{$n} or $sub->io->{$n};
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
   {confess "Missing output parameter: $p" unless my $v = $p{$p};
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

sub PrintErrNL()                                                                # Print a new line to stderr
 {@_ == 0 or confess;
  my $a = Rb(10);
  Comment "Write new line to stderr";

  Call S                                                                        # Print new line
   {SaveFirstFour;
    Mov rax, 1;
    Mov rdi, $stderr;
    Mov rsi, $a;
    Mov rdx, 1;
    Syscall;
    RestoreFirstFour()
   } name => q(PrintErrNL);
 }

sub PrintErrString($)                                                           # Print a constant string to stderr.
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess;

  SaveFirstFour;
  Comment "Write to stderr String: $string";
  my ($c) = @_;
  my $l = length($c);
  my $a = Rs($c);
  Mov rax, 1;
  Mov rdi, $stderr;
  Mov rsi, $a;
  Mov rdx, $l;
  Syscall;
  RestoreFirstFour();
 }

sub PrintErrStringNL($)                                                         # Print a new line to stderr
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess;
  PrintErrString  ($string);
  PrintErrNL;
 }

sub PrintOutNL()                                                                # Print a new line to stdout
 {@_ == 0 or confess;
  my $a = Rb(10);
  Comment "Write new line";

  Call S                                                                        # Print new line
   {SaveFirstFour;
    Mov rax, 1;
    Mov rdi, $stdout;
    Mov rsi, $a;
    Mov rdx, 1;
    Syscall;
    RestoreFirstFour()
   } name => q(PrintOutNL);
 }

sub PrintOutString($)                                                           # Print a constant string to sysout.
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess;

  SaveFirstFour;
  Comment "Write String: $string";
  my ($c) = @_;
  my $l = length($c);
  my $a = Rs($c);
  Mov rax, 1;
  Mov rdi, $stdout;
  Mov rsi, $a;
  Mov rdx, $l;
  Syscall;
  RestoreFirstFour();
 }

sub PrintOutStringNL($)                                                         # Print a constant string to sysout followed by new line
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess;
  PrintOutString  ($string);
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

sub PrintOutRaxInHex                                                            # Write the content of register rax to stderr in hexadecimal in big endian notation
 {@_ == 0 or confess;
  Comment "Print Rax In Hex";
  my $hexTranslateTable = hexTranslateTable;

  my $sub = S                                                                   # Address conversion routine
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
      PrintOutMemory;
      PrintOutString ' ' if $i % 2 and $i < 7;
     }
    RestoreFirstFour;
   } name => "PrintOutRaxInHex";

  Call $sub;
 }

sub PrintOutRaxInReverseInHex                                                   # Write the content of register rax to stderr in hexadecimal in little endian notation
 {@_ == 0 or confess;
  Comment "Print Rax In Reverse In Hex";
  Push rax;
  Bswap rax;
  PrintOutRaxInHex;
  Pop rax;
 }

sub PrintOutRegisterInHex(@)                                                    # Print any register as a hex string
 {my (@r) = @_;                                                                 # Name of the register to print

  for my $r(@r)                                                                 # Each register to print
   {Comment "Print register $r in Hex";

    Call S                                                                      # Reverse rax
     {PrintOutString sprintf("%6s: ", $r);

      my sub printReg(@)                                                        # Print the contents of a register
       {my (@regs) = @_;                                                        # Size in bytes, work registers
        my $s = RegisterSize $r;                                                # Size of the register
        PushR  @regs;                                                           # Save work registers
        PushRR $r;                                                              # Place register contents on stack - might be a x|y|z - without tracking
        PopRR  @regs;                                                           # Load work registers without tracking
        for my $i(keys @regs)                                                   # Print work registers to print input register
         {my $R = $regs[$i];
          if ($R !~ m(\Arax))
           {PrintOutString("  ");
            Keep $R; KeepFree rax;
            Mov rax, $R
           }
          PrintOutRaxInHex;                                                     # Print work register
          PrintOutString(" ") unless $i == $#regs;
         }
        PopR @regs;                                                             # Balance the single push of what might be a large register
       };
      if    ($r =~ m(\A[kr])) {printReg qw(rax)}                                # 64 bit register requested
      elsif ($r =~ m(\Ax))    {printReg qw(rax rbx)}                            # xmm*
      elsif ($r =~ m(\Ay))    {printReg qw(rax rbx rcx rdx)}                    # ymm*
      elsif ($r =~ m(\Az))    {printReg qw(rax rbx rcx rdx r8 r9 r10 r11)}      # zmm*

      PrintOutNL;
     } name => "PrintOutRegister${r}InHex";                                     # One routine per register printed
   }
 }

sub PrintOutRipInHex                                                            #P Print the instruction pointer in hex
 {@_ == 0 or confess;
  my @regs = qw(rax);
  my $sub = S
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

  my $sub = S
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

  my $sub = S
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
  my $s = genHash('Scope',                                                      # Scope definition
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

sub Scope::contains($;$)                                                        # Check that the named parent scope contains the specified child scope. If no child scope is supplied we use the current scope to check that the parent scope is currently visible
 {my ($parent, $child) = @_;                                                    # Parent scope, child scope,
  for(my $c = $child//$ScopeCurrent; $c; $c = $c->parent)                       # Ascend scope tree looking for parent
   {return 1 if $c == $parent;                                                  # Found parent so child or current scope can see the parent
   }
  undef                                                                         # Parent not found so child is not contained by the parent scope
 }

sub Scope::currentlyVisible($)                                                  # Check that the named parent scope is currently visible
 {my ($scope) = @_;                                                             # Scope to check for visibility
  $scope->contains                                                              # Check that the named parent scope is currently visible
 }

#D2 Definitions                                                                 # Variable definitions

sub Variable($$;$)                                                              # Create a new variable with the specified size and name initialized via an expression
 {my ($size, $name, $expr) = @_;                                                # Size as a power of 2, name of variable, optional expression initializing variable
  $size =~ m(\A0|1|2|3|4|5|6|b|w|d|q|x|y|z\Z)i or confess "Size must be 0..6 or b|w|d|q|x|y|z";  # Check size of variable

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

  genHash("Variable",                                                           # Variable definition
    expr      => $expr,                                                         # Expression that initializes the variable
    label     => $label,                                                        # Address in memory
    laneSize  => undef,                                                         # Size of the lanes in this variable
    name      => $name,                                                         # Name of the variable
    purpose   => undef,                                                         # Purpose of this variable
    reference => undef,                                                         # Reference to another variable
    saturate  => undef,                                                         # Computations should saturate rather then wrap if true
    scope     => $subroutinesCreated[-1],                                       # The number of the subroutine we were in when this variable was created
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
  if (@expr == 1 and $expr[0] =~ m(\Al))                                        # Load from the memory at the specifed labe;
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
 {my ($name, $ref) = @_;                                                        # Name of variable, variable being referenced
  my $r = &Variable(3, $name);
  $r->reference = 1;                                                            # Mark variable as a reference
  $r->expr      = $ref;                                                         # Show variable referenced as expr if the reference is known  yet
  $r
 }

#D2 Operations                                                                  # Variable operations

if (1)                                                                          # Define operator overloading for Variables
 {package Variable;
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

sub Variable::address($;$)                                                      # Get the address of a variable with an optional offset
 {my ($left, $offset) = @_;                                                     # Left variable, optional offset
  my $o = $offset ? "+$offset" : "";
  "[".$left-> label."$o]"
 }

sub Variable::copy($$)                                                          # Copy one variable into another
 {my ($left, $right) = @_;                                                      # Left variable, right variable

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

sub Variable::copyAddress($$)                                                   # Copy a reference to a variable
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

sub Variable::equals($$)                                                        # Equals operator
 {my ($op, $left, $right) = @_;                                                 # Operator, left variable,  right variable
  $op
 }


sub Variable::assign($$$)                                                       # Assign to the left hand side the value of the right hand side
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

sub Variable::plusAssign($$)                                                    # Implement plus and assign
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  $left->assign(\&Add, $right);
 }

sub Variable::minusAssign($$)                                                   # Implement minus and assign
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  $left->assign(\&Sub, $right);
 }

sub Variable::arithmetic($$$$)                                                  # Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables
 {my ($op, $name, $left, $right) = @_;                                          # Operator, operator name, Left variable,  right variable

  my $l = $left ->address;
  my $r = ref($right) ? $right->address : $right;                               # Right can be either a variable reference or a constant

  if ($left->size == 3 and !ref($right) || $right->size == 3)                   # Vq
   {PushR r15;
    Mov r15, $l;
    &$op(r15, $r);
    my $v = Vq(join(' ', '('.$left->name, $name, (ref($right) ? $right->name : $right).')'), r15);
    PopR r15;
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

sub Variable::add($$)                                                           # Add the right hand variable to the left hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::arithmetic(\&Add, q(add), $left, $right);
 }

sub Variable::sub($$)                                                           # Subtract the right hand variable from the left hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::arithmetic(\&Sub, q(sub), $left, $right);
 }

sub Variable::times($$)                                                         # Multiply the left hand variable by the right hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::arithmetic(\&Imul, q(times), $left, $right);
 }

sub Variable::division($$$)                                                     # Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side
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

sub Variable::divide($$)                                                        # Divide the left hand variable by the right hand variable and return the result as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::division("/", $left, $right);
 }

sub Variable::mod($$)                                                           # Divide the left hand variable by the right hand variable and return the remainder as a new variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::division("%", $left, $right);
 }

sub Variable::boolean($$$$)                                                     # Combine the left hand variable with the right hand variable via a boolean operator
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

sub Variable::eq($$)                                                            # Check whether the left hand variable is equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::boolean(\&IfEq, q(eq), $left, $right);
 }

sub Variable::ne($$)                                                            # Check whether the left hand variable is not equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::boolean(\&IfNe, q(ne), $left, $right);
 }

sub Variable::ge($$)                                                            # Check whether the left hand variable is greater than or equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::boolean(\&IfGe, q(ge), $left, $right);
 }

sub Variable::gt($$)                                                            # Check whether the left hand variable is greater than the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::boolean(\&IfGt, q(gt), $left, $right);
 }

sub Variable::le($$)                                                            # Check whether the left hand variable is less than or equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::boolean(\&IfLe, q(le), $left, $right);
 }

sub Variable::lt($$)                                                            # Check whether the left hand variable is less than the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Variable::boolean(\&IfLt, q(lt), $left, $right);
 }

sub Variable::print($)                                                          # Write the value of a variable on stdout
 {my ($left) = @_;                                                              # Left variable
  PushR my @regs = (rax, rdi);
  Mov rax, $left->label;
  Mov rdi, 8;
  &PrintOutMemoryInHexNL();
  PopR @regs;
 }

sub Variable::dump($;$)                                                         # Dump the value of a variable on stdout
 {my ($left, $title) = @_;                                                      # Left variable, optional title
  if ($left->size == 3)                                                         # General purpose register
   {PushR my @regs = (rax, rdi);
    Mov rax, $left->label;                                                      # Address in memory
    KeepFree rax;
    Mov rax, "[rax]";
    &PrintOutString($title//$left->name.": ");
    &PrintOutRaxInHex();
    &PrintOutNL();
    PopR @regs;
   }
  elsif ($left->size == 4)                                                      # xmm
   {PushR my @regs = (rax, rdi);
    my $l = $left->label;                                                       # Address in memory
    my $s = RegisterSize rax;
    Mov rax, "[$l]";
    Mov rdi, "[$l+$s]";
    &PrintOutString($title//$left->name.": ");
    &PrintOutRaxInHex();
    &PrintOutString("  ");
    KeepFree rax;
    Mov rax, rdi;
    &PrintOutRaxInHex();
    &PrintOutNL();
    PopR @regs;
   }
 }

sub Variable::debug($)                                                          # Dump the value of a variable on stdout with an indication of where the dump came from
 {my ($left) = @_;                                                              # Left variable
  PushR my @regs = (rax, rdi);
  Mov rax, $left->label;                                                        # Address in memory
  KeepFree rax;
  Mov rax, "[rax]";
  &PrintOutString(pad($left->name, 32).": ");
  &PrintOutRaxInHex();
  my ($p, $f, $l) = caller(0);                                                  # Position of caller in file
  &PrintOutString("               at $f line $l");
  &PrintOutNL();
  PopR @regs;
 }

sub Variable::checkScopeOfCreatingSubroutine($)                                 #P Check that this variable is in scope: a subroutine that has been called rather than inserted might refer to the wrong variable unless the scopes match.
 {my ($variable) = @_;                                                          # Variable to check
  my $m = 'Variable: "'.$variable->name                                         # Check that the variable was created in the same scope
        .'" does not belong to this subroutine.'."\n"
        . 'Variable created in scope: '. $variable->scope."\n"
        . 'Current scope is: '.          dump(\@subroutinesCreated)."\n";
  confess $m  if $variable->scope ne $subroutinesCreated[-1];
  }

sub Variable::isRef($)                                                          # Check whether the specified  variable is a reference to another variable
 {my ($variable) = @_;                                                          # Variable
  my $n = $variable->name;                                                      # Variable name
  $variable->size == 3 or confess "Wrong size for reference: $n";
  $variable->reference
 }

sub Variable::setReg($$@)                                                       # Set the named registers from the content of the variable
 {my ($variable, $register, @registers) = @_;                                   # Variable, register to load, optional further registers to load
# $variable->checkScopeOfCreatingSubroutine;
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

sub Variable::getReg($$@)                                                       # Load the variable from the named registers
 {my ($variable, $register, @registers) = @_;                                   # Variable, register to load, optional further registers to load from
#  $variable->checkScopeOfCreatingSubroutine;
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

sub Variable::incDec($$)                                                        # Increment or decrement a variable
 {my ($left, $op) = @_;                                                         # Left variable operator, address of operator to perform inc or dec
  my $l = $left ->address;
  if ($left->size == 3)
   {PushRR r15;
    Mov r15, $l;
    &$op(r15);
    Mov $l, r15;
    PopRR r15;
    return $left;
   }
  confess "Need more code";
 }

sub Variable::inc($)                                                            # Increment a variable
 {my ($left) = @_;                                                              # Variable
  $left->Variable::incDec(\&Inc);
 }

sub Variable::dec($)                                                            # Decrement a variable
 {my ($left) = @_;                                                              # Variable
  $left->Variable::incDec(\&Dec);
 }

sub Variable::str($)                                                            # The name of the variable
 {my ($left) = @_;                                                              # Variable
  $left->name;
 }

sub Variable::min($$)                                                           # Minimum of two variables
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

sub Variable::max($$)                                                           # Maximum of two variables
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

sub Variable::and($$)                                                           # And two variables
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushRR my @save = (r14, r15);
  Mov r14, 0;
  $left->setReg(r15);
  Cmp r15, 0;
  &IfNe (
    sub
     {$right->setReg(r15);
      Cmp r15, 0;
      &IfNe(sub {Mov r14, 1});
     }
   );
  my $r = Vq("And(".$left->name.", ".$right->name.")", r14);
  PopRR @save;
  $r
 }

sub Variable::or($$)                                                            # Or two variables
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushRR my @save = (r14, r15);
  Mov r14, 1;
  $left->setReg(r15);
  Cmp r15, 0;
  &IfEq (
    sub
     {$right->setReg(r15);
      Cmp r15, 0;
      &IfEq(sub {Mov r14, 0});
     }
   );
  my $r = Vq("Or(".$left->name.", ".$right->name.")", r14);
  PopRR @save;
  $r
 }

sub Variable::setMask($$$)                                                      # Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere
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

sub Variable::setZmm($$$$)                                                      # Load bytes from the memory addressed by specified source variable into the numbered zmm register at the offset in the specified offset moving the number of bytes in the specified variable
 {my ($source, $zmm, $offset, $length) = @_;                                    # Variable containing the address of the source, number of zmm to load, variable containing offset in zmm to move to, variable containing length of move
  @_ == 4 or confess;
  ref($offset) && ref($length) or confess "Missing variable";                   # Need variables of offset and length
  Comment "Set Zmm $zmm from Memory";
  PushR my @save = (k7, r14, r15);
  $offset->setMask($length, k7);                                                # Set mask for target
  $source->setReg(r15);
  Sub r15, $offset->setReg(r14);                                                # Position memory for target
  Vmovdqu8 "zmm${zmm}{k7}", "[r15]";                                            # Read from memory
  PopR @save;
 }

sub Variable::loadZmm($$)                                                       # Load bytes from the memory addressed by the specified source variable into the numbered zmm register.
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

sub Variable::saveZmm($$)                                                       # Save bytes into the memory addressed by the target variable from the numbered zmm register.
 {my ($target, $zmm) = @_;                                                      # Variable containing the address of the source, number of zmm to put
  @_ == 2 or confess;
  Comment "Save zmm$zmm into memory addressed by ".$target->name;
  PushR r15;
  $target->setReg(r15);
  Vmovdqu8 "[r15]", "zmm$zmm";                                                  # Write into memory
  PopR r15;
 }

sub getBwdqFromZmmAsVariable($$$)                                               # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 {my ($size, $zmm, $offset) = @_;                                               # Size of get, Numbered zmm, offset in bytes
  @_ == 3 or confess;
  Comment "Get $size word from $offset in zmm $zmm";
  PushR r15;
  PushRR "zmm$zmm";                                                             # Push zmm
  Mov r15b, "[rsp+$offset]" if $size =~ m(b);                                   # Load byte register from offset
  Mov r15w, "[rsp+$offset]" if $size =~ m(w);                                   # Load word register from offset
  Mov r15d, "[rsp+$offset]" if $size =~ m(d);                                   # Load double word register from offset
  Mov r15,  "[rsp+$offset]" if $size =~ m(q);                                   # Load register from offset
  Add rsp, RegisterSize "zmm$zmm";                                              # Pop zmm
  my $v = Vq("$size at offset $offset in zmm$zmm", r15);                        # Create variable
  PopR r15;
  $v                                                                            # Return variable
 }

sub getBFromZmmAsVariable($$)                                                   # Get the byte from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromZmmAsVariable('b', $zmm, $offset)                                  # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getWFromZmmAsVariable($$)                                                   # Get the word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromZmmAsVariable('w', $zmm, $offset)                                  # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getDFromZmmAsVariable($$)                                                   # Get the double word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromZmmAsVariable('d', $zmm, $offset)                                  # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getQFromZmmAsVariable($$)                                                   # Get the quad word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Size of get, Numbered zmm, offset in bytes
  getBwdqFromZmmAsVariable('q', $zmm, $offset)                                  # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub Variable::putBwdqIntoZmm($$)                                                # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 {my ($content, $size, $zmm, $offset) = @_;                                     # Variable with content, size of put, numbered zmm, offset in bytes
  @_ == 4 or confess;
  Comment "Put $size at $offset in zmm $zmm";
  PushR my @save=(r15, "zmm$zmm");                                              # Push zmm
  $content->setReg(r15);
  Mov   "[rsp+$offset]", r15b if $size =~ m(b);                                 # Write byte register
  Mov   "[rsp+$offset]", r15w if $size =~ m(w);                                 # Write word register
  Mov   "[rsp+$offset]", r15d if $size =~ m(d);                                 # Write double word register
  Mov   "[rsp+$offset]", r15  if $size =~ m(q);                                 # Write register
  PopR @save;
 }

sub Variable::putBIntoZmm($$)                                                   # Place the value of the content variable at the byte in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $content->putBwdqIntoZmm('b', $zmm, $offset)                                  # Place the value of the content variable at the word in the numbered zmm register
 }

sub Variable::putWIntoZmm($$)                                                   # Place the value of the content variable at the word in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $content->putBwdqIntoZmm('w', $zmm, $offset)                                  # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Variable::putDIntoZmm($$)                                                   # Place the value of the content variable at the double word in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $content->putBwdqIntoZmm('d', $zmm, $offset)                                  # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Variable::putQIntoZmm($$)                                                   # Place the value of the content variable at the quad word in the numbered zmm register
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  $content->putBwdqIntoZmm('q', $zmm, $offset)                                  # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Variable::confirmIsMemory($;$$)                                             #P Check that variable describes allocated memory and optionally load registers with its length and size
 {my ($memory, $address, $length) = @_;                                         # Variable describing memory as returned by AllocateMemory, register to contain address, register to contain size
  $memory->size == 4 or confess "Wrong size";
  $memory->purpose =~ m(\AAllocated memory\Z) or confess "Not a memory allocator";
  my $l = $memory->label;
  my $s = RegisterSize rax;
  Mov $address, "[$l]" if $address;                                             # Optionally load address
  Mov $length,  "[$l+$s]" if $length;                                           # Optionally load length
 }

sub Variable::clearMemory($)                                                    # Clear the memory described in this variable
 {my ($memory) = @_;                                                            # Variable describing memory as returned by AllocateMemory
  PushR my @save = (rax, rdi);
  $memory->confirmIsMemory(@save);
  &ClearMemory();                                                               # Clear the memory
  PopR @save;
 }

sub Variable::copyMemoryFrom($$)                                                # Copy from one block of memory to another
 {my ($target, $source) = @_;                                                   # Variable describing the target, variable describing the source
  SaveFirstFour;
  $target->confirmIsMemory(rax, rdx);
  $source->confirmIsMemory(rsi, rdi);

  Cmp rdx, rdi;
  IfLt {PrintErrStringNL "Copy memory source is larger than target"; Exit(1)};  # Check memory sizes
  &CopyMemory();                                                                # Copy the memory
  RestoreFirstFour;
 }

sub Variable::printOutMemoryInHex($)                                            # Print allocated memory in hex
 {my ($memory) = @_;                                                            # Variable describing the memory
  PushR my @save = (rax, rdi);
  $memory->confirmIsMemory(@save);
  &PrintOutMemoryInHexNL();                                                     # Print the memory
  PopR @save;
 }

sub Variable::freeMemory($)                                                     # Free the memory described in this variable
 {my ($memory) = @_;                                                            # Variable describing memory as returned by AllocateMemory
  $memory->size == 4 or confess "Wrong size";
  $memory->purpose =~ m(\AAllocated memory\Z) or confess "Not a memory allocator";
  PushR my @save = (rax, rdi);
  my $l = $memory->label;
  my $s = RegisterSize rax;
  Mov rax, "[$l]";
  Mov rdi, "[$l+$s]";
  &FreeMemory();                                                                # Free the memory
  PopR @save;
 }

sub Variable::for($&)                                                           # Iterate the body from 0 limit times.
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

  my $sub = S                                                                   # Address conversion routine
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

  my $sub = S                                                                   # Wait pid
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

  my $sub = S                                                                   # Read time stamp
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

sub PushRR(@)                                                                   # Push registers onto the stack without tracking
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

sub PushR(@)                                                                    # Push registers onto the stack
 {my (@r) = @_;                                                                 # Register
  PushRR   @r;                                                                  # Push
  KeepPush @r;                                                                  # Track
 }

sub PopRR(@)                                                                    # Pop registers from the stack without tracking
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
  my $local = genHash("Structure",
    size      => 0,
    variables => [],
   );
 }

sub Structure::field($$;$)                                                      # Add a field of the specified length with an optional comment
 {my ($structure, $length, $comment) = @_;                                      # Structure data descriptor, length of data, optional comment
  @_ >= 2 or confess;
  my $variable = genHash("StructureField",
    structure  => $structure,
    loc        => $structure->size,
    size       => $length,
    comment    => $comment
   );
  $structure->size += $length;                                                  # Update size of local data
  push $structure->variables->@*, $variable;                                    # Save variable
  $variable
 }

sub StructureField::addr($;$)                                                   # Address a field in a structure by either the default register or the named register
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
  my $local = genHash("LocalData",
    size      => 0,
    variables => [],
   );
 }

sub LocalData::start($)                                                         # Start a local data area on the stack
 {my ($local) = @_;                                                             # Local data descriptor
  @_ == 1 or confess;
  my $size = $local->size;                                                      # Size of local data
  Push rbp;
  Mov rbp,rsp;
  Sub rsp, $size;
 }

sub LocalData::free($)                                                          # Free a local data area on the stack
 {my ($local) = @_;                                                             # Local data descriptor
  @_ == 1 or confess;
  Mov rsp,rbp;
  Pop rbp;
 }

sub LocalData::variable($$;$)                                                   # Add a local variable
 {my ($local, $length, $comment) = @_;                                          # Local data descriptor, length of data, optional comment
  @_ >= 2 or confess;
  my $variable = genHash("LocalVariable",
    loc        => $local->size,
    size       => $length,
    comment    => $comment
   );
  $local->size += $length;                                                      # Update size of local data
  $variable
 }

sub LocalVariable::stack($)                                                     # Address a local variable on the stack
 {my ($variable) = @_;                                                          # Variable
  @_ == 1 or confess;
  my $l = $variable->loc;                                                       # Location of variable on stack
  my $S = $variable->size;
  my $s = $S == 8 ? 'qword' : $S == 4 ? 'dword' : $S == 2 ? 'word' : 'byte';    # Variable size
  "${s}[rbp-$l]"                                                                # Address variable - offsets are negative per Tino
 }

sub LocalData::allocate8($@)                                                    # Add some 8 byte local variables and return an array of variable definitions
 {my ($local, @comments) = @_;                                                  # Local data descriptor, optional comment
  my @v;
  for my $c(@comments)
   {push @v, LocalData::variable($local, 8, $c);
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

sub PrintOutMemoryInHex                                                         # Dump memory from the address in rax for the length in rdi
 {@_ == 0 or confess;
  Comment "Print out memory in hex";

  Call S
   {my $size = RegisterSize rax;
    SaveFirstFour;
    Mov rsi,rax;                                                                # Position in memory
    Lea rdi,"[rax+rdi-$size+1]";                                                # Upper limit of printing with an 8 byte register
    For                                                                         # Print string in blocks
     {Mov rax, "[rsi]";
      Bswap rax;
      PrintOutRaxInHex;
     } rsi, rdi, $size;
    RestoreFirstFour;
   } name=> "PrintOutMemoryInHex";
 }

sub PrintOutMemoryInHexNL                                                       # Dump memory from the address in rax for the length in rdi and then print a new line
 {@_ == 0 or confess;
  Comment "Print out memory in hex then new line";
  PrintOutMemoryInHex;
  PrintOutNL;
 }

sub PrintOutMemory                                                              # Print the memory addressed by rax for a length of rdi
 {@_ == 0 or confess;

  Call S
   {Comment "Print memory";
    SaveFirstFour rax, rdi;
    Mov rsi, rax;
    Mov rdx, rdi;
    KeepFree rax, rdi;
    Mov rax, 1;
    Mov rdi, $stdout;
    Syscall;
    RestoreFirstFour();
   } name => "PrintOutMemory";
 }

sub PrintOutMemoryNL                                                            # Print the memory addressed by rax for a length of rdi followed by a new line
 {@_ == 0 or confess;
  Comment "Print out memory then new line";
  PrintOutMemory;
  PrintOutNL;
 }

sub AllocateMemory                                                              # Allocate the specified amount of memory via mmap and return its address
 {@_ == 0 or confess;

  S2
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
   } in=>{size=>3}, out=>{address=>3};
 }

sub FreeMemory                                                                  # Free memory
 {@_ == 0 or confess;
  Comment "Free memory";

  S2
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    Mov rax, 11;                                                                # Munmap
    $$p{address}->setReg(rdi);                                                  # Address
    $$p{size}   ->setReg(rsi);                                                  # Length
    Syscall;
    RestoreFirstFour;
   } in => {size=>3, address=>3};
 }

sub ClearMemory()                                                               # Clear memory - the address of the memory is in rax, the length in rdi
 {@_ == 0 or confess;
  Comment "Clear memory";

  my $size = RegisterSize zmm0;

  S2
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
 }

sub CopyMemory()                                                                # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
 {@_ == 0 or confess;

  S2
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

    For                                                                           # Clear memory
     {Mov "r8b", "[$source+$copied]";
      Mov "[$target+$copied]", "r8b";
     } $copied, $length, 1;

    RestoreFirstSeven;
   } in => {source => 3, target => 3, size => 3};
 }

#D1 Files                                                                       # Process a file

sub OpenRead()                                                                  # Open a file, whose name is addressed by rax, for read and return the file descriptor in rax
 {@_ == 0 or confess;
  Comment "Open a file for read";

  my $sub = S
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

  my $sub = S                                                                   # Open file
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

  my $sub = S                                                                   # Open file
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

  my $sub = S                                                                   # Stat file
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

sub ReadFile()                                                                  # Read a file whose name is addressed by rax into memory.  The address of the mapped memory and its length are returned in registers rax,rdi
 {@_ == 0 or confess;

  S2                                                                            # Read file
   {my ($parameters) = @_;
    Comment "Read a file into memory";
    SaveFirstSeven;                                                             # Generated code
    my ($local, $file, $addr, $size, $fdes) = AllocateAll8OnStack 4;            # Local data

    $$parameters{file}->setReg(rax);                                            # File name

    StatSize;                                                                   # File size
    Mov $size, rax;                                                             # Save file size
    KeepFree rax;

    $$parameters{file}->setReg(rax);                                            # File name
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
    RestoreFirstSevenExceptRaxAndRdi;
   } in=>{file => 3};
 }

#D1 Short Strings                                                               # Operations on Short Strings

sub LoadShortStringFromMemoryToZmm2($)                                           # Load the short string addressed by rax into the zmm register with the specified number
 {my ($zmm) = @_;                                                               # Zmm register to load
  @_ == 1 or confess;

  my $sub = S                                                                   # Read file
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

  my $sub = S                                                                   # Read file
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

  my $sub = S                                                                   # Read file
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

  my $sub  = S                                                                  # Create byte string
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

  my $s = S2
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;

    AllocateMemory->call($N, address=>$$p{bs});                                 # Allocate memory and save its location in a variable

    $$p{bs}->setReg(rax);
    $N     ->setReg(rdx);
    Mov rdi, $string->size;                                                     # Size of byte string base structure which is constant
    Mov $used->addr, rdi;                                                       # Used space
    Mov $size->addr, rdx;                                                       # Size

    RestoreFirstFour;
   } out => {bs => 3};

  $s->call(my $bs = Vq(bs));

  genHash("ByteString",                                                         # Definition of byte string
    structure => $string,                                                       # Structure details
    size      => $size,                                                         # Size field details
    used      => $used,                                                         # Used field details
    data      => $data,                                                         # The first 8 bytes of the data
    bs        => $bs,                                                           # Variable that address the bytes string
   );
 }

sub ByteString::updateSpace($)                                                  #P Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi
 {my ($byteString) = @_;                                                        # Byte string descriptor
  my $size = $byteString->size->addr;
  my $used = $byteString->used->addr;

  S2                                                                            # Allocate more space if required
   {my ($p) = @_;                                                               #
    Comment "Allocate more space for a byte string";
    SaveFirstFour;
    $$p{bs}->setReg(rax);                                                       # Address byte string
    Mov rdx, $byteString->used->addr;                                           # Used
    $$p{size}->setReg(rdi);                                                     # Length required
    Add rdx, rdi;                                                               # Wanted
    Cmp rdx, $size;                                                             # Space needed versus actual size
    KeepFree rdi, rdx;

    IfGt                                                                        # More space needed
     {Mov rsi, rax;                                                             # Old byte string
      KeepFree rax;

      Mov rdi, $size;                                                           # Old byte string size
      Mov rax, rdi;                                                             # Old byte string length

      my $double = SetLabel Label;                                              # Keep doubling until we have a string area that is big enough to hold the new data
      Shl rax, 1;                                                               # New byte string size - double the size of the old byte string
      Cmp rax, rdx;                                                             # Big enough ?
      Jl $double;                                                               # Still too low
      $$p{size}->getReg(rdx);

      Mov rdx, rax;                                                             # Save new byte string size
      AllocateMemory;                                                           # Create new byte string
      $$p{bs}->getReg(rax);

      CopyMemory;                                                               # Copy old byte string into new byte string
      Mov $size, rdx;                                                           # rdx can be reused now we have saved the size of the new bye string

      PushR rax;                                                                # Free old byte string
      Mov rax, rsi;                                                             # Old byte string
      FreeMemory;
      PopR rax;
     };
    RestoreFirstFour;
   } io => {bs=>3}, in=>{size=>3};
 }

sub ByteString::makeReadOnly($)                                                 # Make a byte string read only
 {my ($byteString) = @_;                                                        # Byte string descriptor

  S2                                                                            # Read file
   {my ($parameters) = @_;                                                      #
    Comment "Make a byte string readable";
    SaveFirstFour;
    $$parameters{bs}->setReg(rax);
    Mov rdi, rax;                                                               # Address of byte string
    Mov rsi, $byteString->size->addr;                                           # Size of byte string
    Mov rdx, 1;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded byte string
   } in => {bs => $byteString};
 }

sub ByteString::makeWriteable($)                                                # Make a byte string writable
 {my ($byteString) = @_;                                                        # Byte string descriptor

  S2                                                                            # Read file
   {my ($parameters) = @_;                                                      #
    Comment "Make a byte string writable";
    SaveFirstFour;
    $$parameters{bs}->setReg(rax);
    Mov rdi, rax;                                                               # Address of byte string
    Mov rsi, $byteString->size->addr;                                           # Size of byte string
    Mov rdx, 3;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded byte string
   } in => {bs => $byteString};
 }

sub ByteString::allocate($)                                                     # Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi
 {my ($byteString) = @_;                                                        # Byte string descriptor
  my $used   = rdx;                                                             # Register used to calculate how much of the byte string has been used
  my $offset = rsi;                                                             # Register used to hold current offset

  S2                                                                            # Allocate space
   {my ($parameters) = @_;                                                      #
    Comment "Allocate space in a byte string";
    SaveFirstFour;

    $byteString->updateSpace->call($$parameters{bs}, $$parameters{size});       # Update space if needed
    $$parameters{bs}  ->setReg(rax);
    $$parameters{size}->setReg(rdi);
    Mov $used, $byteString->used->addr;                                         # Currently used
    Mov $offset, $used;                                                         # Current offset
    Add $used, rdi;                                                             # Add the requested length to get the amount now used
    Mov $byteString->used->addr, $used;
    Mov rdi, $offset;
    Add rdi, $byteString->structure->size;                                      # This is the offset from the start of the byte string - which means that it will never be less than 16
    $$parameters{offset}->getReg(rdi);

    RestoreFirstFour;
   } in => {bs => 3, size => 3}, out => {offset => 3};
 }

sub ByteString::m($)                                                            # Append the content with length rdi addressed by rsi to the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor
  my $used = $byteString->used->addr;
  my $target = rdx;                                                             # Register that addresses target of move
  my $length = rdx;                                                             # Register used to update used field

  S2                                                                            # Append content
   {my ($p) = @_;                                                               # Parameters
    Comment "Append memory to a byte string";
    $byteString->updateSpace->call($$p{bs}, $$p{size});                         # Update space if needed

    SaveFirstFour;
    $$p{bs}     ->setReg(rax);
    $$p{size}   ->setReg(rdi);
    $$p{address}->setReg(rsi);
#   Lea $target, $byteString->data->addr;                                       # Address of data field
    Mov $target, rax;
    Add $target, $used;                                                         # Skip over used data

    PushR rax;         ## Probably not needed                                                         # Save address of byte string
    Mov rax, $target;                                                           # Address target
    CopyMemory->call(source=>$$p{address}, size=>$$p{size}, target=>Vq(target,$target));                                                                 # Move data in
    PopR rax;                                                                   # Restore address of byte string

    KeepFree $length;
    Mov $length, $used;                                                         # Update used field
    Add $length, rdi;
    Mov $used,   $length;

    RestoreFirstFour;
   } io => { bs => 3}, in => {address => 3, size => 3};
 }

sub ByteString::q($$)                                                           # Append a constant string to the byte string
 {my ($byteString, $string) = @_;                                               # Byte string descriptor, string

  my $s = Rs($string);

  my $bs = $byteString->bs;                                                     # Move data
  my $ad = Vq(address, $s);
  my $sz = Vq(size, length($string));
  $byteString->m->call($bs, $ad, $sz);
 }

#sub ByteString::ql($$$)                                                         # Append a quoted string containing new line characters to the byte string addressed by rax
# {my ($byteString, $bs, $const) = @_;                                           # Byte string descriptor, byte string, constant
#  my @l = split /\s*\n/, $const;
#  for my $l(@l)
#   {$byteString->q->call(bs, ($l);
#    $byteString->nl;
#   }
# }

sub ByteString::char($$$)                                                       # Append a character expressed as a decimal number to the byte string addressed by rax
 {my ($byteString, $bs, $char) = @_;                                            # Byte string descriptor, var byte string, decimal number of character to be appended
  PushR rax;
  Mov al, $char;
  $byteString->m->call($bs, Vq(string, rax), Vq(size, 1));                      # Move data
  PopR rax;
 }

sub ByteString::nl($$)                                                          # Append a new line to the byte string addressed by rax
 {my ($byteString, $bs) = @_;                                                   # Byte string descriptor, var byte string
  $byteString->char($bs, ord("\n"));
 }

sub ByteString::z($$)                                                           # Append a trailing zero to the byte string addressed by rax
 {my ($byteString, $bs) = @_;                                                   # Byte string descriptor, var byte string
  $byteString->char($bs, 0);
 }

sub ByteString::rdiInHex                                                        # Add the content of register rdi in hexadecimal in big endian notation to a byte string
 {my ($byteString) = @_;                                                        # Byte string descriptor

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

sub ByteString::append($)                                                       # Append one byte string to another
 {my ($byteString) = @_;                                                        # Byte string descriptor, var target byte string, var source byte string

  S2
   {my ($p) = @_;                                                               # Parameters
    Comment "Concatenate byte strings";
    SaveFirstFour;
    $$p{source}->setReg(rax);
    Mov rdi, $byteString->used->addr;
    Sub rdi, $byteString->structure->size;
    Lea rsi, $byteString->data->addr;
    $byteString->m->call(bs=>$$p{target}, Vq(address, rsi), Vq(size, rdi));
    RestoreFirstFour;
   } in => {target=>3, source=>3};
 }

sub ByteString::clear($)                                                        # Clear the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor, var byte string

  PushR my @save = (rax, rdi);
  $byteString->bs->setReg(rax);
  Mov rdi, $byteString->structure->size;
  Mov $byteString->used->addr, rdi;
  PopR     @save;
 }

sub ByteString::write($$)                                                       # Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file
 {my ($byteString, $bs) = @_;                                                   # Byte string descriptor, var byte string
  my $FileNameSize = 12;                                                        # Size of the temporary file name

  S2                                                                            # Copy byte string
   {my ($p) = @_;                                                               # Parameters
    Comment "Write a byte string to a temporary file";
    SaveFirstSeven;
    $$p{bs}->setReg(rax);

    my $string = r8;                                                            # Byte string
    my $file   = r9;                                                            # File descriptor

    Mov $string, rax;                                                           # Save address of byte string

    GetPidInHex;                                                                # Name of file
    Push rax;
    if (1)
     {my @c = split //, "atmpat";
      while(@c)
       {my $a = pop @c; my $b = pop @c;
        my $x = sprintf("%x%x", ord($a), ord($b));
        KeepFree rax;
        Mov rax, "0x$x";
        Push ax;
       }
     }

    KeepFree rax;
    Mov rax, rsp;                                                               # Address file name
    OpenWrite;                                                                  # Create a temporary file
    Mov $file, rax;                                                             # File descriptor

    KeepFree rax;
    Mov rax, 1;                                                                 # Write content to file
    Mov rdi, $file;
    Lea rsi, $byteString->data->addr($string);
    Mov rdx, $byteString->used->addr($string);
    Syscall;
    KeepFree rax, rdi;

    Mov rax, $string;                                                           # Clear string and add file name
    $byteString->clear->call($bs);
    KeepFree rax;

    Mov rax, $string;                                                           # Put file name in byte string
    Mov rsi, rsp;
    Mov rdi, 1+$FileNameSize;                                                   # File name size plus one trailing zero
    $byteString->m;
    Add rsp, 2+$FileNameSize;                                                   # File name size plus two trailing zeros
    KeepFree rax;

    Mov rax, $file;
    CloseFile;
    RestoreFirstSeven;
   }  in => {bs=>3};
 }

sub ByteString::read($)                                                         # Read the file named in the byte string (terminated with a zero byte) addressed by rax and place it into the byte string after clearing the byte string to remove the file name contained therein.
 {my ($byteString) = @_;                                                        # Byte string descriptor

  PushR rax;                                                                    # Get address of byte string
  $byteString->address->setReg(rax);

# Call S                                                                        # Copy byte string
   {Comment "Read a byte string";
    SaveFirstFour;
    Mov rdx, rax;                                                               # Save address of byte string
    Lea rax, $byteString->data->addr;                                           # Address file name with rax
    ReadFile;                                                                   # Read the file named by rax
    Mov rsi, rax;                                                               # Address of content in rax, length of content in rdi
    KeepFree rax;
    Mov rax, rdx;                                                               # Address of byte string
    $byteString->clear;                                                         # Remove file name in byte string
    $byteString->m;                                                             # Move data into byte string
    PushR rax;                                                                  # We might have a new byte string by now
    Mov rax, rsi;                                                               # File data
    FreeMemory;                                                                 # Address of allocated memory in rax, length in rdi
    PopR rax;                                                                   # Address byte string
    RestoreFirstFour;
   }# name => "ByteString::read";

  PopR rax;
 }

sub ByteString::out($)                                                          # Print the specified byte string addressed by rax on sysout
 {my ($byteString) = @_;                                                        # Byte string descriptor
  SaveFirstFour;
  $byteString->bs->setReg(rax);
  Mov rdi, $byteString->used->addr;                                             # Length to print
  Sub rdi, $byteString->structure->size;                                       # Length to print
  Lea rax, $byteString->data->addr;                                             # Address of data field
  PrintOutMemory;
  RestoreFirstFour;
 }

sub ByteString::bash($)                                                         # Execute the file named in the byte string addressed by rax with bash
 {my ($byteString) = @_;                                                        # Byte string descriptor

  PushR rax;                                                                    # Get address of byte string
  $byteString->address->setReg(rax);

  Call S                                                                        # Bash string
   {Comment "Execute a byte string via bash";
    SaveFirstFour;
    Mov rdx, rax;                                                               # Save byte string address
    Fork;                                                                       # Fork

    Test rax,rax;

    IfNz                                                                        # Parent
     {WaitPid;
     }
    sub                                                                         # Child
     {KeepFree rax;
      Mov rax, rdx;                                                             # Restore address of byte string
      KeepFree rdx;
      Lea rdi, $byteString->data->addr;
      KeepFree rax;
      Mov rsi, 0;
      Mov rdx, 0;
      Mov rax, 59;
      Syscall;
     };
    RestoreFirstFour;
   } name => "ByteString::bash";

  PopR rax;
 }

sub ByteString::unlink($)                                                       # Unlink the file named in the byte string addressed by rax with bash
 {my ($byteString) = @_;                                                        # Byte string descriptor

  PushR rax;                                                                    # Get address of byte string
  $byteString->address->setReg(rax);

  Call S                                                                        # Bash string
   {Comment "Unlink a file named in a byte string";
    SaveFirstFour;
    Lea rdi, $byteString->data->addr;
    Mov rax, 87;
    Syscall;
    RestoreFirstFour;
   } name => "ByteString::unlink";

  PopR rax;
 }

sub ByteString::dump($)                                                         # Dump details of a byte string
 {my ($byteString) = @_;                                                        # Byte string descriptor

  PushR rax;                                                                    # Get address of byte string
  $byteString->address->setReg(rax);

  Call S                                                                        # Bash string
   {Comment "Print details of a byte string";
    SaveFirstFour;
    PrintOutStringNL("Byte String");

    PushR rax;                                                                   # Print size
    Mov rax, $byteString->size->addr;
    PrintOutString("  Size: ");
    PrintOutRaxInHex;
    PrintOutNL;
    PopR rax;

    PushR rax;                                                                   # Print used
    Mov rax, $byteString->used->addr;
    PrintOutString("  Used: ");
    PrintOutRaxInHex;
    PrintOutNL;
    PopR rax;
    RestoreFirstFour;
   } name => "ByteString::dump";

  PopR rax;
 }

#D1 Block Strings                                                               # Strings made from zmm sized blocks of text

sub ByteString::CreateBlockString($)                                            # Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the byte string addressed by rax and return its descriptor
 {my ($byteString) = @_;                                                        # Byte string description
  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  Comment "Allocate a new block string in a byte string";

  my $s = genHash(q(BlockString),                                               # Block string definition
    byteString => $byteString,                                                  # Bytes string definition
    size       => $b,                                                           # Size of a block == size of a zmm
    offset     => $o,                                                           # Size of an offset is size of eax
    links      => $b - 2 * $o,                                                  # Location of links in bytes in zmm
    next       => $b - 1 * $o,                                                  # Location of next offset in block in bytes
    prev       => $b - 2 * $o,                                                  # Location of prev offset in block in bytes
    length     => $b - 2 * $o - 1,                                              # Variable containing maximum length in a block
    address    => undef,                                                        # Variable addressing first block in string
   );

  $s->address = $s->allocBlock($byteString->address);                           # Variable containing offset of first block in string

  $s                                                                            # Description of block string
 }

sub BlockString::allocBlock($$)                                                 # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($blockString, $bsa) = @_;                                                 # Block string descriptor, variable containing address of underlying byte string
  my $byteString = $blockString->byteString;

  Comment "Allocate a zmm block in a byte string";

  PushR my @regs = (rax, rdi, r14, r15);                                        # Save registers
# $blockString->bsAddress->setReg(rax);                                         # Set rax to byte string address
  defined($bsa) or confess;
  $bsa->setReg(rax);                                                            # Set rax to byte string address
  Mov rdi, $blockString->size;                                                  # Size of allocation
  $byteString->allocate;                                                        # Allocate in byte string
  my $block = Vq("Offset of allocated block", rdi);                             # Save address of block

  if (1)                                                                        # Initialize circular list
   {my $n = $blockString->next;                                                 # Quad word of next offset
    my $p = $blockString->prev;                                                 # Quad word of prev offset
    Mov "[rax+rdi+$n]", edi;
    Mov "[rax+rdi+$p]", edi;
   }

  PopR @regs;                                                                   # Restore registers

  $block;                                                                       # Variable containing address of allocation
 }

#sub BlockString::getBlockLength($$)                                             # Get the length of the block at the specified offset and return it as a new variable
# {my ($blockString, $block) = @_;                                               # Block string descriptor, variable containing offset of block whose length we want
#  PushR my @save = (r13, r14, r15);                                             # Result register
#  $blockString->bsAddress->setReg(r14);                                         # Byte string
#  $block->setReg(r15);                                                          # Offset in byte string to block
#  Mov r13b, "[r15+r14]";                                                        # Block length
#  my $r = Vq("Length of block", r13);                                           # Block length variable
#  PopR @save;                                                                   # Length of block is a byte
#  $r                                                                            # Result variable
# }

sub BlockString::getBlockLengthInZmm($$)                                        # Get the block length of the numbered zmm and return it in a variable
 {my ($blockString, $zmm) = @_;                                                 # Block string descriptor, number of zmm register
  getBFromZmmAsVariable $zmm, 0;                                                # Block length
 }

#sub BlockString::setBlockLength($$$)                                            # Set the length of the specified block to the specified length
# {my ($blockString, $block, $length) = @_;                                      # Block string descriptor, number of xmm register addressing block, new length in a byte register
#  PushR my @save = (r13, r14, r15);                                             # Result register
#  $blockString->bsAddress->setReg(r15);                                         # Byte string
#  $block->setReg(r14);                                                          # Offset of block
#  $length->setReg(r13);                                                         # New length
#  Mov "[r15+r14]", r13b;                                                        # Block length
#  PopR @save;                                                                   # Length of block is a byte
# }

sub BlockString::setBlockLengthInZmm($$$)                                       # Set the block length of the numbered zmm to the specified length
 {my ($blockString, $length, $zmm) = @_;                                        # Block string descriptor, length as a variable, number of zmm register
  PushR my @save = (r15);                                                       # Save work register
  $length->setReg(r15);                                                         # New length
  $length->putBIntoZmm($zmm, 0);                                                # Insert block length
  PopR @save;                                                                   # Length of block is a byte
 }

sub BlockString::getBlock($$$$)                                                 # Get the block with the specified offset in the specified block string and return it in the numbered zmm
 {my ($blockString, $bsa, $block, $zmm) = @_;                                   # Block string descriptor, offset of the block as a variable, number of zmm register to contain block
  PushR my @save = (r14, r15);                                                  # Result register
# $blockString->bsAddress->setReg(r15);                                         # Byte string address
  $bsa->setReg(r15);                                                            # Byte string address
  $block->setReg(r14);                                                          # Offset of block in byte string
  Vmovdqu64 "zmm$zmm", "[r15+r14]";                                             # Read from memory
  PopR @save;                                                                   # Restore registers
 }

sub BlockString::putBlock($$$$)                                                 # Write the numbered zmm to the block at the specified offset in the specified byte string
 {my ($blockString, $bsa, $block, $zmm) = @_;                                   # Block string descriptor, blosk in byte string, content variable
  PushR my @save = (r14, r15);                                                  # Work registers
  $bsa->setReg(r15);                                                            # Byte string address
  $block->setReg(r14);                                                          # Offset of block in byte string
  Vmovdqu64 "[r15+r14]", "zmm$zmm";                                             # Write to memory
  PopR @save;                                                                   # Restore registers
 }

#sub BlockString::getNextBlock($$)                                               # Get the offset of the next block from the specified block in the specified block string and return it as a variable
# {my ($blockString, $block) = @_;                                               # Block string descriptor, variable addressing current block
#  my $n = $blockString->next;                                                   # Quad word of next offset
#  my $p = $blockString->prev;                                                   # Quad word of prev offset
#  PushR my @regs = (r13, r14, r15);                                             # Work registers
#  $blockString->bsAddress->setReg(r15);                                         # Byte string address
#  $block->setReg(r14);                                                          # Offset of block in byte string
#  Mov    r13d, "[r15+r14+$n]";                                                  # Offset of next offset
#  my $r = Vq("Offset of next block", r13);                                      # Save offset of next block as a variable
#  PopR @regs;                                                                   # Free work registers
#  $r;                                                                           # Return address of next block
# }
#
#sub BlockString::getNextBlockFromZmm($$)                                        # Get the offset of the next block from the numbered zmm and return in in a variable
# {my ($blockString, $zmm) = @_;                                                 # Block string descriptor, numbered zmm
#  my $n = $blockString->next;                                                   # Quad word of next offset
#  my $p = $blockString->prev;                                                   # Quad word of prev offset
#  PushR my @regs = (k7);                                                        # Work registers
#  Mov    r13d, "[r15+r14+$n]";                                                  # Offset of next offset
#  my $r = Vq("Offset of next block", r13);                                      # Save offset of next block as a variable
#  PopR @regs;                                                                   # Free work registers
#  $r;                                                                           # Return address of next block
# }
#
#sub BlockString::getPrevBlock($$)                                               # Get the prev block from the block addressed by the numbered xmm register and return it in the same xmm
# {my ($blockString, $block) = @_;                                               # Block string descriptor, variable addressing current bloxk
#  my $n = $blockString->next;                                                   # Quad word of next offset
#  my $p = $blockString->prev;                                                   # Quad word of prev offset
#  PushR my @regs = (r13, r14, r15);                                             # Work registers
#  $blockString->bsAddress->setReg(r15);                                         # Byte string address
#  $block->setReg(r14);                                                          # Offset of block in byte string
#  Mov    r13d, "[r15+r14+$p]";                                                  # Offset of next offset
#  my $r = Vq("Offset of prev block", r13);                                      # Save offset of prev block as a variable
#  PopR @regs;                                                                   # Free work registers
#  $r;                                                                           # Return address of next block
# }

sub BlockString::getNextAndPrevBlockOffsetFromZmm($$)                           # Get the offsets of the next and previous blocks as variables from the specified zmm
 {my ($blockString, $zmm) = @_;                                                 # Block string descriptor, zmm containing block
  my $l = $blockString->links;                                                  # Location of links
  PushR my @regs = (r14, r15);                                                  # Work registers
  my $L = getQFromZmmAsVariable($zmm, $blockString->links);                     # Links in one register
  $L->setReg(r15);                                                              # Links
  Mov r14d, r15d;                                                                # Next
  Shr r15, RegisterSize(r14d) * 8;                                              # Prev
  my @r = (Vq("Next block offset", r14), Vq("Prev block offset", r15));         # Result
  PopR @regs;                                                                   # Free work registers
  @r;                                                                           # Return (next, prev)
 }

sub BlockString::putNextandPrevBlockOffsetIntoZmm($$$)                          # Save next and prev offsets into a zmm representing a block
 {my ($blockString, $zmm, $next, $prev) = @_;                                   # Block string descriptor, zmm containing block, next offset as a variable, prev offset as a variable
  PushR my @regs = (r14, r15);                                                  # Work registers
  $next->setReg(r15);                                                           # Next offset
  $prev->setReg(r14);                                                           # Prev offset
  Shl r14, RegisterSize(r14d) * 8;                                              # Prev high
  Or r15, r14;                                                                  # Links in one register
  my $l = Vq("Links", r15);                                                     # Links as variable
  $l->putQIntoZmm($zmm, $blockString->links);                                   # Load links into zmm
  PopR @regs;                                                                   # Free work registers
 }

#sub BlockString::putNext($$$)                                                   # Put a block in a numbered zmm to another block in another zmm
# {my ($blockString, $old, $new) = @_;                                           # Block string, number of xmm addressing existing old block in string, number of xmm addressing new block to be added
#  my $n = $blockString->next;                                                   # Quad word of next offset
#  my $p = $blockString->prev;                                                   # Quad word of prev offset
#  PushR my @save = (r12, r13, r14, r15);                                        # Work registers
#  my $bs  = r15;                                                                # Byte string
#  my $or  = r14;                                                                # Old block
#  my $nr  = r13;                                                                # New block
#  my $pr  = r12;                                                                # Next bloxk after old block
#  my $prd = r12d;                                                               # Next bloxk after old block
#  $blockString->bsAddress->setReg($bs);                                         # Byte string address
#  $old->setReg($or);                                                            # Offset of block in byte string
#  $new->setReg($nr);                                                            # Offset of block in byte string
#  Mov $prd, "[$bs+$or+$n]";                                                     # Block past old block
#  Mov "[$bs+$or+$n]", $nr;                                                      # Old block next to new block
#  Mov "[$bs+$nr+$p]", $or;                                                      # New block prev to old block
#  Mov "[$bs+$nr+$n]", $pr;                                                      # New block next to block past old block
#  Mov "[$bs+$pr+$p]", $nr;                                                      # Past block prev to new block
#  PopR @save;                                                                   # Free work registers
# }

sub BlockString::dump($)                                                        # Dump a block string  to sysout
 {my ($blockString) = @_;                                                       # Block string descriptor

  PushR my @save = (zmm31);
  my $block  = $blockString->address;                                           # The first block
               $blockString->getBlock($block, 31);                              # The first block in zmm31
  my $length = $blockString->getBlockLengthInZmm(31);                           # Length of block
  $block->dump("BlockString at address: ");
  $length->dump("Length: "); PrintOutRegisterInHex zmm31;                       # Print block

  ForEver                                                                       # Each block in string
   {my ($start, $end) = @_;                                                     #
    my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);     # Get links from current block
    If ($next == $block, sub{Jmp $end});                                        # Next block is the first block so we have printed the block string
    $blockString->getBlock($next, 31);                                          # Next block in zmm
    my $length = $blockString->getBlockLengthInZmm(31);                         # Length of block
    $next  ->dump("Offset: ");                                                  # Print block
    $length->dump("Length: ");
    PrintOutRegisterInHex zmm31;
   };
  PopR @save;
 }

sub BlockString::appendSub($$$$$)                                               # Append the specified content in memory to the specified block string
 {my ($blockString, $first, $source, $length, $bsa) = @_;                       # Block string descriptor, variable containing offset of first block, variable addressing source, variable containing length of source, variable containing byte string address
  my $success = Label;                                                          # Append completed successfully

  PushR my @save = (zmm29, zmm30, zmm31);
  $blockString->getBlock($bsa, $first, 29);                                     # Get the first block
  my ($second, $last) = $blockString->getNextAndPrevBlockOffsetFromZmm(29);     # Get the offsets of the next and previous blocks as variables from the specified zmm

  if (1)                                                                        # Fill a partially full first block in a string that only has one block
   {If ($last == $first, sub                                                    # String only has one block
     {my $lengthFirst = $blockString->getBlockLengthInZmm(29);                  # Length of the first block
      my $spaceFirst  = $blockString->length - $lengthFirst;                    # Space in first block

      If ($spaceFirst >= $length, sub                                           # Enough space in first block
       {$source->setZmm(29, $lengthFirst + 1, $length);                         # Append bytes
        $blockString->setBlockLengthInZmm($lengthFirst + $length, 29);          # Set the length
        $blockString->putBlock($bsa, $first, 29);                               # Put the block
        Jmp $success;
       },
      sub                                                                       # Completely fill first block
       {If ($spaceFirst >= 0, sub                                               # Some space in first block
         {$source->setZmm(29, $lengthFirst + 1, $spaceFirst);                   # Append bytes to fill first block
          $blockString->setBlockLengthInZmm(Vq('maximumLength', $blockString->length), 29);          # Set the length
          $source += $spaceFirst;
          $length -= $spaceFirst;
         });
        Vmovdqa64 zmm31, zmm29;                                                 # Place the first block which is also the last block into the last block
       }),
     },
    sub                                                                         # Fill partially full last block
     {$blockString->getBlock($bsa, $last, 31);                                  # Get the last block now known not to be the first block
      my $lengthLast = $blockString->getBlockLengthInZmm(31);                   # Length of the last block
      my $spaceLast  = $blockString->length - $lengthLast;                      # Space in last block
      If ($spaceLast >= $length, sub                                            # Enough space in last block
       {$source->setZmm(31, $lengthLast + 1, $length);                          # Append bytes
        $blockString->setBlockLengthInZmm($lengthLast + $length, 31);           # Set the length
        $blockString->putBlock($bsa, $last, 31);                                # Put the block
        Jmp $success;
       },
      sub                                                                       # Completely fill last block
       {If ($spaceLast >= 0, sub                                                # Some space in last block
         {$source->setZmm(31, $lengthLast + 1, $spaceLast);                     # Append bytes to fill last block
          $blockString->setBlockLengthInZmm(Vq('maximumLength', $blockString->length), 31);  # Set the length
          $source += $spaceLast;
          $length -= $spaceLast;
         });
       }),
     });
   }

  if (1)                                                                        # Add new blocks and fill them
   {ForEver                                                                     # Fill any more blocks needed
     {my ($start, $end) = @_;                                                   # Start and end of loop

      my $new = $blockString->allocBlock($bsa);                                 # Allocate new block that we will insert next
      $blockString->getBlock($bsa, $new, 30);                                   # Get the new block which will have been properly formatted

      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Link new block
      If ($first == $last, sub                                                  # Connect first block to new block in string of one block
       {$blockString->putNextandPrevBlockOffsetIntoZmm(31, $new,  $new);
        $blockString->putNextandPrevBlockOffsetIntoZmm(30, $last, $last);
       },
      sub                                                                       # Connect last block to new block in string of two or more blocks
       {$blockString->putNextandPrevBlockOffsetIntoZmm(31, $new,    $prev);
        $blockString->putNextandPrevBlockOffsetIntoZmm(30, $next,   $last);
        $blockString->putNextandPrevBlockOffsetIntoZmm(29, $second, $new);
        $blockString->putBlock($bsa, $last, 31);                                # Only write the block if it is not the first block as the first block will be written later
       });

      If ($blockString->length >= $length, sub                                  # Enough space in last block to complete move
       {$source->setZmm(30, $blockString->one, $length);                        # Append bytes
        $blockString->setBlockLengthInZmm($length, 30);                         # Set the length
        $blockString->putBlock($bsa, $new, 30);                                 # Put the block
        Jmp $end;
       });

      $source->setZmm(31, $blockString->one, $blockString->length);             # Append full block
      $blockString->setBlockLengthInZmm($blockString->length, 31);              # Set the length
      $source += $blockString->length;
      $length -= $blockString->length;

      Vmovdqa64 zmm31, zmm30;                                                   # New block is now the last block
      $last->copy($new);                                                        # Make last equal to new for the next iteration
     };
   }

  If ($first == $last, sub                                                      # Save first  block if there is more than two blocks in the string
   {$blockString->putBlock($last, 31);                                          # Only write the block if it is not the first block as the first block will be written later
   },
  sub
   {$blockString->putBlock($first, 29);                                         # Put the first block back
   });

  SetLabel $success;                                                            # The move is now complete
  PopR @save;
 }

sub BlockString::append($$$)                                                    # Append the specified content in memory to the specified block string
 {my ($blockString, $source, $length) = @_;                                     # Block string descriptor, variable addressing source, variable containing length of source

  if (!defined $$blockString{append})
   {$$b{BlockString}{append}{sub} = S
     {my $first  = $$blockString{append}{first}  = Vq("first");
      my $source = $$blockString{append}{source} = Vq("source");
      my $length = $$blockString{append}{length} = Vq("length");
      my $bsa    = $$blockString{append}{bsa}    = Vq("bsa");

      $blockString->appendSub($first, $source, $length, $bsa)
     } name => "BlockString::Append";
   }

  $$blockString{append}{first} ->copy($blockString->address);
  $$blockString{append}{source}->copy($source);
  $$blockString{append}{length}->copy($length);
  $$blockString{append}{bsa}   ->copy($$blockString->byteString->address);
  Call $blockString->{append}{sub};
 }

#D1 Tree                                                                        # Tree operations

sub GenTree($$)                                                                 # Generate a set of routines to manage a tree held in a byte string with key and data fields of specified widths.  Allocate a byte string to contain the tree, return its address in xmm0=(0, tree).
 {my ($keyLength, $dataLength) = @_;                                            # Fixed key length in bytes, fixed data length in bytes
  @_ == 2 or confess;
  $keyLength  =~ m(\A2|4|8\Z) or confess;
  $dataLength =~ m(\A2|4|8\Z) or confess;

  my ($structure, $up, $left, $right) = All8Structure 3;                        # Tree structure addressed by a register
  my $height = $structure->field(4, "Height of the sub tree");
  my $count  = $structure->field(4, "Number of entries active in this node");

  my $s = $structure->size;                                                     # Structure size
  my $k = RegisterSize(zmm0) / $keyLength;                                      # Number of keys

  PushR my @regs = (rax, rdi);                                                  # Allocate a byte string to contain the tree and return its address in xmm0
  my $byteString = CreateByteString;                                            # Create a byte string to contain the tree
  ClearRegisters rdi;                                                           # Zero
  Push rdi;                                                                     # Format stack for xmm0
  Push rax;
  PopRR xmm0;                                                                   # Put result in xmm0
  PopRR @regs;                                                                  # Restore stack

  my $K = $k * $keyLength;
  my $D = $k * $dataLength;

  my $arenaTree = genHash("ArenaTree",                                          # A node in an arena tree
    byteString  => $byteString,
    dump        => undef,
    node        => undef,
    disLeft     => undef,
    disRight    => undef,
    insertLeft  => undef,
    insertRight => undef,
    isRoot      => undef,
    find        => undef,
    put         => undef,
    get         => undef,
    up          => $up,
    left        => $left,
    right       => $right,
    structure   => $structure,
    sizeBase    => $s,
    sizeKeys    => $K,
    sizeData    => $D,
    size        => $s + $K + $D,
   );

  $arenaTree->node = sub                                                        # Create a new node in the arena tree pointed to by xmm0=(*,tree) and return the offset of the new node in xmm0=(offset, tree)
   {@_ == 0 or confess;
    SaveFirstFour;
    PushR xmm0;                                                                 # Parse xmm0
    Mov rax, "[rsp]";                                                           # We want rax while keeping xmm0 on the stack
    Mov rdi, $arenaTree->size;                                                  # Size of allocation
    $arenaTree->byteString->allocate;
    Mov "[rsp+8]", rdi;                                                         # Push into position on stack
    PopR xmm0;                                                                  # Receive xmm0 with the node offset in the high quad
    RestoreFirstFour;
   };

  $arenaTree->dump = sub                                                        # Dump a node
   {my ($title) = @_;                                                           # Title
    @_ <= 1 or confess;
    my $s = $arenaTree->structure;
    PrintOutStringNL($title) if $title;
    PrintOutString("ArenaTreeNode at: ");

    SaveFirstFour;
    PushR xmm0;                                                                 # Parse xmm0
    PopR  rdi, rax;                                                             # Address node

    PushR my @regs = (rax, rdi);                                                # Print offset
    Mov rax, rdi;
    PrintOutRaxInHex;
    PopR  @regs;
    PrintOutNL;

    for my $f(qw(up left right))                                                # Fields to print
     {PrintOutString sprintf("%5s: ", $f);                                      # Field name
      PushR my @regs = (rax, rdi);
      Mov rax, $arenaTree->{$f}->addr("rax+rdi");
      PrintOutRaxInHex;
      PopR @regs;
      PrintOutNL;
     }
    RestoreFirstFour;
   };

  $arenaTree->isRoot = sub                                                      # Clear the zero flag if the tree node addressed by xmm0 is a root node else set it.  This makes If takes the then clause if we are on a root  node.
   {@_ == 0 or confess;
    SaveFirstFour;
    PushR xmm0;                                                                 # Parse xmm0
    PopR rax, rdi;
    Mov rsi, $arenaTree->up->addr("rax+rdi");                                   # Load up field
    Test rsi, rsi;                                                              # Test up field
    IfNz {SetZF} sub {ClearZF};
    RestoreFirstFour;
   };

  for my $d(qw(left right))                                                     # Insert left or right
   {my $s = <<'END';
    $arenaTree->insertXXXX = sub                                                # Insert the node addressed by xmm1 left under the node addressed by xmm0
     {@_ == 0 or confess;
      SaveFirstFour;                                                            # A check that we are in the same tree would be a good idea here.
      PushRR xmm0;                                                              # Parse xmm0
      PopRR rdi, rax;
      PushRR xmm1;                                                              # Parse xmm0
      PopRR rsi, rdx;
      Mov $arenaTree->xxxx->addr("rax+rdi"), rsi;                               # XXXX
      Mov $arenaTree->up  ->addr("rdx+rsi"), rdi;                               # Up
      RestoreFirstFour;
     };
END
    my $u = ucfirst $d;
       $s =~ s(XXXX) ($u)gs;
       $s =~ s(xxxx) ($d)gs;
    eval $s;
    confess $@ if $@;
   }

  $arenaTree                                                                    # Description of this tree
 }

#D1 Assemble                                                                    # Assemble generated code

sub Start()                                                                     # Initialize the assembler
 {@bss = @data = @rodata = %rodata = %rodatas = %subroutines = @text = %Keep = %KeepStack = ();
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
  KeepFree rax;
  Mov rax, 60;
  Syscall;
 }

my $LocateIntelEmulator;                                                        # Location of Intel Software Development Emulator

sub LocateIntelEmulator()                                                       # Assemble the generated code
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

my $totalBytesAssembled = 0;                                                    # Estimate the size of the output programs

sub Assemble(%)                                                                 # Assemble the generated code
 {my (%options) = @_;                                                           # Options
  Exit 0 unless @text > 4 and $text[-4] =~ m(Exit code:);                       # Exit with code 0 if no other exit has been taken

  my $k = $options{keep};                                                       # Keep the executable
  my $r = join "\n", map {s/\s+\Z//sr} @rodata;
  my $d = join "\n", map {s/\s+\Z//sr} @data;
  my $b = join "\n", map {s/\s+\Z//sr} @bss;
  my $t = join "\n", map {s/\s+\Z//sr} @text;
  my $a = <<END;
section .rodata
  $r
section .data
  $d
section .bss
  $b
section .text
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

  my $cmd  = qq(nasm -f elf64 -g -l $l -o $o $c && ld -o $e $o && chmod 744 $e);# Assemble
  my $exec = $emulator                                                          # Execute with or without the emulator
             ? qq($sde -ptr-check -- ./$e 2>&1)
             :                    qq(./$e 2>&1);

  $cmd .= qq( && $exec) unless $k;                                              # Execute automatically unless suppressed by user

  say STDERR qq($cmd);
  my $R    = qx($cmd);
  say STDERR $R;
  $totalBytesAssembled += fileSize $c;                                          # Estimate the size of the output programs
  unlink $o;                                                                    # Delete files
  unlink $e unless $k;                                                          # Delete executable unless asked to keep it
  $totalBytesAssembled += fileSize $c;                                          # Estimate the size of the output program
  Start;                                                                        # Clear work areas for next assembly
  $k ? $exec : $R                                                               # Return execution command or execution results
 }

sub removeNonAsciiChars($)                                                      #P Return a copy of the specified string with all the non ascii characters removed
 {my ($string) = @_;                                                            # String
  $string =~ s([^0x0-0x7f]) ()gsr;                                              # Remove non ascii characters
 }

sub totalBytesAssembled                                                         #P Total size in bytes of all files assembled during testing
 {$totalBytesAssembled
 }

#d
#-------------------------------------------------------------------------------
# Export - eeee
#-------------------------------------------------------------------------------

if (0)                                                                          #  Print exports
 {my @e;
  for my $a(sort keys %Nasm::X86::)
   {next if $a =~ m(DATA|confirmHasCommandLineCommand|currentDirectory|fff|fileSize|findFiles|fpe|fpf|genHash|lll|owf|pad|readFile);
    next if $a !~ m(\A[A-Z]) and !$Registers{$a};
    push @e, $a if $Nasm::X86::{$a} =~ m(\*Nasm::X86::);
   }
  say STDERR q/@EXPORT_OK    = qw(/.join(' ', @e).q/);/;
  exit;
 }

use Exporter qw(import);

use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA          = qw(Exporter);
@EXPORT       = qw();
@EXPORT_OK    = qw(Add All8Structure AllocateAll8OnStack AllocateMemory And Assemble BEGIN Bswap Bt Btc Btr Bts Bzhi Call ClearMemory ClearRegisters ClearZF CloseFile Cmova Cmovae Cmovb Cmovbe Cmovc Cmove Cmovg Cmovge Cmovl Cmovle Cmovna Cmovnae Cmovnb Cmp Comment ConcatenateShortStrings Copy CopyMemory CreateByteString Cstrlen Db Dbwdq Dd Dec Decrement Dq Ds Dw Dx Dy Dz EXPORT EXPORT_OK EXPORT_TAGS Exit Float32 Float64 For ForIn Fork FreeMemory GenTree GetLengthOfShortString GetPPid GetPid GetPidInHex GetUid Hash ISA Idiv If IfEq IfGe IfGt IfLe IfLt IfNe IfNz Imul Inc Increment InsertIntoXyz Ja Jae Jb Jbe Jc Jcxz Je Jecxz Jg Jge Jl Jle Jmp Jna Jnae Jnb Jnbe Jnc Jne Jng Jnge Jnl Jnle Jno Jnp Jns Jnz Jo Jp Jpe Jpo Jrcxz Js Jz Kaddb Kaddd Kaddq Kaddw Kandb Kandd Kandnb Kandnd Kandnq Kandnw Kandq Kandw Keep KeepFree KeepPop KeepPush KeepSet Kmovb Kmovd Kmovq Kmovw Knotb Knotd Knotq Knotw Korb Kord Korq Kortestb Kortestd Kortestq Kortestw Korw Kshiftlb Kshiftld Kshiftlq Kshiftlw Kshiftrb Kshiftrd Kshiftrq Kshiftrw Ktestb Ktestd Ktestq Ktestw Kunpckb Kunpckd Kunpckq Kunpckw Kxnorb Kxnord Kxnorq Kxnorw Kxorb Kxord Kxorq Kxorw Label Lea LoadShortStringFromMemoryToZmm LoadShortStringFromMemoryToZmm2 LoadTargetZmmFromSourceZmm LoadZmmFromMemory LocalData Lzcnt MaximumOfTwoRegisters MinimumOfTwoRegisters Minus Mov Movdqa Mulpd Neg Not OpenRead OpenWrite Or PeekR Pextrb Pextrd Pextrq Pextrw Pi32 Pi64 Pinsrb Pinsrd Pinsrq Pinsrw Plus Pop PopR PopRR Popfq PrintOutMemory PrintOutMemoryInHex PrintOutMemoryInHexNL PrintOutMemoryNL PrintOutNL PrintOutRaxInHex PrintOutRaxInReverseInHex PrintOutRegisterInHex PrintOutRegistersInHex PrintOutRflagsInHex PrintOutRipInHex PrintOutString PrintOutStringNL PrintOutZF Pslldq Psrldq Push PushR PushRR Pushfq Rb Rbwdq Rd Rdtsc ReadFile ReadTimeStampCounter RegisterSize ReorderSyscallRegisters ReorderXmmRegisters RestoreFirstFour RestoreFirstFourExceptRax RestoreFirstFourExceptRaxAndRdi RestoreFirstSeven RestoreFirstSevenExceptRax RestoreFirstSevenExceptRaxAndRdi Ret Rq Rs Rw S SaveFirstFour SaveFirstSeven SetLabel SetLengthOfShortString SetMaskRegister SetRegisterToMinusOne SetZF Seta Setae Setb Setbe Setc Sete Setg Setge Setl Setle Setna Setnae Setnb Setnbe Setnc Setne Setng Setnge Setnl Setno Setnp Setns Setnz Seto Setp Setpe Setpo Sets Setz Shl Shr Start StatSize Structure Sub Syscall Test Tzcnt UnReorderSyscallRegisters UnReorderXmmRegisters VERSION Vaddd Vaddpd Variable Vb Vcvtudq2pd Vcvtudq2ps Vcvtuqq2pd Vd Vdpps Vgetmantps Vmovd Vmovdqa32 Vmovdqa64 Vmovdqu Vmovdqu32 Vmovdqu64 Vmovdqu8 Vmovq Vmulpd Vpbroadcastb Vpbroadcastd Vpbroadcastq Vpbroadcastw Vpcmpub Vpcmpud Vpcmpuq Vpcmpuw Vpcompressd Vpcompressq Vpexpandd Vpexpandq Vpinsrb Vpinsrd Vpinsrq Vpinsrw Vprolq Vpxorq Vq Vsqrtpd Vw Vx Vy Vz WaitPid Xchg Xor ah al ax bh bl bp bpl bx ch cl cs cx dh di dil dl ds dx eax ebp ebx ecx edi edx es esi esp fs gs k0 k1 k2 k3 k4 k5 k6 k7 mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7 r10 r10b r10d r10l r10w r11 r11b r11d r11l r11w r12 r12b r12d r12l r12w r13 r13b r13d r13l r13w r14 r14b r14d r14l r14w r15 r15b r15d r15l r15w r8 r8b r8d r8l r8w r9 r9b r9d r9l r9w rax rbp rbx rcx rdi rdx rflags rip rsi rsp si sil sp spl ss st0 st1 st2 st3 st4 st5 st6 st7 xmm0 xmm1 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm2 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm3 xmm30 xmm31 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 ymm0 ymm1 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm2 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm3 ymm30 ymm31 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 zmm0 zmm1 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm2 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm3 zmm30 zmm31 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9);%EXPORT_TAGS = (all=>[@EXPORT, @EXPORT_OK]);

# podDocumentation
=pod

=encoding utf-8

=head1 Name

Nasm::X86 - Generate Nasm assembler code

=head1 Synopsis

Write and execute x64 instructions using perl as a macro assembler as shown in
the following examples.

=head2 Avx512 instructions

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
   rax: 0000 0000 0000 00$P
END

=head2 Dynamic string held in an arena

Create a dynamic byte string, add some content to it, write the byte string to
a file and then execute it:.

  my $s = CreateByteString;                                                     # Create a string
  $s->ql(<<END);                                                                # Write code to execute
#!/usr/bin/bash
whoami
ls -la
pwd
END
  $s->write;                                                                    # Write code to a temporary file
  $s->bash;                                                                     # Execute the temporary file
  $s->unlink;                                                                   # Execute the temporary file

  my $u = qx(whoami); chomp($u);
  ok Assemble =~ m($u);

=head2 Process management

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

=head2 Read a file

Read this file:

  Mov rax, Rs($0);                                                              # File to read
  ReadFile;                                                                     # Read file
  PrintOutMemory;                                                               # Print memory

  my $r = Assemble;                                                             # Assemble and execute
  ok index($r, readFile($0)) > -1;                                              # Output contains this file

=head2 Installation

The Intel Software Development Emulator will be required if you do not have a
computer with the avx512 instruction set and wish to execute code containing
these instructions. For details see:

L<https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2>


The Networkwide Assembler is required to assemble the code produced  For full
details see:

L<https://github.com/philiprbrenan/NasmX86/blob/main/.github/workflows/main.yml>

=head2 Execution Options

The L<Assemble(%options)> function takes the following keywords to control assembly
and execution of the assembled code:

To produce a named executable without running it, specify:

 keep=>"executable file name"

To run the executable produced by L<Assemble(%options)> without the Intel emulator,
which is used by default if it is present, specify:

 emulator=>0

=head1 Description

Generate Nasm assembler code


Version "20210510".


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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;
    CopyMemory;
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

Load bytes in the numbered target zmm register at a register specified offset with source bytes from a numbered source zmm register at a specified register offset for a specified register length.

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

=head1 Variables

Variable definitions and operations

=head2 Definitions

Variable definitions

=head3 Variable($size, $name, $expr)

Create a new variable with the specified size and name initialized via an expression

     Parameter  Description
  1  $size      Size as a power of 2
  2  $name      Name of variable
  3  $expr      Expression initializing variable

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

    If($a == 3, sub{PrintOutStringNL "a == 3"});

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


=head3 Vx($name, $expr)

Define an xmm variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression

=head3 Vy($name, $expr)

Define a ymm variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression

=head3 Vz($name, $expr)

Define a zmm variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression

=head2 Operations

Variable operations

=head3 Variable::address($left)

Get the address of a variable

     Parameter  Description
  1  $left      Left variable

=head3 Variable::arithmetic($op, $name, $left, $right)

Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables

     Parameter  Description
  1  $op        Operator
  2  $name      Operator name
  3  $left      Left variable
  4  $right     Right variable

=head3 Variable::add($left, $right)

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

    If($a == 3, sub{PrintOutStringNL "a == 3"});

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


=head3 Variable::sub($left, $right)

Subtract the right hand variable from the left hand variable and return the result as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::times($left, $right)

Multiply the left hand variable by the right hand variable and return the result as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::division($op, $left, $right)

Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side

     Parameter  Description
  1  $op        Operator
  2  $left      Left variable
  3  $right     Right variable

=head3 Variable::divide($left, $right)

Divide the left hand variable by the right hand variable and return the result as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::mod($left, $right)

Divide the left hand variable by the right hand variable and return the remainder as a new variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::boolean($sub, $op, $left, $right)

Combine the left hand variable with the right hand variable via a boolean operator

     Parameter  Description
  1  $sub       Operator
  2  $op        Operator name
  3  $left      Left variable
  4  $right     Right variable

=head3 Variable::eq($left, $right)

Check whether the left hand variable is equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::ne($left, $right)

Check whether the left hand variable is not equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::ge($left, $right)

Check whether the left hand variable is greater than or equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::gt($left, $right)

Check whether the left hand variable is greater than the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::le($left, $right)

Check whether the left hand variable is less than or equal to the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::lt($left, $right)

Check whether the left hand variable is less than the right hand variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::print($left)

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

    If($a == 3, sub{PrintOutStringNL "a == 3"});

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

    my $a = Vq(a, 3); $a->dump;
    my $b = Vq(b, 2); $b->dump;
    my $c = $a +  $b; $c->print;
    my $d = $c -  $a; $d->print;
    my $e = $d == $b; $e->print;
    my $f = $d != $b; $f->print;
    my $g = $a *  $b; $g->print;
    my $h = $g /  $b; $h->print;
    my $i = $a %  $b; $i->print;

    If($a == 3, sub{PrintOutStringNL "a == 3"});

    is_deeply Assemble, <<END;
  a: 0300 0000 0000 0000
  b: 0200 0000 0000 0000
  0500 0000 0000 0000
  0200 0000 0000 0000
  0100 0000 0000 0000
  0000 0000 0000 0000
  0600 0000 0000 0000
  0300 0000 0000 0000
  0100 0000 0000 0000
  a == 3
  END


=head3 Variable::dump($left)

Dump the value of a variable on stdout

     Parameter  Description
  1  $left      Left variable

B<Example:>


    my $a = Vq(a, 3); $a->dump;
    my $b = Vq(b, 2); $b->dump;
    my $c = $a +  $b; $c->print;
    my $d = $c -  $a; $d->print;
    my $e = $d == $b; $e->print;
    my $f = $d != $b; $f->print;
    my $g = $a *  $b; $g->print;
    my $h = $g /  $b; $h->print;
    my $i = $a %  $b; $i->print;

    If($a == 3, sub{PrintOutStringNL "a == 3"});

    is_deeply Assemble, <<END;
  a: 0300 0000 0000 0000
  b: 0200 0000 0000 0000
  0500 0000 0000 0000
  0200 0000 0000 0000
  0100 0000 0000 0000
  0000 0000 0000 0000
  0600 0000 0000 0000
  0300 0000 0000 0000
  0100 0000 0000 0000
  a == 3
  END

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


=head3 Variable::setReg($variable, $register)

Set the named register from the content of the variable

     Parameter  Description
  1  $variable  Variable
  2  $register  Register to load

=head3 Variable::getReg($variable, $register)

Load the variable from the named register

     Parameter  Description
  1  $variable  Variable
  2  $register  Register to load

=head3 Variable::incDec($left, $op)

Increment or decrement a variable

     Parameter  Description
  1  $left      Left variable operator
  2  $op        Address of operator to perform inc or dec

=head3 Variable::inc($left)

Increment a variable

     Parameter  Description
  1  $left      Variable

=head3 Variable::dec($left)

Decrement a variable

     Parameter  Description
  1  $left      Variable

=head3 Variable::str($left)

The name of the variable

     Parameter  Description
  1  $left      Variable

=head3 Variable::min($left, $right)

Minimum of two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

B<Example:>


    my $a = Vq("a", 1);
    my $b = Vq("b", 2);
    my $c = $a->min($b);
    my $d = $a->max($b);
    $a->dump;
    $b->dump;
    $c->dump;
    $d->dump;

    is_deeply Assemble,<<END;
  a: 0100 0000 0000 0000
  b: 0200 0000 0000 0000
  Minimum(a, b): 0100 0000 0000 0000
  Maximum(a, b): 0200 0000 0000 0000
  END


=head3 Variable::max($left, $right)

Maximum of two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

B<Example:>


    my $a = Vq("a", 1);
    my $b = Vq("b", 2);
    my $c = $a->min($b);
    my $d = $a->max($b);
    $a->dump;
    $b->dump;
    $c->dump;
    $d->dump;

    is_deeply Assemble,<<END;
  a: 0100 0000 0000 0000
  b: 0200 0000 0000 0000
  Minimum(a, b): 0100 0000 0000 0000
  Maximum(a, b): 0200 0000 0000 0000
  END


=head3 Variable::and($left, $right)

And two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::or($left, $right)

Or two variables

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable

=head3 Variable::setMask($start, $length, $mask)

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


=head3 Variable::setZmm($source, $target, $offset, $length)

Load bytes from the memory addressed by the source variable into the numbered zmm register at a specified offset moving the specified number of bytes

     Parameter  Description
  1  $source    Variable containing the address of the source
  2  $target    Number of zmm to load
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

    my $s = Rb(0..128);
    my $t = Db(map {0} 0..128);
    my $source = Vq(Source, $s);
    my $target = Vq(Target, $t);
    $source->getZmm(0);
    PrintOutRegisterInHex zmm0;

    $target->putZmm(0);
    $target->getZmm(1);
    PrintOutRegisterInHex zmm1;

    is_deeply Assemble, <<END;
    zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
    zmm1: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  END


=head3 Variable::getZmm($source, $target)

Load bytes from the memory addressed by the source variable into the numbered zmm register.

     Parameter  Description
  1  $source    Variable containing the address of the source
  2  $target    Number of zmm to get

B<Example:>


    my $s = Rb(0..128);
    my $t = Db(map {0} 0..128);
    my $source = Vq(Source, $s);
    my $target = Vq(Target, $t);
    $source->getZmm(0);
    PrintOutRegisterInHex zmm0;

    $target->putZmm(0);
    $target->getZmm(1);
    PrintOutRegisterInHex zmm1;

    is_deeply Assemble, <<END;
    zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
    zmm1: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  END


=head3 Variable::putZmm($source, $target)

Write bytes into the memory addressed by the source variable from the numbered zmm register.

     Parameter  Description
  1  $source    Variable containing the address of the source
  2  $target    Number of zmm to put

=head3 Variable::for($limit, $body)

Iterate the body from 0 limit times.

     Parameter  Description
  1  $limit     Limit
  2  $body      Body

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

For - iterate the body as long as register plus increment is less than than limit incrementing by increment each time

     Parameter   Description
  1  $full       Body for full block
  2  $last       Body for last block
  3  $register   Register
  4  $limit      Limit on loop
  5  $increment  Increment on each iteration

=head2 S($body, %options)

Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub

     Parameter  Description
  1  $body      Body
  2  %options   Options.

B<Example:>


    Mov rax, 0x44332211;
    PrintOutRegisterInHex rax;


    my $s = S  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {PrintOutRegisterInHex rax;
      Inc rax;
      PrintOutRegisterInHex rax;
     };

    Call $s;

    PrintOutRegisterInHex rax;

    my $r = Assemble;
    ok $r =~ m(0000 0000 4433 2211.*2211.*2212.*0000 0000 4433 2212)s;


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


=head1 Print

Print

=head2 PrintOutNL()

Print a new line to stdout


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


=head2 PrintOutString($string)

Print a constant string to sysout.

     Parameter  Description
  1  $string    String

B<Example:>



    PrintOutString "Hello World";  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(Hello World);


=head2 PrintOutStringNL($string)

Print a constant string to sysout followed by new line

     Parameter  Description
  1  $string    String

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


=head2 PrintOutRaxInHex()

Write the content of register rax to stderr in hexadecimal in big endian notation


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


=head2 PrintOutRegisterInHex(@r)

Print any register as a hex string

     Parameter  Description
  1  @r         Name of the register to print

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

=head3 PushRR(@r)

Push registers onto the stack without tracking

     Parameter  Description
  1  @r         Register

=head3 PushR(@r)

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


=head3 PopRR(@r)

Pop registers from the stack without tracking

     Parameter  Description
  1  @r         Register

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


=head4 Structure::field($structure, $length, $comment)

Add a field of the specified length with an optional comment

     Parameter   Description
  1  $structure  Structure data descriptor
  2  $length     Length of data
  3  $comment    Optional comment

=head4 StructureField::addr($field, $register)

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


=head4 LocalData::start($local)

Start a local data area on the stack

     Parameter  Description
  1  $local     Local data descriptor

=head4 LocalData::free($local)

Free a local data area on the stack

     Parameter  Description
  1  $local     Local data descriptor

=head4 LocalData::variable($local, $length, $comment)

Add a local variable

     Parameter  Description
  1  $local     Local data descriptor
  2  $length    Length of data
  3  $comment   Optional comment

=head4 LocalVariable::stack($variable)

Address a local variable on the stack

     Parameter  Description
  1  $variable  Variable

=head4 LocalData::allocate8($local, @comments)

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

=head2 PrintOutMemoryInHex()

Dump memory from the address in rax for the length in rdi


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


=head2 PrintOutMemoryInHexNL()

Dump memory from the address in rax for the length in rdi and then print a new line


=head2 PrintOutMemory()

Print the memory addressed by rax for a length of rdi


B<Example:>


    Comment "Print a string from memory";
    my $s = "Hello World";
    Mov rax, Rs($s);
    Mov rdi, length $s;

    PrintOutMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(Hello World);


=head2 PrintOutMemoryNL()

Print the memory addressed by rax for a length of rdi followed by a new line


=head2 AllocateMemory()

Allocate the amount of memory specified in rax via mmap and return the address of the allocated memory in rax


B<Example:>


    my $N = 2048;
    my $q = Rs('a'..'p');
    Mov rax, $N; KeepFree rax;

    AllocateMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    Vmovdqu8 xmm0, "[$q]";
    Vmovdqu8 "[rax]", xmm0;
    Mov rdi,16;
    PrintOutMemory;
    PrintOutNL;
    KeepFree rdi;

    Mov rdi, $N;
    FreeMemory;
    PrintOutRegisterInHex rax;

    ok Assemble =~ m(abcdefghijklmnop)s;

    my $N = 4096;                                                                 # Size of the initial allocation which should be one or more pages
    my $S = RegisterSize rax;
    Mov rax, $N;

    AllocateMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    Mov rdi, $N;
    ClearMemory;
    PrintOutRegisterInHex rax;
    PrintOutMemoryInHex;

    my $r = Assemble;
    if ($r =~ m((0000.*0000))s)
     {is_deeply length($1), 9776;
     }


=head2 FreeMemory()

Free memory via munmap. The address of the memory is in rax, the length to free is in rdi


B<Example:>


    my $N = 2048;
    my $q = Rs('a'..'p');
    Mov rax, $N; KeepFree rax;
    AllocateMemory;
    PrintOutRegisterInHex rax;

    Vmovdqu8 xmm0, "[$q]";
    Vmovdqu8 "[rax]", xmm0;
    Mov rdi,16;
    PrintOutMemory;
    PrintOutNL;
    KeepFree rdi;

    Mov rdi, $N;

    FreeMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    ok Assemble =~ m(abcdefghijklmnop)s;

    my $N = 4096;                                                                 # Size of the initial allocation which should be one or more pages
    my $S = RegisterSize rax;
    Mov rax, $N;
    AllocateMemory;
    PrintOutRegisterInHex rax;
    Mov rdi, $N;
    ClearMemory;
    PrintOutRegisterInHex rax;
    PrintOutMemoryInHex;

    my $r = Assemble;
    if ($r =~ m((0000.*0000))s)
     {is_deeply length($1), 9776;
     }


=head2 ClearMemory()

Clear memory - the address of the memory is in rax, the length in rdi


B<Example:>


    my $N = 4096;                                                                 # Size of the initial allocation which should be one or more pages
    my $S = RegisterSize rax;
    Mov rax, $N;
    AllocateMemory;
    PrintOutRegisterInHex rax;
    Mov rdi, $N;

    ClearMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    PrintOutMemoryInHex;

    my $r = Assemble;
    if ($r =~ m((0000.*0000))s)
     {is_deeply length($1), 9776;
     }


=head2 CopyMemory()

Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi


B<Example:>


    my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;
    my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

    Vmovdqu8 xmm0, "[$s]";
    Vmovdqu8 xmm1, "[$t]";
    PrintOutRegisterInHex xmm0;
    PrintOutRegisterInHex xmm1;
    Sub rsp, 16;

  # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
    Mov rax, rsp;
    Mov rdi, 16;
    Mov rsi, $s;

    CopyMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


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

    Mov rax, Rs(my $f = "zzz.txt");                                               # File to write
    OpenWrite;                                                                    # Open file
    CloseFile;                                                                    # Close file

    my $r = Assemble;
    ok $r =~ m(( 0000){3} 0003)i;                                                 # Expected file number
    ok $r =~ m(( 0000){4})i;                                                      # Expected file number
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

    Mov rax, Rs(my $f = "zzz.txt");                                               # File to write

    OpenWrite;                                                                    # Open file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CloseFile;                                                                    # Close file

    my $r = Assemble;
    ok $r =~ m(( 0000){3} 0003)i;                                                 # Expected file number
    ok $r =~ m(( 0000){4})i;                                                      # Expected file number
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

    Mov rax, Rs(my $f = "zzz.txt");                                               # File to write
    OpenWrite;                                                                    # Open file

    CloseFile;                                                                    # Close file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $r = Assemble;
    ok $r =~ m(( 0000){3} 0003)i;                                                 # Expected file number
    ok $r =~ m(( 0000){4})i;                                                      # Expected file number
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


=head2 ReadFile()

Read a file whose name is addressed by rax into memory.  The address of the mapped memory and its length are returned in registers rax,rdi


B<Example:>


    Mov rax, Rs($0);                                                              # File to read

    ReadFile;                                                                     # Read file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutMemory;                                                               # Print memory

    my $r = Assemble;                                                             # Assemble and execute
    ok index(removeNonAsciiChars($r), removeNonAsciiChars(readFile $0)) >= 0;     # Output contains this file


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


    if (0 and develop)                                                            # Hash various strings  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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


=head1 Long Strings

Operations on Long Strings

=head2 Cstrlen()

Length of the C style string addressed by rax returning the length in r15


B<Example:>


    my $s = Rs("abcd");
    Mov rax, $s;

    Cstrlen;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex r15;
    ok Assemble =~ m(r15: 0000 0000 0000 0004);


=head2 CreateByteString()

Create an relocatable string of bytes in an arena and returns its address in rax


B<Example:>



    my $s = CreateByteString;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $s->q(my $t = 'ab');                                                          # Append a constant to the byte string
    $s->nl;                                                                       # New line

    Mov rdi, rax;                                                                 # Save source byte string

    CreateByteString;                                                             # Create target byte string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $s->copy;                                                                     # Copy source to target

    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;                                                                     # Copy source to target
    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;

    Xchg rdi, rax;
    $s->copy;
    Xchg rdi, rax;
    $s->copy;

    $s->out;                                                                      # Print byte string
    $s->clear;                                                                    # Clear byte string

    my $T = "$t
" x 8;                                                           # Expected response
    ok Assemble =~ m($T)s;                                                        # Assemble and execute


=head2 ByteString::makeReadOnly($byteString)

Make a byte string read only

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a byte string
    $s->q("Hello");                                                               # Write data to byte string
    $s->makeReadOnly;                                                             # Make byte string read only - tested above
    $s->makeWriteable;                                                             # Make byte string writable again
    $s->q(" World");                                                              # Try to write to byte string
    $s->out;

    ok Assemble =~ m(Hello World);


=head2 ByteString::makeWriteable($byteString)

Make a byte string writable

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a byte string
    $s->q("Hello");                                                               # Write data to byte string
    $s->makeReadOnly;                                                             # Make byte string read only - tested above
    $s->makeWriteable;                                                             # Make byte string writable again
    $s->q(" World");                                                              # Try to write to byte string
    $s->out;

    ok Assemble =~ m(Hello World);


=head2 ByteString::allocate($byteString)

Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a byte string
    Mov r8,  rax;
    Mov rdi, my $w = 0x20;                                                        # Space wanted
    $s->allocate;                                                                 # Allocate space wanted
    PrintOutRegisterInHex rdi;
    KeepFree rdi;
    Mov rdi, $w;                                                                  # Space wanted
    $s->allocate;                                                                 # Allocate space wanted
    PrintOutRegisterInHex rdi;

    my $e = sprintf("rdi: 0000 0000 0000 %04X", $s->structure->size);             # Expected results
    my $E = sprintf("rdi: 0000 0000 0000 %04X", $s->structure->size+$w);
    ok Assemble =~ m($e.*$E)s;


=head2 ByteString::m($byteString)

Append the content with length rdi addressed by rsi to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 ByteString::q($byteString, $const)

Append a quoted string == a constant to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $const       Constant

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->q($0);                                                                    # Append a constant to the byte string
    $s->z;                                                                        # New line
    $s->read;
    $s->out;

    my $r = Assemble;
    ok index(removeNonAsciiChars($r), removeNonAsciiChars(readFile $0)) >= 0;     # Output contains this file


=head2 ByteString::ql($byteString, $const)

Append a quoted string containing new line characters to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $const       Constant

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write;                                                                    # Write code to a temporary file
    $s->bash;                                                                     # Execute the temporary file
    $s->unlink;                                                                   # Execute the temporary file

    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);


=head2 ByteString::char($byteString, $char)

Append a character expressed as a decimal number to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $char        Decimal number of character to be appended

=head2 ByteString::nl($byteString)

Append a new line to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->q(my $t = 'ab');                                                          # Append a constant to the byte string
    $s->nl;                                                                       # New line

    Mov rdi, rax;                                                                 # Save source byte string
    CreateByteString;                                                             # Create target byte string
    $s->copy;                                                                     # Copy source to target

    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;                                                                     # Copy source to target
    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;

    Xchg rdi, rax;
    $s->copy;
    Xchg rdi, rax;
    $s->copy;

    $s->out;                                                                      # Print byte string
    $s->clear;                                                                    # Clear byte string

    my $T = "$t
" x 8;                                                           # Expected response
    ok Assemble =~ m($T)s;                                                        # Assemble and execute


=head2 ByteString::z($byteString)

Append a trailing zero to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->q($0);                                                                    # Append a constant to the byte string
    $s->z;                                                                        # New line
    $s->read;
    $s->out;

    my $r = Assemble;
    ok index(removeNonAsciiChars($r), removeNonAsciiChars(readFile $0)) >= 0;     # Output contains this file


=head2 ByteString::rdiInHex()

Add the content of register rdi in hexadecimal in big endian notation to a byte string


B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    Mov rdi, 0x88776655;
    Shl rdi, 32;
    Or  rdi, 0x44332211;

    $s->rdiInHex;                                                                 # Append a constant to the byte string
    $s->out;

    ok Assemble =~ m(8877665544332211);


=head2 ByteString::copy($byteString)

Append the byte string addressed by rdi to the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->q(my $t = 'ab');                                                          # Append a constant to the byte string
    $s->nl;                                                                       # New line

    Mov rdi, rax;                                                                 # Save source byte string
    CreateByteString;                                                             # Create target byte string
    $s->copy;                                                                     # Copy source to target

    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;                                                                     # Copy source to target
    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;

    Xchg rdi, rax;
    $s->copy;
    Xchg rdi, rax;
    $s->copy;

    $s->out;                                                                      # Print byte string
    $s->clear;                                                                    # Clear byte string

    my $T = "$t
" x 8;                                                           # Expected response
    ok Assemble =~ m($T)s;                                                        # Assemble and execute


=head2 ByteString::clear($byteString)

Clear the byte string addressed by rax

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->q(my $t = 'ab');                                                          # Append a constant to the byte string
    $s->nl;                                                                       # New line

    Mov rdi, rax;                                                                 # Save source byte string
    CreateByteString;                                                             # Create target byte string
    $s->copy;                                                                     # Copy source to target

    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;                                                                     # Copy source to target
    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;

    Xchg rdi, rax;
    $s->copy;
    Xchg rdi, rax;
    $s->copy;

    $s->out;                                                                      # Print byte string
    $s->clear;                                                                    # Clear byte string

    my $T = "$t
" x 8;                                                           # Expected response
    ok Assemble =~ m($T)s;                                                        # Assemble and execute


=head2 ByteString::write($byteString)

Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write;                                                                    # Write code to a temporary file
    $s->bash;                                                                     # Execute the temporary file
    $s->unlink;                                                                   # Execute the temporary file

    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);


=head2 ByteString::read($byteString)

Read the file named in the byte string (terminated with a zero byte) addressed by rax and place it into the byte string after clearing the byte string to remove the file name contained therein.

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->q($0);                                                                    # Append a constant to the byte string
    $s->z;                                                                        # New line
    $s->read;
    $s->out;

    my $r = Assemble;
    ok index(removeNonAsciiChars($r), removeNonAsciiChars(readFile $0)) >= 0;     # Output contains this file


=head2 ByteString::out($byteString)

Print the specified byte string addressed by rax on sysout

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->q(my $t = 'ab');                                                          # Append a constant to the byte string
    $s->nl;                                                                       # New line

    Mov rdi, rax;                                                                 # Save source byte string
    CreateByteString;                                                             # Create target byte string
    $s->copy;                                                                     # Copy source to target

    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;                                                                     # Copy source to target
    Xchg rdi, rax;                                                                # Swap source and target byte strings
    $s->copy;

    Xchg rdi, rax;
    $s->copy;
    Xchg rdi, rax;
    $s->copy;

    $s->out;                                                                      # Print byte string
    $s->clear;                                                                    # Clear byte string

    my $T = "$t
" x 8;                                                           # Expected response
    ok Assemble =~ m($T)s;                                                        # Assemble and execute

    my $s = CreateByteString;                                                     # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write;                                                                    # Write code to a temporary file
    $s->bash;                                                                     # Execute the temporary file
    $s->unlink;                                                                   # Execute the temporary file

    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);


=head2 ByteString::bash($byteString)

Execute the file named in the byte string addressed by rax with bash

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write;                                                                    # Write code to a temporary file
    $s->bash;                                                                     # Execute the temporary file
    $s->unlink;                                                                   # Execute the temporary file

    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);


=head2 ByteString::unlink($byteString)

Unlink the file named in the byte string addressed by rax with bash

     Parameter    Description
  1  $byteString  Byte string descriptor

B<Example:>


    my $s = CreateByteString;                                                     # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write;                                                                    # Write code to a temporary file
    $s->bash;                                                                     # Execute the temporary file
    $s->unlink;                                                                   # Execute the temporary file

    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);


=head2 ByteString::dump($byteString)

Dump details of a byte string

     Parameter    Description
  1  $byteString  Byte string descriptor

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


=head1 Block Strings

Strings made from zmm sized blocks of text

=head2 ByteString::CreateBlockString($byteString)

Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the byte string addressed by rax and return its descriptor

     Parameter    Description
  1  $byteString  Byte string description

=head2 BlockString::allocBlock($blockString)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter     Description
  1  $blockString  Block string descriptor

=head2 BlockString::getBlockLength($blockString, $block)

Get the length of the block at the specified offset and return it as a new variable

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $block        Variable containing offset of block whose length we want

=head2 BlockString::setBlockLength($blockString, $block, $length)

Set the length of the specified block to the specified length

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $block        Number of xmm register addressing block
  3  $length       New length in a byte register

=head2 BlockString::getBlock($blockString, $block)

Get the specified block in the specified block string and return its content as a variable

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $block        Number of zmm register to contain block

=head2 BlockString::putBlock($blockString, $block, $content)

Write the specified content into the specified block in the specified byte string.

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $block        Blosk in byte string
  3  $content      Content variable

=head2 BlockString::getNextBlock($blockString, $block)

Get the offset of the next block from the specified block in the specified block string and return it as a variable

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $block        Variable addressing current bloxk

=head2 BlockString::getPrevBlock($blockString, $block)

Get the prev block from the block addressed by the numbered xmm register and return it in the same xmm

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $block        Variable addressing current bloxk

=head2 BlockString::putNext($blockString, $old, $new)

Link the specified new block after the specified existing block in the specified block string

     Parameter     Description
  1  $blockString  Block string
  2  $old          Number of xmm addressing existing old block in string
  3  $new          Number of xmm addressing new block to be added

=head2 BlockString::append($blockString, $source, $length)

Append the specified content in memory to the specified block string

     Parameter     Description
  1  $blockString  Block string descriptor
  2  $source       Variable addressing source
  3  $length       Variable containing length of source

=head1 Tree

Tree operations

=head2 GenTree($keyLength, $dataLength)

Generate a set of routines to manage a tree held in a byte string with key and data fields of specified widths.  Allocate a byte string to contain the tree, return its address in xmm0=(0, tree).

     Parameter    Description
  1  $keyLength   Fixed key length in bytes
  2  $dataLength  Fixed data length in bytes

B<Example:>



    my $t = GenTree(2,2);                                                         # Tree description  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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


=head1 Assemble

Assemble generated code

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


    PrintOutString "Hello World";


    ok Assemble =~ m(Hello World);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲




=head2 BlockString Definition


Block string definition




=head3 Output fields


=head4 address

Variable addressing first block in string

=head4 bsAddress

Variable addressing backing byte string

=head4 byteString

Bytes string definition

=head4 length

Variable containing maximum length in a block

=head4 next

Location of next offset in block in dwords

=head4 offset

Size of an offset is size of eax

=head4 prev

Location of prev offset in block in dwords

=head4 size

Size of a block == size of a zmm register



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


=head2 ByteString::updateSpace($byteString)

Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi

     Parameter    Description
  1  $byteString  Byte string descriptor

=head2 removeNonAsciiChars($string)

Return a copy of the specified string with all the non ascii characters removed

     Parameter  Description
  1  $string    String

=head2 develop()

Developing


=head2 totalBytesAssembled()

Total size in bytes of all files assembled during testing



=head1 Index


1 L<All8Structure|/All8Structure> - Create a structure consisting of 8 byte fields

2 L<AllocateAll8OnStack|/AllocateAll8OnStack> - Create a local data descriptor consisting of the specified number of 8 byte local variables and return an array: (local data descriptor,  variable definitions.

3 L<AllocateMemory|/AllocateMemory> - Allocate the amount of memory specified in rax via mmap and return the address of the allocated memory in rax

4 L<Assemble|/Assemble> - Assemble the generated code

5 L<BlockString::allocBlock|/BlockString::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

6 L<BlockString::append|/BlockString::append> - Append the specified content in memory to the specified block string

7 L<BlockString::getBlock|/BlockString::getBlock> - Get the specified block in the specified block string and return its content as a variable

8 L<BlockString::getBlockLength|/BlockString::getBlockLength> - Get the length of the block at the specified offset and return it as a new variable

9 L<BlockString::getNextBlock|/BlockString::getNextBlock> - Get the offset of the next block from the specified block in the specified block string and return it as a variable

10 L<BlockString::getPrevBlock|/BlockString::getPrevBlock> - Get the prev block from the block addressed by the numbered xmm register and return it in the same xmm

11 L<BlockString::putBlock|/BlockString::putBlock> - Write the specified content into the specified block in the specified byte string.

12 L<BlockString::putNext|/BlockString::putNext> - Link the specified new block after the specified existing block in the specified block string

13 L<BlockString::setBlockLength|/BlockString::setBlockLength> - Set the length of the specified block to the specified length

14 L<ByteString::allocate|/ByteString::allocate> - Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi

15 L<ByteString::bash|/ByteString::bash> - Execute the file named in the byte string addressed by rax with bash

16 L<ByteString::char|/ByteString::char> - Append a character expressed as a decimal number to the byte string addressed by rax

17 L<ByteString::clear|/ByteString::clear> - Clear the byte string addressed by rax

18 L<ByteString::copy|/ByteString::copy> - Append the byte string addressed by rdi to the byte string addressed by rax

19 L<ByteString::CreateBlockString|/ByteString::CreateBlockString> - Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the byte string addressed by rax and return its descriptor

20 L<ByteString::dump|/ByteString::dump> - Dump details of a byte string

21 L<ByteString::m|/ByteString::m> - Append the content with length rdi addressed by rsi to the byte string addressed by rax

22 L<ByteString::makeReadOnly|/ByteString::makeReadOnly> - Make a byte string read only

23 L<ByteString::makeWriteable|/ByteString::makeWriteable> - Make a byte string writable

24 L<ByteString::nl|/ByteString::nl> - Append a new line to the byte string addressed by rax

25 L<ByteString::out|/ByteString::out> - Print the specified byte string addressed by rax on sysout

26 L<ByteString::q|/ByteString::q> - Append a quoted string == a constant to the byte string addressed by rax

27 L<ByteString::ql|/ByteString::ql> - Append a quoted string containing new line characters to the byte string addressed by rax

28 L<ByteString::rdiInHex|/ByteString::rdiInHex> - Add the content of register rdi in hexadecimal in big endian notation to a byte string

29 L<ByteString::read|/ByteString::read> - Read the file named in the byte string (terminated with a zero byte) addressed by rax and place it into the byte string after clearing the byte string to remove the file name contained therein.

30 L<ByteString::unlink|/ByteString::unlink> - Unlink the file named in the byte string addressed by rax with bash

31 L<ByteString::updateSpace|/ByteString::updateSpace> - Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi

32 L<ByteString::write|/ByteString::write> - Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file

33 L<ByteString::z|/ByteString::z> - Append a trailing zero to the byte string addressed by rax

34 L<ClearMemory|/ClearMemory> - Clear memory - the address of the memory is in rax, the length in rdi

35 L<ClearRegisters|/ClearRegisters> - Clear registers by setting them to zero

36 L<ClearZF|/ClearZF> - Clear the zero flag

37 L<CloseFile|/CloseFile> - Close the file whose descriptor is in rax

38 L<Comment|/Comment> - Insert a comment into the assembly code

39 L<ConcatenateShortStrings|/ConcatenateShortStrings> - Concatenate the numbered source zmm containing a short string with the short string in the numbered target zmm.

40 L<Copy|/Copy> - Copy the source to the target register

41 L<CopyMemory|/CopyMemory> - Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi

42 L<cr|/cr> - Call a subroutine with a reordering of the registers.

43 L<CreateByteString|/CreateByteString> - Create an relocatable string of bytes in an arena and returns its address in rax

44 L<Cstrlen|/Cstrlen> - Length of the C style string addressed by rax returning the length in r15

45 L<cxr|/cxr> - Call a subroutine with a reordering of the xmm registers.

46 L<Db|/Db> - Layout bytes in the data segment and return their label

47 L<Dbwdq|/Dbwdq> - Layout data

48 L<Dd|/Dd> - Layout double words in the data segment and return their label

49 L<Decrement|/Decrement> - Decrement the specified register

50 L<develop|/develop> - Developing

51 L<Dq|/Dq> - Layout quad words in the data segment and return their label

52 L<Ds|/Ds> - Layout bytes in memory and return their label

53 L<Dw|/Dw> - Layout words in the data segment and return their label

54 L<Exit|/Exit> - Exit with the specified return code or zero if no return code supplied.

55 L<Float32|/Float32> - 32 bit float

56 L<Float64|/Float64> - 64 bit float

57 L<For|/For> - For - iterate the body as long as register is less than limit incrementing by increment each time

58 L<ForIn|/ForIn> - For - iterate the body as long as register plus increment is less than than limit incrementing by increment each time

59 L<Fork|/Fork> - Fork

60 L<FreeMemory|/FreeMemory> - Free memory via munmap.

61 L<GenTree|/GenTree> - Generate a set of routines to manage a tree held in a byte string with key and data fields of specified widths.

62 L<GetLengthOfShortString|/GetLengthOfShortString> - Get the length of the short string held in the numbered zmm register into the specified register

63 L<GetPid|/GetPid> - Get process identifier

64 L<GetPidInHex|/GetPidInHex> - Get process identifier in hex as 8 zero terminated bytes in rax

65 L<GetPPid|/GetPPid> - Get parent process identifier

66 L<GetUid|/GetUid> - Get userid of current process

67 L<Hash|/Hash> - Hash a string addressed by rax with length held in rdi and return the hash code in r15

68 L<hexTranslateTable|/hexTranslateTable> - Create/address a hex translate table and return its label

69 L<If|/If> - If

70 L<IfEq|/IfEq> - If equal execute the then body else the else body

71 L<IfGe|/IfGe> - If greater than or equal execute the then body else the else body

72 L<IfGt|/IfGt> - If greater than execute the then body else the else body

73 L<IfLe|/IfLe> - If less than or equal execute the then body else the else body

74 L<IfLt|/IfLt> - If less than execute the then body else the else body

75 L<IfNe|/IfNe> - If not equal execute the then body else the else body

76 L<IfNz|/IfNz> - If not zero execute the then body else the else body

77 L<Increment|/Increment> - Increment the specified register

78 L<InsertIntoXyz|/InsertIntoXyz> - Shift and insert the specified word, double, quad from rax or the contents of xmm0 into the specified xyz register at the specified position shifting data above it to the left towards higher order bytes.

79 L<Keep|/Keep> - Mark free registers so that they are not updated until we Free them or complain if the register is already in use.

80 L<KeepFree|/KeepFree> - Free registers so that they can be reused

81 L<KeepPop|/KeepPop> - Reset the status of the specified registers to the status quo ante the last push

82 L<KeepPush|/KeepPush> - Push the current status of the specified registers and then mark them as free

83 L<KeepReturn|/KeepReturn> - Pop the specified register and mark it as in use to effect a subroutine return with this register.

84 L<KeepSet|/KeepSet> - Confirm that the specified registers are in use

85 L<Label|/Label> - Create a unique label

86 L<LoadShortStringFromMemoryToZmm|/LoadShortStringFromMemoryToZmm> - Load the short string addressed by rax into the zmm register with the specified number

87 L<LoadShortStringFromMemoryToZmm2|/LoadShortStringFromMemoryToZmm2> - Load the short string addressed by rax into the zmm register with the specified number

88 L<LoadTargetZmmFromSourceZmm|/LoadTargetZmmFromSourceZmm> - Load bytes in the numbered target zmm register at a register specified offset with source bytes from a numbered source zmm register at a specified register offset for a specified register length.

89 L<LoadZmmFromMemory|/LoadZmmFromMemory> - Load bytes into the numbered target zmm register at a register specified offset with source bytes from memory addressed by a specified register for a specified register length from memory addressed by a specified register.

90 L<LocalData|/LocalData> - Map local data

91 L<LocalData::allocate8|/LocalData::allocate8> - Add some 8 byte local variables and return an array of variable definitions

92 L<LocalData::free|/LocalData::free> - Free a local data area on the stack

93 L<LocalData::start|/LocalData::start> - Start a local data area on the stack

94 L<LocalData::variable|/LocalData::variable> - Add a local variable

95 L<LocalVariable::stack|/LocalVariable::stack> - Address a local variable on the stack

96 L<MaximumOfTwoRegisters|/MaximumOfTwoRegisters> - Return in the specified register the value in the second register if it is greater than the value in the first register

97 L<MinimumOfTwoRegisters|/MinimumOfTwoRegisters> - Return in the specified register the value in the second register if it is less than the value in the first register

98 L<Minus|/Minus> - Subtract the third operand from the second operand and place the result in the first operand

99 L<OpenRead|/OpenRead> - Open a file, whose name is addressed by rax, for read and return the file descriptor in rax

100 L<OpenWrite|/OpenWrite> - Create the file named by the terminated string addressed by rax for write

101 L<PeekR|/PeekR> - Peek at register on stack

102 L<Plus|/Plus> - Add the last operands and place the result in the first operand

103 L<PopR|/PopR> - Pop registers from the stack

104 L<PopRR|/PopRR> - Pop registers from the stack without tracking

105 L<PrintOutMemory|/PrintOutMemory> - Print the memory addressed by rax for a length of rdi

106 L<PrintOutMemoryInHex|/PrintOutMemoryInHex> - Dump memory from the address in rax for the length in rdi

107 L<PrintOutMemoryInHexNL|/PrintOutMemoryInHexNL> - Dump memory from the address in rax for the length in rdi and then print a new line

108 L<PrintOutMemoryNL|/PrintOutMemoryNL> - Print the memory addressed by rax for a length of rdi followed by a new line

109 L<PrintOutNL|/PrintOutNL> - Print a new line to stdout

110 L<PrintOutRaxInHex|/PrintOutRaxInHex> - Write the content of register rax to stderr in hexadecimal in big endian notation

111 L<PrintOutRaxInReverseInHex|/PrintOutRaxInReverseInHex> - Write the content of register rax to stderr in hexadecimal in little endian notation

112 L<PrintOutRegisterInHex|/PrintOutRegisterInHex> - Print any register as a hex string

113 L<PrintOutRegistersInHex|/PrintOutRegistersInHex> - Print the general purpose registers in hex

114 L<PrintOutRflagsInHex|/PrintOutRflagsInHex> - Print the flags register in hex

115 L<PrintOutRipInHex|/PrintOutRipInHex> - Print the instruction pointer in hex

116 L<PrintOutString|/PrintOutString> - Print a constant string to sysout.

117 L<PrintOutStringNL|/PrintOutStringNL> - Print a constant string to sysout followed by new line

118 L<PrintOutZF|/PrintOutZF> - Print the zero flag without disturbing it

119 L<PushR|/PushR> - Push registers onto the stack

120 L<PushRR|/PushRR> - Push registers onto the stack without tracking

121 L<Rb|/Rb> - Layout bytes in the data segment and return their label

122 L<Rbwdq|/Rbwdq> - Layout data

123 L<Rd|/Rd> - Layout double words in the data segment and return their label

124 L<ReadFile|/ReadFile> - Read a file whose name is addressed by rax into memory.

125 L<ReadTimeStampCounter|/ReadTimeStampCounter> - Read the time stamp counter and return the time in nanoseconds in rax

126 L<RegisterSize|/RegisterSize> - Return the size of a register

127 L<removeNonAsciiChars|/removeNonAsciiChars> - Return a copy of the specified string with all the non ascii characters removed

128 L<ReorderSyscallRegisters|/ReorderSyscallRegisters> - Map the list of registers provided to the 64 bit system call sequence

129 L<ReorderXmmRegisters|/ReorderXmmRegisters> - Map the list of xmm registers provided to 0-31

130 L<RestoreFirstFour|/RestoreFirstFour> - Restore the first 4 parameter registers

131 L<RestoreFirstFourExceptRax|/RestoreFirstFourExceptRax> - Restore the first 4 parameter registers except rax so it can return its value

132 L<RestoreFirstFourExceptRaxAndRdi|/RestoreFirstFourExceptRaxAndRdi> - Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values

133 L<RestoreFirstSeven|/RestoreFirstSeven> - Restore the first 7 parameter registers

134 L<RestoreFirstSevenExceptRax|/RestoreFirstSevenExceptRax> - Restore the first 7 parameter registers except rax which is being used to return the result

135 L<RestoreFirstSevenExceptRaxAndRdi|/RestoreFirstSevenExceptRaxAndRdi> - Restore the first 7 parameter registers except rax and rdi which are being used to return the results

136 L<Rq|/Rq> - Layout quad words in the data segment and return their label

137 L<Rs|/Rs> - Layout bytes in read only memory and return their label

138 L<Rw|/Rw> - Layout words in the data segment and return their label

139 L<S|/S> - Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub

140 L<SaveFirstFour|/SaveFirstFour> - Save the first 4 parameter registers making any parameter registers read only

141 L<SaveFirstSeven|/SaveFirstSeven> - Save the first 7 parameter registers

142 L<SetLabel|/SetLabel> - Set a label in the code section

143 L<SetLengthOfShortString|/SetLengthOfShortString> - Set the length of the short string held in the numbered zmm register into the specified register

144 L<SetMaskRegister|/SetMaskRegister> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

145 L<SetRegisterToMinusOne|/SetRegisterToMinusOne> - Set the specified register to -1

146 L<SetZF|/SetZF> - Set the zero flag

147 L<Start|/Start> - Initialize the assembler

148 L<StatSize|/StatSize> - Stat a file whose name is addressed by rax to get its size in rax

149 L<Structure|/Structure> - Create a structure addressed by a register

150 L<Structure::field|/Structure::field> - Add a field of the specified length with an optional comment

151 L<StructureField::addr|/StructureField::addr> - Address a field in a structure by either the default register or the named register

152 L<totalBytesAssembled|/totalBytesAssembled> - Total size in bytes of all files assembled during testing

153 L<UnReorderSyscallRegisters|/UnReorderSyscallRegisters> - Recover the initial values in registers that were reordered

154 L<UnReorderXmmRegisters|/UnReorderXmmRegisters> - Recover the initial values in the xmm registers that were reordered

155 L<Variable|/Variable> - Create a new variable with the specified size and name initialized via an expression

156 L<Variable::add|/Variable::add> - Add the right hand variable to the left hand variable and return the result as a new variable

157 L<Variable::address|/Variable::address> - Get the address of a variable

158 L<Variable::and|/Variable::and> - And two variables

159 L<Variable::arithmetic|/Variable::arithmetic> - Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables

160 L<Variable::boolean|/Variable::boolean> - Combine the left hand variable with the right hand variable via a boolean operator

161 L<Variable::dec|/Variable::dec> - Decrement a variable

162 L<Variable::divide|/Variable::divide> - Divide the left hand variable by the right hand variable and return the result as a new variable

163 L<Variable::division|/Variable::division> - Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side

164 L<Variable::dump|/Variable::dump> - Dump the value of a variable on stdout

165 L<Variable::eq|/Variable::eq> - Check whether the left hand variable is equal to the right hand variable

166 L<Variable::for|/Variable::for> - Iterate the body from 0 limit times.

167 L<Variable::ge|/Variable::ge> - Check whether the left hand variable is greater than or equal to the right hand variable

168 L<Variable::getReg|/Variable::getReg> - Load the variable from the named register

169 L<Variable::getZmm|/Variable::getZmm> - Load bytes from the memory addressed by the source variable into the numbered zmm register.

170 L<Variable::gt|/Variable::gt> - Check whether the left hand variable is greater than the right hand variable

171 L<Variable::inc|/Variable::inc> - Increment a variable

172 L<Variable::incDec|/Variable::incDec> - Increment or decrement a variable

173 L<Variable::le|/Variable::le> - Check whether the left hand variable is less than or equal to the right hand variable

174 L<Variable::lt|/Variable::lt> - Check whether the left hand variable is less than the right hand variable

175 L<Variable::max|/Variable::max> - Maximum of two variables

176 L<Variable::min|/Variable::min> - Minimum of two variables

177 L<Variable::mod|/Variable::mod> - Divide the left hand variable by the right hand variable and return the remainder as a new variable

178 L<Variable::ne|/Variable::ne> - Check whether the left hand variable is not equal to the right hand variable

179 L<Variable::or|/Variable::or> - Or two variables

180 L<Variable::print|/Variable::print> - Write the value of a variable on stdout

181 L<Variable::putZmm|/Variable::putZmm> - Write bytes into the memory addressed by the source variable from the numbered zmm register.

182 L<Variable::setMask|/Variable::setMask> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

183 L<Variable::setReg|/Variable::setReg> - Set the named register from the content of the variable

184 L<Variable::setZmm|/Variable::setZmm> - Load bytes from the memory addressed by the source variable into the numbered zmm register at a specified offset moving the specified number of bytes

185 L<Variable::str|/Variable::str> - The name of the variable

186 L<Variable::sub|/Variable::sub> - Subtract the right hand variable from the left hand variable and return the result as a new variable

187 L<Variable::times|/Variable::times> - Multiply the left hand variable by the right hand variable and return the result as a new variable

188 L<Vb|/Vb> - Define a byte variable

189 L<Vd|/Vd> - Define a double word variable

190 L<Vq|/Vq> - Define a quad variable

191 L<Vw|/Vw> - Define a word variable

192 L<Vx|/Vx> - Define an xmm variable

193 L<Vy|/Vy> - Define a ymm variable

194 L<Vz|/Vz> - Define a zmm variable

195 L<WaitPid|/WaitPid> - Wait for the pid in rax to complete

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
use Test::More;

my $develop   = -e q(/home/phil/);                                              # Developing
my $localTest = ((caller(1))[0]//'Nasm::X86') eq "Nasm::X86";                   # Local testing mode

Test::More->builder->output("/dev/null") if $localTest;                         # Reduce number of confirmation messages during testing

if ($^O =~ m(bsd|linux)i)                                                       # Supported systems
 {if (confirmHasCommandLineCommand(q(nasm)) and LocateIntelEmulator)            # Network assembler and Intel Software Development emulator
   {plan tests => 80;
   }
  else
   {plan skip_all =>qq(Nasm or Intel 64 emulator not available);
   }
 }
else
 {plan skip_all =>qq(Not supported on: $^O);
 }

my $start = time;                                                               # Tests

eval {goto latest} unless caller(0);

if (1) {                                                                        #TPrintOutStringNL #TPrintErrStringNL #TAssemble
  PrintOutStringNL "Hello World";
  PrintErrStringNL "Hello World";

  is_deeply Assemble, <<END;
Hello World
Hello World
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

if (1) {                                                                        #TAllocateMemory #TVariable::freeMemory
  my $N = Vq(size, 2048);
  my $q = Rs('a'..'p');
  AllocateMemory->call($N, my $address = Vq(address));
  $address->dump;

  Vmovdqu8 xmm0, "[$q]";
  $address->setReg(rax);
  Vmovdqu8 "[rax]", xmm0;
  Mov rdi, 16;
  PrintOutMemory;
  PrintOutNL;

  FreeMemory->call(address => $address, size=> $N);

  ok Assemble =~ m(address: 0000.*abcdefghijklmnop)s;
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

  Mov rax, Rs(my $f = "zzz.txt");                                               # File to write
  OpenWrite;                                                                    # Open file
  CloseFile;                                                                    # Close file

  my $r = Assemble;
  ok $r =~ m(( 0000){3} 0003)i;                                                 # Expected file number
  ok $r =~ m(( 0000){4})i;                                                      # Expected file number
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

  AllocateMemory->call($N, my $A = Vq(address));
  $A->dump;

  ClearMemory->call($N, $A);

  $A->setReg(rax);
  $N->setReg(rdi);
  PrintOutMemoryInHex;

  FreeMemory->call($N, $A);

  my $r = Assemble;
  if ($r =~ m((0000.*0000))s)
   {is_deeply length($1), 9748;
   }
 }

if (1) {                                                                        #TCall #TS
  Mov rax, 0x44332211;
  PrintOutRegisterInHex rax;

  my $s = S
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
  ReadFile->call(Vq(file, Rs($0)));                                             # Read file
  PrintOutMemory;                                                               # Print memory

  my $r = Assemble;                                                             # Assemble and execute
  ok index(removeNonAsciiChars($r), removeNonAsciiChars(readFile $0)) >= 0;     # Output contains this file
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
  $a->append->call(target=>$b->bs, source=>$a->bs);
  $a->append->call(target=>$b->bs, source=>$a->bs);
  $a->append->call(target=>$a->bs, source=>$b->bs);
  $a->append->call(target=>$b->bs, source=>$a->bs);
  $a->append->call(target=>$a->bs, source=>$b->bs);
  $a->append->call(target=>$b->bs, source=>$a->bs);
  $a->append->call(target=>$b->bs, source=>$a->bs);
  $a->append->call(target=>$b->bs, source=>$a->bs);
  $a->append->call(target=>$b->bs, source=>$a->bs);


  $a->out;   PrintOutNL;                                                        # Print byte string
  $b->out;   PrintOutNL;                                                        # Print byte string
  $a->clear;
  $a->out;                                                                      # Clear byte string

  is_deeply Assemble, <<END;                                                    # Assemble and execute
abababababababab
ababababababababababababababababababababababababababababababababababababab
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

if (1) {                                                                        # Print this file  #TByteString::read #TByteString::z #TByteString::q
  my $s = CreateByteString;                                                     # Create a string
  $s->q($0);                                                                    # Append a constant to the byte string
  $s->z;                                                                        # Trailing zero
  $s->read;
  $s->out;

  my $r = Assemble;
  ok index(removeNonAsciiChars($r), removeNonAsciiChars(readFile $0)) >= 0;     # Output contains this file
 }

if (1) {                                                                        # Print rdi in hex into a byte string #TByteString::rdiInHex
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

if (1) {                                                                        # Write a hex string to a temporary file
  my $s = CreateByteString;                                                     # Create a string
  Mov rdi, 0x88776655;                                                          # Write into string
  Shl rdi, 32;
  Or  rdi, 0x44332211;
  $s->rdiInHex;                                                                 # Append a constant to the byte string
  $s->write;                                                                    # Write the byte string to a temporary file
  $s->out;                                                                      # Write the name of the temporary file

  ok Assemble =~ m(tmp);
 }

if (1) {                                                                        # Execute the content of a byte string #TByteString::bash #TByteString::write #TByteString::out #TByteString::unlink #TByteString::ql
  my $s = CreateByteString;                                                     # Create a string
  $s->ql(<<END);                                                                # Write code to execute
#!/usr/bin/bash
whoami
ls -la
pwd
END
  $s->write;                                                                    # Write code to a temporary file
  $s->bash;                                                                     # Execute the temporary file
  $s->unlink;                                                                   # Execute the temporary file

  my $u = qx(whoami); chomp($u);
  ok Assemble(emulator=>0) =~ m($u);
 }

if (1) {                                                                        # Make a byte string readonly
  my $s = CreateByteString;                                                     # Create a byte string
  $s->q("Hello");                                                               # Write code to byte string
  $s->makeReadOnly;                                                             # Make byte string read only
  $s->q(" World");                                                              # Try to write to byte string

  ok Assemble =~ m(SDE ERROR: DEREFERENCING BAD MEMORY POINTER.*mov byte ptr .rax.rdx.1., r8b);
 }

if (1) {                                                                        # Make a read only byte string writable  #TByteString::makeReadOnly #TByteString::makeWriteable
  my $s = CreateByteString;                                                     # Create a byte string
  $s->q("Hello");                                                               # Write data to byte string
  $s->makeReadOnly;                                                             # Make byte string read only - tested above
  $s->makeWriteable;                                                             # Make byte string writable again
  $s->q(" World");                                                              # Try to write to byte string
  $s->out;

  ok Assemble =~ m(Hello World);
 }

if (1) {                                                                        # Allocate some space in byte string #TByteString::allocate
  my $s = CreateByteString;                                                     # Create a byte string
  Mov r8,  rax;
  Mov rdi, my $w = 0x20;                                                        # Space wanted
  $s->allocate;                                                                 # Allocate space wanted
  PrintOutRegisterInHex rdi;
  KeepFree rdi;
  Mov rdi, $w;                                                                  # Space wanted
  $s->allocate;                                                                 # Allocate space wanted
  PrintOutRegisterInHex rdi;

  my $e = sprintf("rdi: 0000 0000 0000 %04X", $s->structure->size);             # Expected results
  my $E = sprintf("rdi: 0000 0000 0000 %04X", $s->structure->size+$w);
  ok Assemble =~ m($e.*$E)s;
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

# Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
  Mov rax, rsp;
  Mov rdi, 16;
  Mov rsi, $s;
  CopyMemory;
  PrintOutMemoryInHex;

  my $r = Assemble;
  ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
  ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
  ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);
 }

if (1) {                                                                        #T
  my $N = 256;
  my $s = Rb 0..$N-1;
  Mov rax, $N;
  my $a = AllocateMemory;
  Mov rdi, $N;
  Mov rsi, $s;
  CopyMemory;
  KeepFree rax, rdi, rsi;

  Mov rax, $N;
  my $b = AllocateMemory;

  $b->clearMemory;
  $b->copyMemoryFrom($a);
  $b->printOutMemoryInHex;

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

if (1) {                                                                        #TVq  #TVariable::print #TVariable::add
  my $a = Vq(a, 3);   $a->print;
  my $c = $a +  2;    $c->print;
  my $d = $c -  $a;   $d->print;
  my $e = $d == 2;    $e->print;
  my $f = $d != 2;    $f->print;
  my $g = $a *  2;    $g->print;
  my $h = $g /  2;    $h->print;
  my $i = $a %  2;    $i->print;

  If($a == 3, sub{PrintOutStringNL "a == 3"});

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

if (1) {                                                                        #TVariable::dump  #TVariable::print
  my $a = Vq(a, 3); $a->dump;
  my $b = Vq(b, 2); $b->dump;
  my $c = $a +  $b; $c->print;
  my $d = $c -  $a; $d->print;
  my $e = $d == $b; $e->print;
  my $f = $d != $b; $f->print;
  my $g = $a *  $b; $g->print;
  my $h = $g /  $b; $h->print;
  my $i = $a %  $b; $i->print;

  If($a == 3, sub{PrintOutStringNL "a == 3"});

  is_deeply Assemble, <<END;
a: 0000 0000 0000 0003
b: 0000 0000 0000 0002
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

if (1) {                                                                        #TVariable::dump
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

if (1) {                                                                        #TVariable::min #TVariable::max
  my $a = Vq("a", 1);
  my $b = Vq("b", 2);
  my $c = $a->min($b);
  my $d = $a->max($b);
  $a->dump;
  $b->dump;
  $c->dump;
  $d->dump;

  is_deeply Assemble,<<END;
a: 0000 0000 0000 0001
b: 0000 0000 0000 0002
Minimum(a, b): 0000 0000 0000 0001
Maximum(a, b): 0000 0000 0000 0002
END
 }

if (1) {                                                                        #TVariable::setMask
  my $start  = Vq("Start",  7);
  my $length = Vq("Length", 3);
  $start->setMask($length, k7);
  PrintOutRegisterInHex k7;

  is_deeply Assemble, <<END;
    k7: 0000 0000 0000 0380
END
 }

if (1) {                                                                        #TVariable::setZmm
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

if (1) {                                                                        #TVariable::getZmm  #TVariable::setZmm
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

if (1) {                                                                        #TgetDFromZmmAsVariable #TVariable::putDIntoZmm
  my $s = Rb(0..8);
  my $c = Vq("Content",   "[$s]");
     $c->putBIntoZmm(0,  4);
     $c->putWIntoZmm(0,  6);
     $c->putDIntoZmm(0, 10);
     $c->putQIntoZmm(0, 16);
  PrintOutRegisterInHex zmm0;
  getBFromZmmAsVariable(0, 12)->dump;
  getWFromZmmAsVariable(0, 12)->dump;
  getDFromZmmAsVariable(0, 12)->dump;
  getQFromZmmAsVariable(0, 12)->dump;

  is_deeply Assemble, <<END;
  zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0706 0504 0302 0100   0000 0302 0100 0000   0100 0000 0000 0000
b at offset 12 in zmm0: 0000 0000 0000 0002
w at offset 12 in zmm0: 0000 0000 0000 0302
d at offset 12 in zmm0: 0000 0000 0000 0302
q at offset 12 in zmm0: 0302 0100 0000 0302
END
 }

if (1) {                                                                        #TCreateBlockString
  my $s = Rb(0..128);
  my $B = CreateByteString;
  my $b = $B->CreateBlockString(0);
  $b->append(Vq("Source String", $s), Vq("Source Length", 3));
  $b->append(Vq("Source String", $s), Vq("Source Length", 4));
  $b->append(Vq("Source String", $s), Vq("Source Length", 5));

  $b->dump;

  is_deeply Assemble, <<END;
BlockString at address: 0000 0000 0000 0010
Length: 0000 0000 0000 000C
 zmm31: 0000 0010 0000 0010   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0004 0302 0100   0302 0100 0201 000C
END
 }

if (1) {
  my $s = Rb(0..128);
  my $B = CreateByteString;
  my $b = $B->CreateBlockString(0);
  $b->append(Vq("Source String", $s), Vq("Source Length", 58));
  $b->append(Vq("Source String", $s), Vq("Source Length", 52));
  $b->append(Vq("Source String", $s), Vq("Source Length", 51));
  $b->dump;

  $b->append(Vq("Source String", $s), Vq("Source Length",  2));
  $b->dump;

  is_deeply Assemble, <<END;
BlockString at address: 0000 0000 0000 0010
Length: 0000 0000 0000 0037
 zmm31: 0000 0090 0000 0050   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0050
Length: 0000 0000 0000 0037
 zmm31: 0000 0010 0000 0090   3332 3130 2F2E 2D2C   2B2A 2928 2726 2524   2322 2120 1F1E 1D1C   1B1A 1918 1716 1514   1312 1110 0F0E 0D0C   0B0A 0908 0706 0504   0302 0100 3938 3737
Offset: 0000 0000 0000 0090
Length: 0000 0000 0000 0033
 zmm31: 0000 0050 0000 0010   0000 0000 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0033
BlockString at address: 0000 0000 0000 0010
Length: 0000 0000 0000 0037
 zmm31: 0000 0090 0000 0050   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0050
Length: 0000 0000 0000 0037
 zmm31: 0000 0010 0000 0090   3332 3130 2F2E 2D2C   2B2A 2928 2726 2524   2322 2120 1F1E 1D1C   1B1A 1918 1716 1514   1312 1110 0F0E 0D0C   0B0A 0908 0706 0504   0302 0100 3938 3737
Offset: 0000 0000 0000 0090
Length: 0000 0000 0000 0035
 zmm31: 0000 0050 0000 0010   0000 0100 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0035
END
 }

if (1) {
  my $s = S2
   {my ($parameters) = @_;                                                      #
    $$parameters{a}->setReg(rax);
    $$parameters{b}->setReg(rdx);
    Add rax, rdx;
    $$parameters{c}->getReg(rax);
   } in=>{a=>3, b=>3}, out=>{c=>3};

  $s->call(Vq(a, 1), Vq(b, 2), c => my $c1 = Vq(c1));
  $c1->dump;

  $s->call(Vq(a, 2), Vq(b, 3), c => my $c2 = Vq(c2));
  $c2->dump;

  is_deeply Assemble, <<END;
c1: 0000 0000 0000 0003
c2: 0000 0000 0000 0005
END
 }

if (0) {
  is_deeply Assemble, <<END;
END
 }

unlink $_ for qw(hash print2 sde-log.txt sde-ptr-check.out.txt z.asm z.txt);    # Remove incidental files
unlink $_ for grep {/\A\.\/atmpa/} findFiles('.');                              # Remove temporary files

lll "Finished:", time - $start,  "bytes assembled:",   totalBytesAssembled;
