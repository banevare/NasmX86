#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I. -I/home/phil/perl/cpan/AsmC/lib/
#-------------------------------------------------------------------------------
# Generate X86 assembler code using Perl as a macro pre-processor.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation
package Nasm::X86;
our $VERSION = "20210629";
use warnings FATAL => qw(all);
use strict;
use Carp qw(confess cluck);
use Data::Dump qw(dump);
use Data::Table::Text qw(confirmHasCommandLineCommand convertUtf32ToUtf8 currentDirectory evalFile fff fileMd5Sum fileSize findFiles firstNChars formatTable fpe fpf genHash lll owf pad readFile stringsAreNotEqual stringMd5Sum temporaryFile);
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

our $stdin  = 0;                                                                # File descriptor for standard input
our $stdout = 1;                                                                # File descriptor for standard output
our $stderr = 2;                                                                # File descriptor for standard error

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
pinsr pextr vpcmpeq vpinsr vpextr vpadd vpsub vpmull
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
sub PrintErrStringNL(@);                                                        # Print a constant string followed by a new line to stderr
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
  my @e;
  for my $e(split //, $d)
   {if ($e !~ m([A-Z0-9])i) {push @e, sprintf("0x%x", ord($e))} else {push @e, qq('$e')}
   }
  my $e = join ', ', @e;
  my $L = $rodatas{$e};
  return $L if defined $L;                                                      # Data already exists so return it
  my $l = Label;                                                                # New label for new data
  $rodatas{$e} = $l;                                                            # Record label
  push @rodata, <<END;                                                          # Define bytes
  $l: db  $e, 0;
END
  $l                                                                            # Return label
 }

sub Rutf8(@)                                                                    # Layout a utf8 encoded string as bytes in read only memory and return their label
 {my (@d) = @_;                                                                 # Data to be laid out
  confess unless @_;
  my $d = join '', @_;
  my @e;
  for my $e(split //, $d)
   {my $o  = ord $e;
    my $u  = convertUtf32ToUtf8($o);
    my $x = sprintf("%08x", $u);
    my $o1 = substr($x, 0, 2);
    my $o2 = substr($x, 2, 2);
    my $o3 = substr($x, 4, 2);
    my $o4 = substr($x, 6, 2);
    if    ($o <= (1 << 7))  {push @e,                $o4}
    elsif ($o <= (1 << 11)) {push @e,           $o3, $o4}
    elsif ($o <= (1 << 16)) {push @e,      $o2, $o3, $o4}
    else                    {push @e, $o1, $o2, $o3, $o4}
   }
  my $e = join ', ',map {"0x$_"}  @e;
  my $L = $rodatas{$e};
  return $L if defined $L;                                                      # Data already exists so return it
  my $l = Label;                                                                # New label for new data
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

sub xmm(@)                                                                      # Add xmm to the front of a list of register expressions
 {my (@r) = @_;                                                                 # Register numbers
  map {"xmm$_"} @_;
 }

sub ymm(@)                                                                      # Add ymm to the front of a list of register expressions
 {my (@r) = @_;                                                                 # Register numbers
  map {"ymm$_"} @_;
 }

sub zmm(@)                                                                      # Add zmm to the front of a list of register expressions
 {my (@r) = @_;                                                                 # Register numbers
  map {"zmm$_"} @_;
 }

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

#D2 Tracing                                                                     # Trace the execution of a program

my $Trace;                                                                      # Tracing level: 0 - no tracing
my $TraceCount;                                                                 # Trace count
my $TraceStop;                                                                  # Report the position of this trace count

sub Trace                                                                       # Add tracing code
 {return unless $Trace;
  ++$TraceCount;
  &PrintString(3, "$TraceCount\n");
  confess "Trace" if $TraceStop and $TraceStop == $TraceCount;
 }

#D2 Tracking                                                                    # Track the use of registers so that we do not accidently use unset registers or write into registers that are already in use.

my %Keep;                                                                       # Registers to keep
my %KeepStack;                                                                  # Registers keep stack across PushR and PopR

sub Keep(@)                                                                     # Mark free registers so that they are not updated until we Free them or complain if the register is already in use.
 {my (@target) = @_;                                                            # Registers to keep
  for my $target(@target)
   {my $r = $RegisterContaining{$target};                                       # Containing register
    $r or confess "No such register $target";
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

#D2 Mask                                                                        # Operations on mask registers

sub LoadConstantIntoMaskRegister($$)                                            # Load a constant into a mask register
 {my ($reg, $value) = @_;                                                       # Mask register to load, constant to load
  PushR rax;
  Mov rax, $value;                                                              # Load a general register
  Kmovq $reg, rax;                                                              # Load mask register
  PopR rax;
 }

#D1 Structured Programming                                                      # Structured programming constructs

sub If($$;$)                                                                    # If
 {my ($jump, $then, $else) = @_;                                                # Jump op code of variable, then - required , else - optional
  @_ >= 2 && @_ <= 3 or confess;

  ref($jump) or $jump =~ m(\AJ(e|g|ge|gt|h|l|le|ne|nz|z)\Z)
             or confess "Invalid jump: $jump";

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
    Trace;
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
    Trace;
    &$then;
    Jmp $endIf;
    SetLabel $startElse;
    Trace;
    &$else;
    SetLabel  $endIf;
   }
 }

sub Then(&)                                                                     # Then body for an If statement
 {my ($body) = @_;                                                              # Then body
  $body;
 }

sub Else(&)                                                                     # Else body for an If statement
 {my ($body) = @_;                                                              # Else body
  $body;
 }

sub IfEq(&;&)                                                                   # If equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jne), $then, $else);                                                     # Opposite code
 }

sub IfNe(&;&)                                                                   # If not equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Je), $then, $else);                                                      # Opposite code
 }

sub IfNz(&;&)                                                                   # If the zero is not set then execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jz), $then, $else);                                                      # Opposite code
 }

sub IfZ(&;&)                                                                    # If the zero is set then execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jnz), $then, $else);                                                     # Opposite code
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
    $p{$name} = Variable($size, $name);                                         # Make a value parameter variable
   }

  my sub checkIo($$)                                                            # Check an io parameter
   {my ($name, $size) = @_;
    confess "Invalid size $size for parameter: $name" unless $size =~ m(\A(1|2|3|4|5|6)\Z);
    $p{$name} = Vr($name, $size);                                               # Make a reference  parameter variable
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
  while(@parameters)                                                            # Copy parameters supplied by the caller
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
    $sub->variables->{$p}->copyAddress($v);
   }

  my $n = $$sub{name};
  Trace;
  Call $$sub{start};                                                            # Call the sub routine
  Trace;

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

sub Comment(@)                                                                  # Insert a comment into the assembly code
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  my ($p, $f, $l) = caller;
  push @text, <<END;
; $c at $f line $l
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
  Comment "Write to channel  $channel, the string: ".dump($c);
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

sub PrintRaxInHex($;$)                                                          # Write the content of register rax in hexadecimal in big endian notation to the specified channel
 {my ($channel, $end) = @_;                                                     # Channel, optional end byte
  @_ == 1 or @_ == 2 or confess;
  Comment "Print Rax In Hex on channel: $channel";
  my $hexTranslateTable = hexTranslateTable;
  $end //= 7;                                                                   # Default end byte

  my $sub = Macro
   {SaveFirstFour rax;                                                          # Rax is a parameter
    Mov rdx, rax;                                                               # Content to be printed
    Mov rdi, 2;                                                                 # Length of a byte in hex
    KeepFree rax;

    for my $i((7-$end)..7)                                                      # Each byte
     {my $s = 8*$i;
      KeepFree rax;
      Mov rax, rdx;
      Shl rax, $s;                                                              # Push selected byte high
      Shr rax, 56;                                                              # Push select byte low
      Shl rax, 1;                                                               # Multiply by two because each entry in the translation table is two bytes long
      Lea rax, "[$hexTranslateTable+rax]";
      PrintMemory($channel);                                                    # Print memory addressed by rax for length specified by rdi
      PrintString($channel, ' ') if $i % 2 and $i < 7;
     }
    RestoreFirstFour;
   } name => "PrintOutRaxInHexOn-$channel-$end";

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

sub PrintErrZF                                                                  # Print the zero flag without disturbing it on stderr
 {@_ == 0 or confess;

  Pushfq;
  IfNz {PrintErrStringNL "ZF=0"} sub {PrintErrStringNL "ZF=1"};
  Popfq;
 }

sub PrintOutZF                                                                  # Print the zero flag without disturbing it on stdout
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

sub Variable($$;$%)                                                             # Create a new variable with the specified size and name initialized via an expression
 {my ($size, $name, $expr, %options) = @_;                                      # Size as a power of 2, name of variable, optional expression initializing variable, options
  $size =~ m(\A0|1|2|3|4|5|6|b|w|d|q|x|y|z\Z)i or confess "Size must be 0..6 or b|w|d|q|x|y|z";# Check size of variable

  my $const = $options{constant} // 0;                                          # Whether the variable is in fact a constant
  if ($const)                                                                   # Comment in appropriate section
   {defined($expr) or confess "Value required for constant";
    defined($name) or confess "Name required";
    RComment qq(Constant name: "$name", size: $size, value $expr);
   }
  else
   {DComment qq(Variable name: "$name", size: $size);
   }

  my $init = 0;                                                                 # Initializer
  if (defined $expr)                                                            # Initialize value
   {if ($Registers{$expr})
     {$const and confess "Cannot use a register to initialize a constant";
     }
#   elsif (ref($expr)) {}                                                       # Reference a variable
    else
     {$init = $expr;
     }
   }
  else
   {$const and confess "Expression required for constant";
   }

  my $label;                                                                    # Allocate space
     $label = $size =~ m(\A0|b\Z) ? Db(0) :
              $size =~ m(\A1|w\Z) ? Dw(0) :
              $size =~ m(\A2|d\Z) ? Dd(0) :
              $size =~ m(\A3|q\Z) ? Dq(0) :
              $size =~ m(\A4|x\Z) ? Dq(0,0) :
              $size =~ m(\A5|y\Z) ? Dq(0,0,0,0) :
              $size =~ m(\A6|z\Z) ? Dq(0,0,0,0,0,0,0,0) : undef unless $const;

     $label = $size =~ m(\A0|b\Z) ? Rb($init) :
              $size =~ m(\A1|w\Z) ? Rw($init) :
              $size =~ m(\A2|d\Z) ? Rd($init) :
              $size =~ m(\A3|q\Z) ? Rq($init) :
              $size =~ m(\A4|x\Z) ? Rq(0,0) :
              $size =~ m(\A5|y\Z) ? Rq(0,0,0,0) :
              $size =~ m(\A6|z\Z) ? Rq(0,0,0,0,0,0,0,0) : undef if $const;

  my $nSize = $size =~ tr(bwdqxyz) (0123456)r;                                  # Size of variable

  if (defined $expr)                                                            # Initialize variable if an initializer was supplied
   {my $t = "[$label]";
    if ($Registers{$expr})
     {$const and confess "Cannot use a register to initialize a constant";
      Mov $t, $expr;
     }
#   elsif (ref($expr)) {}                                                       # Reference a variable
    elsif (!$const)
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
    constant  => $options{constant},                                            # Constant if true
    expr      => $expr,                                                         # Expression that initializes the variable
    label     => $label,                                                        # Address in memory
    laneSize  => undef,                                                         # Size of the lanes in this variable
    name      => $name,                                                         # Name of the variable
    purpose   => undef,                                                         # Purpose of this variable
#   reference => ref($expr) ? $expr->size : undef,                              # Reference to another variable
    reference => undef,                                                         # Reference to another variable
    saturate  => undef,                                                         # Computations should saturate rather then wrap if true
    signed    => undef,                                                         # Elements of x|y|zmm registers are signed if true
    size      => $nSize,                                                        # Size of variable
   );
 }

sub Vb(*;$%)                                                                    # Define a byte variable
 {my ($name, $expr, %options) = @_;                                             # Name of variable, initializing expression, options
  &Variable(0, @_)
 }

sub Vw(*;$%)                                                                    # Define a word variable
 {my ($name, $expr, %options) = @_;                                             # Name of variable, initializing expression, options
  &Variable(1, @_)
 }

sub Vd(*;$%)                                                                    # Define a double word variable
 {my ($name, $expr, %options) = @_;                                             # Name of variable, initializing expression, options
  &Variable(2, @_)
 }

sub Vq(*;$%)                                                                    # Define a quad variable
 {my ($name, $expr, %options) = @_;                                             # Name of variable, initializing expression, options
  &Variable(3, @_)
 }

sub Cq(*;$%)                                                                    # Define a quad constant
 {my ($name, $expr, %options) = @_;                                             # Name of variable, initializing expression, options
  &Variable(3, @_, constant=>1)
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
  @expr <= $N or confess "$N initializers required";
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
  @_ == 2 or confess;

  ref($right) =~ m(Variable) or confess "Variable required";
  my $l = $left ->address;
  my $r = $right->address;

  if ($left->size == 3 and $right->size == 3)
   {my $lr = $left ->reference;
    my $rr = $right->reference;
    Comment "Copy variable: ".$right->name.' to '.$left->name;
    PushR my @save = (r15);
    Mov r15, $r;
    if ($rr)
     {KeepFree r15;
      Mov r15, "[r15]";
     }
    if (!$lr)
     {Mov $l, r15;
     }
    else
     {Comment "Copy ".$right->name.' to '.$left->name;
      PushR my @save2 = (r14);
      Mov r14, $l;
      Mov "[r14]", r15;
      PopR @save2;
     }
    PopR @save;
    return;
   }

  confess "Need more code";
 }

sub Nasm::X86::Variable::clone($)                                               # Clone a variable to create a new variable
 {my ($var) = @_;                                                               # Variable to clone
  @_ == 1 or confess;

  my $a = $var->address;
  if ($var->size == 3)
   {Comment "Clone ".$var->name;
    my $new = Vq('Clone of '.$var->name);
    PushR my @save = (r15);
    Mov r15, $var->address;
    Mov $new->address, r15;
    PopR @save;
    $new->reference = $var->reference;
    return $new;
   }

  confess "Need more code";
 }

sub Nasm::X86::Variable::copyAddress($$)                                        # Copy a reference to a variable
 {my ($left, $right) = @_;                                                      # Left variable, right variable

  $left->reference  or confess "Left hand side must be a reference";
  $left->size == 3  or confess "Left hand side must be size 3";

  my $l = $left ->address;
  my $r = $right->address;

  if ($right->size == 3)
   {Comment "Copy parameter address";
    PushR my @save = (r15);
    if ($right->reference)                                                      # Right is a reference so we copy its value
     {Mov r15, $r;
     }
    else                                                                        # Right is not a reference so we copy its address
     {Lea r15, $r;
     }
    Mov $l, r15;                                                                # Save value of address in left
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
  $left->constant and confess "cannot assign to a constant";

  if ($left->size == 3 and !ref($right) || $right->size == 3)
   {Comment "Variable assign";
    PushR my @save = (r14, r15);
    Mov r14, $left ->address;
    if ($left->reference)                                                       # Dereference left if necessary
     {KeepFree r14;
      Mov r14, "[r14]";
     }
    if (!ref($right))                                                           # Load right constant
     {KeepFree r15;
      Mov r15, $right;
     }
    else                                                                        # Load right variable
     {Mov r15, $right->address;
      if ($right->reference)                                                    # Dereference right if necessary
       {KeepFree r15;
        Mov r15, "[r15]";
       }
     }
    &$op(r14, r15);
    if ($left->reference)                                                       # Store in reference on left if necessary
     {PushR r13;
      Mov r13, $left->address;
      Mov "[r13]", r14;
      PopR r13;
     }
    else                                                                        # Store in variable
     {Mov $left ->address, r14;
     }
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

  !ref($right) or ref($right) =~ m(Variable) or confess "Variable expected";
  my $r = ref($right) ? $right->address : $right;                               # Right can be either a variable reference or a constant

  if ($left->size == 3)
   {PushR r15;
    Mov r15, $left ->address;
    if ($left->reference)                                                       # Dereference left if necessary
     {KeepFree r15;
      Mov r15, "[r15]";
     }
    if (ref($right) and $right->reference)                                      # Dereference on right if necessary
     {PushR r14;
      Mov r14, $right ->address;
      KeepFree r14;
      Mov r14, "[r14]";
      Cmp r15, r14;
     }
    elsif (ref($right))                                                         # Variable but not a reference on the right
     {Cmp r15, $right->address;
     }
    else                                                                        # Constant on the right
     {Cmp r15, $right;
     }
    KeepFree r15;

    &$sub(sub {Mov  r15, 1;  KeepFree r15}, sub {Mov  r15, 0;  KeepFree r15});
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

#D2 Print variables                                                             # Print the values of variables or the memory addressed by them

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

sub Nasm::X86::Variable::out($;$$)                                              # Dump the value of a variable on stdout
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stdout, 0, $title1, $title2);
 }

sub Nasm::X86::Variable::errNL($;$$)                                            # Dump the value of a variable on stderr and append a new line
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stderr, 1, $title1, $title2);
 }

sub Nasm::X86::Variable::outNL($;$$)                                            # Dump the value of a variable on stdout and append a new line
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
  else
   {confess "More code needed";
   }
  $register
 }

sub Nasm::X86::Variable::getReg($$@)                                            # Load the variable from the named registers
 {my ($variable, $register, @registers) = @_;                                   # Variable, register to load, optional further registers to load from
  if ($variable->size == 3)
   {if ($variable->isRef)                                                       # Move to the location referred to by this variable
     {$Registers{$register} or confess "No such register: $register";           # Check we have been given a register
      Comment "Get variable value from register $register";
      my $r = $register eq r15 ? r14 : r15;
      PushR $r;
      Mov $r, $variable->address;
      Mov "[$r]", $register;
      PopR $r;
     }
    else                                                                        # Move to this variable
     {Mov $variable->address, $register;
     }
   }
  elsif ($variable->size == 4)                                                  # Xmm
   {Mov $variable->address, $register;
    for my $i(keys @registers)
     {Mov $variable->address(($i + 1) * RegisterSize rax), $registers[$i];
     }
   }
  else
   {confess "More code needed";
   }
 }

sub Nasm::X86::Variable::getConst($$)                                           # Load the variable from a constant in effect setting a variable to a specified value
 {my ($variable, $constant) = @_;                                               # Variable, constant to load
  if ($variable->size == 3)
   {PushR my @save = (r14, r15);
    Comment "Load constant $constant into variable: ".$variable->name;
    Mov r15, $constant;
    Lea r14, $variable->address;
    Mov "[r14]", r15;
    PopR @save;
   }
  else
   {confess "More code needed";
   }
 }

sub Nasm::X86::Variable::incDec($$)                                             # Increment or decrement a variable
 {my ($left, $op) = @_;                                                         # Left variable operator, address of operator to perform inc or dec
  $left->constant and confess "Cannot increment or decrement a constant";
  my $l = $left->address;
  if ($left->size == 3)
   {if ($left->reference)
     {PushR my @save = (r14, r15);
      Mov r15, $l;
      KeepFree r15;
      Mov r14, "[r15]";
      &$op(r14);
      Mov "[r15]", r14;
      PopR @save;
      return $left;
     }
    else
     {PushR r15;
      Mov r15, $l;
      &$op(r15);
      Mov $l, r15;
      PopR r15;
      return $left;
     }
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
    ref($length) or confess "Not a variable";
    $length->setReg(r13);
    Add  r14, r13;
   }
  else                                                                          # Starting at zero
   {confess "Deprecated: use setMaskFirst instead";
     $length->setReg(r13);
    Mov r14, $length;
   }
  Bzhi r15, r15, r14;
  Kmovq $mask, r15;
  PopR @save;
 }

sub Nasm::X86::Variable::setMaskFirst($$)                                       # Set the first bits in the specified mask register
 {my ($length, $mask) = @_;                                                     # Variable containing length to set, mask register
  @_ == 2 or confess;

  PushR my @save = (r14, r15);
  Mov r15, -1;
  $length->setReg(r14);
  Bzhi r15, r15, r14;
  Kmovq $mask, r15;
  PopR @save;
 }

sub Nasm::X86::Variable::setMaskBit($$)                                         # Set a bit in the specified mask register retaining the other bits
 {my ($length, $mask) = @_;                                                     # Variable containing bit position to set, mask register
  @_ == 2 or confess;

  PushR my @save = (r14, r15);
  Kmovq r15, $mask;
  $length->setReg(r14);
  Bts r15, r14;
  Kmovq $mask, r15;
  PopR @save;
 }

sub Nasm::X86::Variable::clearMaskBit($$)                                       # Clear a bit in the specified mask register retaining the other bits
 {my ($length, $mask) = @_;                                                     # Variable containing bit position to clear, mask register
  @_ == 2 or confess;

  PushR my @save = (r14, r15);
  Kmovq r15, $mask;
  $length->setReg(r14);
  Btc r15, r14;
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

sub Nasm::X86::Variable::saveZmm2222($$)                                        # Save bytes into the memory addressed by the target variable from the numbered zmm register.
 {my ($target, $zmm) = @_;                                                      # Variable containing the address of the source, number of zmm to put
  @_ == 2 or confess;
  Comment "Save zmm$zmm into memory addressed by ".$target->name;
  PushR r15;
  $target->setReg(r15);
  Vmovdqu8 "[r15]", "zmm$zmm";                                                  # Write into memory
  PopR r15;
 }

sub getBwdqFromMm($$$)                                                          # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 {my ($size, $mm, $offset) = @_;                                                # Size of get, register, offset in bytes either as a constant or as a variable
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
  PushRR $mm;    ##Rewrite using masked move rather than stack                  # Push source register

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

sub getBFromXmm($$)                                                             # Get the byte from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('b', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getWFromXmm($$)                                                             # Get the word from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('w', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getDFromXmm($$)                                                             # Get the double word from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('d', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getQFromXmm($$)                                                             # Get the quad word from the numbered xmm register and return it in a variable
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('q', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub getBFromZmm($$)                                                             # Get the byte from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('b', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getWFromZmm($$)                                                             # Get the word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('w', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getDFromZmm($$)                                                             # Get the double word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('d', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub getQFromZmm($$)                                                             # Get the quad word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('q', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub Nasm::X86::Variable::getBFromZmm($$$)                                       # Get the byte from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMm('b', "zmm$zmm", $offset))                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::getWFromZmm($$$)                                       # Get the word from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMm('w', "zmm$zmm", $offset))                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::getDFromZmm($$$)                                       # Get the double word from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMm('d', "zmm$zmm", $offset))                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::getQFromZmm($$$)                                       # Get the quad word from the numbered zmm register and put it in a variable
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  $variable->copy(getBwdqFromMm('q', "zmm$zmm", $offset))                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
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

  PushR my @save=(r15, $mm);   # Rewrite using masked move                      # Push target register
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

#D2 Broadcast                                                                   # Broadcast from a variable into a zmm

sub Nasm::X86::Variable::zBroadCastD($$)                                        # Broadcast a double word in a variable into the numbered zmm.
 {my ($variable, $zmm) = @_;                                                    # Variable containing value to broadcast, numbered zmm to broadcast to
  PushR my @save = (r15);
  $variable->setReg(r15);                                                       # Value of variable
  Vpbroadcastd "zmm".$zmm, r15d;                                                # Broadcast
  PopR @save;
 }

#D2 Stack                                                                       # Push and pop variables to and from the stack

sub Nasm::X86::Variable::push($)                                                # Push a variable onto the stack
 {my ($variable) = @_;                                                          # Variable
  $variable->size == 3 or confess "Wrong size";
  PushR rax; Push rax;                                                          # Make a slot on the stack and save rax
  $variable->setReg(rax);                                                       # Variable to rax
  my $s = RegisterSize rax;                                                     # Size of rax
  Mov "[rsp+$s]", rax;                                                          # Move variable to slot
  PopR rax;                                                                     # Remove rax to leave variable on top of the stack
 }

sub Nasm::X86::Variable::pop($)                                                 # Pop a variable from the stack
 {my ($variable) = @_;                                                          # Variable
  $variable->size == 3 or confess "Wrong size";
  PushR rax;                                                                    # Liberate a register
  my $s = RegisterSize rax;                                                     # Size of rax
  Mov rax, "[rsp+$s]";                                                          # Load from stack
  $variable->getReg(rax);                                                       # Variable to rax
  PopR rax;                                                                     # Remove rax to leave variable on top of the stack
  Add rsp, $s;                                                                  # Remove variable from stack
 }

#D2 Memory                                                                      # Actions on memory described by variables

sub Nasm::X86::Variable::clearMemory($$)                                        # Clear the memory described in this variable
 {my ($address, $size) = @_;                                                    # Address of memory to clear, size of the memory to clear
  $address->name eq q(address) or confess "Need address";
  $size->name eq q(size) or confess "Need size";
  &ClearMemory(size=>$size, address=>$address);                                 # Free the memory
 }

sub Nasm::X86::Variable::copyMemory($$$)                                        # Copy from one block of memory to another
 {my ($target, $source, $size) = @_;                                            # Address of target, address of source, length to copy
  $target->name eq q(target) or confess "Need target";
  $source->name eq q(source) or confess "Need source";
  $size  ->name eq q(size)   or confess "Need size";
  &CopyMemory(target => $target, source => $source, size => $size);             # Copy the memory
 }

sub Nasm::X86::Variable::printMemoryInHexNL($$$)                                # Write the memory addressed by a variable to stdout or stderr
 {my ($address, $channel, $size) = @_;                                          # Address of memory, channel to print on, number of bytes to print
  $address->name eq q(address) or confess "Need address";
  $size   ->name eq q(size)    or confess "Need size";
  PushR my @save = (rax, rdi);
  $address->setReg(rax);
  $size->setReg(rdi);
  &PrintMemoryInHex($channel);
  &PrintNL($channel);
  PopR @save;
 }

sub Nasm::X86::Variable::printErrMemoryInHexNL($$)                              # Write the memory addressed by a variable to stderr
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  $address->printMemoryInHexNL($stderr, $size);
 }

sub Nasm::X86::Variable::printOutMemoryInHexNL($$)                              # Write the memory addressed by a variable to stdout
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  $address->printMemoryInHexNL($stdout, $size);
 }

sub Nasm::X86::Variable::freeMemory($$)                                         # Free the memory addressed by this variable for the specified length
 {my ($address, $size) = @_;                                                    # Address of memory to free, size of the memory to free
  $address->name eq q(address) or confess "Need address";
  $size   ->name eq q(size)    or confess "Need size";
  &FreeMemory(size=>$size, address=>$address);                                  # Free the memory
 }

sub Nasm::X86::Variable::allocateMemory(@)                                      # Allocate the specified amount of memory via mmap and return its address
 {my ($size) = @_;                                                              # Size
  @_ >= 1 or confess;
  $size->name eq q(size) or confess "Need size";
  &AllocateMemory(size => $size, my $a = Vq(address));
  $a
 }

#D2 Structured Programming with variables                                       # Structured programming operations driven off variables.

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

#D1 Stack                                                                       # Manage data on the stack

#D2 Push, Pop, Peek                                                             # Generic versions of push, pop, peek

sub PushRR(@)                                                                   #P Push registers onto the stack without tracking
 {my (@r) = @_;                                                                 # Register
  for my $r(@r)
   {my $size = RegisterSize $r;
    $size or confess "No such register: $r";
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

sub PopEax()                                                                    # We cannot pop a double word from the stack in 64 bit long mode using pop so we improvise
 {my $l = RegisterSize eax;                                                     # eax is half rax
  Mov eax, "[rsp]";
  Add rsp, RegisterSize eax;
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
    structure  => $structure,                                                   # Structure containing the field
    loc        => $structure->size,                                             # Offset of the field
    size       => $length,                                                      # Size of the field
    comment    => $comment                                                      # Comment describing the purpose of the field
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

#D1 Operating system                                                            # Interacting with the operating system.

#D2 Processes                                                                   # Create and manage processes

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

#D2 Memory                                                                      # Allocate and print memory

sub PrintMemoryInHex($)                                                         # Dump memory from the address in rax for the length in rdi on the specified channel. As this method prints in blocks of 8 up to 7 bytes will be missing from the end unless the length is a multiple of 8 .
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess;
  Comment "Print out memory in hex on channel: $channel";

  Call Macro
   {my $size = RegisterSize rax;
    SaveFirstFour;
    Mov rsi, rax;                                                               # Position in memory
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
    Cmp rax, -12;                                                               # Check return code
    IfEq(sub
     {PrintErrString "Cannot allocate memory, ";
      $$p{size}->errNL;
      Exit(1);
     });
    $$p{address}->getReg(rax);                                                  # Amount of memory

    RestoreFirstSeven;
   } in => {size => 3}, out => {address => 3};

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
   } in => {size => 3, address => 3};

  $s->call(@variables);
 }

sub ClearMemory(@)                                                              # Clear memory - the address of the memory is in rax, the length in rdi
 {my (@variables) = @_;                                                         # Variables
  @_ >= 2 or confess;
  Comment "Clear memory";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR my @save = (k7, zmm0, rax, rdi, rsi, rdx);
    $$p{address}->setReg(rax);
    $$p{size}   ->setReg(rdi);
    Lea rdx, "[rax+rdi]";                                                       # Address of upper limit of buffer

    ClearRegisters zmm0;                                                        # Clear the register that will be written into memory

    Mov rsi, rdi;                                                               # Modulus the size of zmm
    And rsi, 0x3f;
    Test rsi, rsi;
    IfNz sub                                                                    # Need to align so that the rest of the clear can be done in full zmm blocks
     {Vq(align, rsi)->setMaskFirst(k7);                                         # Set mask bits
      Vmovdqu8 "[rax]{k7}", zmm0;                                               # Masked move to memory
      Add rax, rsi;                                                             # Update point to clear from
      Sub rdi, rsi;                                                             # Reduce clear length
     };

    For                                                                         # Clear remaining memory in full zmm blocks
     {Vmovdqu64 "[rax]", zmm0;
     } rax, rdx, RegisterSize zmm0;

    PopR @save;
   } in => {size => 3, address => 3};

  $s->call(@variables);
 }

sub MaskMemory(@)                                                               # Write the specified byte into locations in the target mask that correspond to the locations in the source that contain the specified byte.
 {my (@variables) = @_;                                                         # Variables
  @_ >= 2 or confess;
  Comment "Clear memory";

  my $size = RegisterSize zmm0;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR my @save = (k6, k7, rax, rdi, rsi, rdx, r8, r9, r10, zmm0, zmm1, zmm2);
    $$p{source}->setReg(rax);
    $$p{mask}  ->setReg(rdx);
    $$p{match} ->setReg(rsi);
    $$p{set}   ->setReg(rdi);
    $$p{size}  ->setReg(r8);
    Lea r9, "[rax+r8]";                                                         # Address of upper limit of source

    Vpbroadcastb zmm1, rsi;                                                     # Character to match
    Vpbroadcastb zmm2, rdi;                                                     # Character to write into mask

    Mov r10, r8;                                                                # Modulus the size of zmm
    And r10, 0x3f;
    Test r10, r10;
    IfNz sub                                                                    # Need to align so that the rest of the clear can be done in full zmm blocks
     {Vq(align, r10)->setMaskFirst(k7);                                         # Set mask bits
      Vmovdqu8 "zmm0\{k7}", "[rax]";                                            # Load first incomplete block of source
      Vpcmpub  "k6{k7}", zmm0, zmm1, 0;                                         # Characters in source that match
      Vmovdqu8 "[rdx]{k6}", zmm2;                                               # Write set byte into mask at match points
      Add rax, r10;                                                             # Update point to mask from
      Add rdx, r10;                                                             # Update point to mask to
      Sub  r8, r10;                                                             # Reduce mask length
     };

    For                                                                         # Clear remaining memory in full zmm blocks
     {Vmovdqu8 zmm0, "[rax]";                                                   # Load complete block of source
      Vpcmpub  "k7", zmm0, zmm1, 0;                                             # Characters in source that match
      Vmovdqu8 "[rdx]{k7}", zmm2;                                               # Write set byte into mask at match points
      Add rdx, $size;                                                           # Update point to mask to
     } rax, r9, $size;

    PopR @save;
   } in => {size => 3, source => 3, mask => 3, match => 3, set => 3};           # Match is the character to match on in the source, set is the character to write into the mask at the corresponding position.

  $s->call(@variables);
 }

sub MaskMemoryInRange4(@)                                                       # Write the specified byte into locations in the target mask that correspond to the locations in the source that contain 4 bytes in the specified range.
 {my (@variables) = @_;                                                         # Variables
  @_ >= 6 or confess;
  Comment "Clear memory";

  my $size = RegisterSize zmm0;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR my @save = (k4, k5, k6, k7, zmm(0..9), map{"r$_"} qw(ax di si dx), 8..15);
    $$p{source}->setReg(rax);
    $$p{mask}  ->setReg(rdx);
    $$p{low}   ->setReg(r10);
    $$p{high}  ->setReg(r11);
    $$p{set}   ->setReg(rdi);
    $$p{size}  ->setReg(rsi);

    Vpbroadcastb zmm1, rdi;                                                     # Character to write into mask
                Vpbroadcastb zmm2, r10;                                         # Character 1 low
    Shr r10, 8; Vpbroadcastb zmm3, r10;                                         # Character 2 low
    Shr r10, 8; Vpbroadcastb zmm4, r10;                                         # Character 3 low
    Shr r10, 8; Vpbroadcastb zmm5, r10;                                         # Character 4 low
                Vpbroadcastb zmm6, r11;                                         # Character 1 high
    Shr r11, 8; Vpbroadcastb zmm7, r11;                                         # Character 2 high
    Shr r11, 8; Vpbroadcastb zmm8, r11;                                         # Character 3 high
    Shr r11, 8; Vpbroadcastb zmm9, r11;                                         # Character 4 high
    KeepFree r10, r11;
    Lea r8, "[rax+rsi]";                                                        # Address of upper limit of source
PrintErrRegisterInHex zmm 2..9;

    my sub check($$)                                                            # Check a character
     {my ($z, $f) = @_;                                                         # First zmm, finished label
      my $Z = $z + 4;
PrintErrRegisterInHex zmm($z, $Z), k7;
      Vpcmpub  "k6{k7}", zmm0, "zmm$z", 5;                                      # Greater than or equal
      Vpcmpub  "k7{k6}", zmm0, "zmm$Z", 2;                                      # Less than or equal
PrintErrRegisterInHex k6, k7;
      Ktestq k7, k7;
      Jz $f;                                                                    # No match
      Kshiftlq k7, k7, 1;                                                       # Match - move up to next character
     };

    my sub last4()                                                              # Expand each set bit four times
     {Kshiftlq k6, k7, 1;  Kandq k7, k6, k7;                                    # We have found a character in the specified range
      Kshiftlq k6, k7, 2;  Kandq k7, k6, k7;                                    # Last four
     };

PrintErrStringNL "AAAA";
PrintErrRegisterInHex rsi;
    For                                                                         # Mask remaining memory in full zmm blocks
     {my $finished = Label;                                                     # Point where we have finished the initial comparisons
      Vmovdqu8 zmm0, "[rax]";                                                   # Load complete block of source
      Kxnorq k7, k7, k7;                                                        # Complete block - sets register to all ones
PrintErrStringNL "BBBB";
PrintErrRegisterInHex k7, zmm0;
      check($_, $finished) for 2..5;  last4;                                    # Check a range

PrintErrStringNL "CCCC";
PrintErrRegisterInHex k7, zmm1;
      Vmovdqu8 "[rdx]{k7}", zmm1;                                               # Write set byte into mask at match points
      Add rdx, $size;                                                           # Update point to mask to
      SetLabel $finished;
     } rax, r8, $size;


    Mov r10, rsi; And r10, 0x3f;                                                # Modulus the size of zmm
    Test r10, r10;
PrintErrStringNL "DDDD";
    IfNz sub                                                                    # Need to align so that the rest of the mask can be done in full zmm blocks
     {my $finished = Label;                                                     # Point where we have finished the initial comparisons
      Vq(align, r10)->setMaskFirst(k7);                                         # Set mask bits
      Vmovdqu8 "zmm0\{k7}", "[rax]";                                            # Load first incomplete block of source
PrintErrStringNL "EEEE";
PrintErrRegisterInHex k7, r10, zmm0;
      check($_, $finished) for 2..5;  last4;                                    # Check a range
      Vmovdqu8 "[rdx]{k7}", zmm1;                                               # Write set byte into mask at match points
      Add rax, r10;                                                             # Update point to mask from
      Add rdx, r10;                                                             # Update point to mask to
      Sub  r8, r10;                                                             # Reduce mask length
      SetLabel $finished;
     };

    PopR @save;
   } in => {size => 3, source => 3, mask => 3, set => 3, low => 3, high => 3};

  $s->call(@variables);
 } # MaskMemoryInRange4

sub CopyMemory(@)                                                               # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
 {my (@variables) = @_;                                                         # Variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Copy memory";
    SaveFirstSeven;
    $$p{source}->setReg(rsi);
    $$p{target}->setReg(rax);
    $$p{size}  ->setReg(rdi);
    ClearRegisters rdx;
    For                                                                         # Clear memory
     {Mov "r8b", "[rsi+rdx]";
      Mov "[rax+rdx]", "r8b";
     } rdx, rdi, 1;
    RestoreFirstSeven;
   } in => {source => 3, target => 3, size => 3};

  $s->call(@variables);
 }

#D2 Files                                                                       # Interact with the operating system via files.

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

#D1 Unicode                                                                     # Convert utf8 to utf32

sub GetNextUtf8CharAsUtf32(@)                                                   # Get the next utf8 encoded character from the addressed memory and return it as a utf32 char
 {my (@parameters) = @_;                                                        # Parameters
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Get next Utf8 char";

    PushR my @save = (r11, r12, r13, r14, r15);
    $$p{fail}->getConst(0);                                                     # Clear failure indicator
    $$p{in}->setReg(r15);                                                       # Character to convert
    ClearRegisters r14;                                                         # Move to byte register below does not clear the entire register
    KeepFree r14;
    Mov r14b, "[r15]";
    my $success = Label;                                                        # https://en.wikipedia.org/wiki/UTF-8

    KeepFree r15;
    Cmp r14, 0x7f;                                                              # Ascii
    IfLe
     {$$p{out}->getReg(r14);
      $$p{size}->copy(Cq(one, 1));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    Cmp r14, 0xdf;                                                              # 2 bytes
    IfLe
     {Mov r13b, "[r15+1]";
      And r13, 0x3f;
      And r14, 0x1f;
      Shl r14, 6;
      Or  r14,  r13;
      $$p{out}->getReg(r14);
      $$p{size}->copy(Cq(two, 2));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    Cmp r14, 0xef;                                                              # 3 bytes
    IfLe
     {Mov r12b, "[r15+2]";
      And r12, 0x3f;
      Mov r13b, "[r15+1]";
      And r13, 0x3f;
      And r14, 0x0f;
      Shl r13,  6;
      Shl r14, 12;
      Or  r14,  r13;
      Or  r14,  r12;
      $$p{out}->getReg(r14);
      $$p{size}->copy(Cq(three, 3));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    Cmp r14, 0xf7;                                                              # 4 bytes
    IfLe
     {Mov r11b, "[r15+3]";
      And r11, 0x3f;
      Mov r12b, "[r15+2]";
      And r12, 0x3f;
      Mov r13b, "[r15+1]";
      And r13, 0x3f;
      And r14, 0x07;
      Shl r12,  6;
      Shl r13, 12;
      Shl r14, 18;
      Or  r14,  r13;
      Or  r14,  r12;
      Or  r14,  r11;
      $$p{out}->getReg(r14);
      $$p{size}->copy(Cq(four, 4));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    $$p{fail}->getConst(1);                                                     # Conversion failed

    SetLabel $success;

    PopR @save;
   } in => {in => 3}, out => {out => 3, size => 3, fail => 3};

  $s->call(@parameters);
 } # GetNextUtf8CharAsUtf32

sub ConvertUtf8ToUtf32(@)                                                       # Convert a string of utf8 to an allocated block of utf32 and return its address and length.
 {my (@parameters) = @_;                                                        # Parameters
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Convert utf8 to utf32";

    PushR my @save = (r10, r11, r12, r13, r14, r15);

    my $size = $$p{size8} * 4;                                                  # Estimated length for utf32
    AllocateMemory size => $size, my $address = Vq(address);

     $$p{u8}            ->setReg(r14);                                          # Current position in input string
    ($$p{u8}+$$p{size8})->setReg(r15);                                          # Upper limit of input string
    $address->setReg(r13);                                                      # Current position in output string
    ClearRegisters r12;                                                         # Number of characters in output string

    ForEver sub                                                                 # Loop through input string  converting each utf8 sequence to utf32
     {my ($start, $end) = @_;
      my @p = my ($out, $size, $fail) = (Vq(out), Vq(size), Vq('fail'));
      GetNextUtf8CharAsUtf32 Vq(in, r14), @p;                                   # Get next utf 8 character and convert it to utf32
      If ($fail, sub
       {PrintErrStringNL "Invalid utf8 character at index:";
        PrintErrRegisterInHex r12;
        Exit(1);
       });

      Inc r12;                                                                  # Count characters converted
      $out->setReg(r11);                                                        # Output character

      Mov  "[r13]",  r11d;
      Add    r13,    RegisterSize eax;                                          # Move up 32 bits output string
      $size->setReg(r10);                                                       # Decoded this many bytes
      Add   r14, r10;                                                           # Move up in input string
      Cmp   r14, r15;
      IfGe {Jmp $end};                                                          # Exhausted input string
    };

    $$p{u32}   ->copy($address);                                                # Address of allocation
    $$p{size32}->copy($size);                                                   # Size of allocation
    $$p{count} ->getReg(r12);                                                   # Number of unicode points converted from utf8 to utf32
    PopR @save;
   } in => {u8 => 3, size8 => 3}, out => {u32 => 3, size32 => 3, count => 3};

  $s->call(@parameters);
 } # ConvertUtf8ToUtf32

sub ClassifyCharacters4(@)                                                      # Classify the utf32 characters in a block of memory of specified length using the classification held in zmm0: zmm0 should be  formatted in double words with each word having the classification in the highest 8 bits and the utf32 character so classified in the lower 21 bits.  The classification bits are copied into the hign unused) byte of each utf32 character in the block of memory.
 {my (@parameters) = @_;                                                        # Parameters
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Classify characters in utf32 format";
    my $finish = Label;

    PushR my @save =  (r14, r15, k6, k7, zmm 29..31);

    Mov r15, 0x88888888;                                                        # Create a mask for the classification bytes
    Kmovq k7, r15;
    KeepFree r15;
    Kshiftlq k6, k7, 32;                                                        # Move mask into upper half of register
    Korq  k7, k6, k7;                                                           # Classification bytes masked by k7

    Knotq k7, k7;                                                               # Utf32 characters mask
    Vmovdqu8   "zmm31\{k7}{z}", zmm0;                                           # utf32 characters to match

    $$p{address}->setReg(r15);                                                  # Address of first utf32 character
    $$p{size}->for(sub                                                          # Process each utf32 character in the block of memory
     {my ($index, $start, $next, $end) = @_;

      Mov r14d, "[r15]";                                                        # Load utf32 character
      Add r15, RegisterSize r14d;                                               # Move up to next utf32 character
      Vpbroadcastd zmm30, r14d;                                                 # 16 copies of the utf32  character to be processed
      Vpcmpud  k7, zmm30, zmm31, 0;                                             # Look for one matching character
      Ktestw k7, k7;                                                            # Was there a match
      IfZ {Jmp $next};                                                          # No character was matched
      Vpcompressd "zmm30\{k7}", zmm0;                                           # Place classification byte at start of xmm
      Vpextrb "[r15-1]", xmm30, 3;                                              # Extract classification character
     });

    SetLabel $finish;
    PopR @save;
   } in => {address => 3, size => 3};

  $s->call(@parameters);
 } # ClassifyCharacters4

sub ClassifyRange($@)                                                           #P Implementation of ClassifyInRange and ClassifyWithinRange
 {my ($recordOffsetInRange, @parameters) = @_;   # Record offset in classification in high byte if true, record offset in range in low byte if true, parameters
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Classify characters in utf32 format";
    my $finish = Label;

    PushR my @save =  (($recordOffsetInRange ? (r12, r13) : ()),                # More registers required if we are recording position in range
                       r14, r15, k6, k7, zmm 29..31);

    Mov r15, 0x88888888;                                                        # Create a mask for the classification bytes
    Kmovq k7, r15;
    KeepFree r15;
    Kshiftlq k6, k7, 32;                                                        # Move mask into upper half of register
    Korq  k7, k6, k7;                                                           # Classification bytes masked by k7

    Knotq k7, k7;                                                               # Utf32 characters mask
    Vmovdqu8 "zmm31\{k7}{z}", zmm1;                                             # utf32 characters at upper end of each range
    Vmovdqu8 "zmm30\{k7}{z}", zmm0;                                             # utf32 characters at lower end of each range

    $$p{address}->setReg(r15);                                                  # Address of first utf32 character
    $$p{size}->for(sub                                                          # Process each utf32 character in the block of memory
     {my ($index, $start, $next, $end) = @_;

      Mov r14d, "[r15]";                                                        # Load utf32 character
      Add r15, RegisterSize r14d;                                               # Move up to next utf32 character
      Vpbroadcastd       zmm29, r14d;                                           # 16 copies of the utf32  character to be processed
      Vpcmpud  k7,       zmm29, zmm30, 5;                                       # Look for start of range
      Vpcmpud "k6\{k7}", zmm29, zmm31, 2;                                       # Look for end of range
      Ktestw k6, k6;                                                            # Was there a match ?
      IfZ {Jmp $next};                                                          # No character was matched
                                                                                # Process matched character
      if ($recordOffsetInRange == 1)                                            # Record offset in classification range in high byte as used for bracket matching
       {Vpcompressd "zmm29\{k6}", zmm0;                                         # Place classification byte at start of xmm29
        Vpextrd r13d, xmm29, 4;                                                 # Extract start of range
        Mov r12, r13;                                                           # Copy start of range
        Shr r12, 24;                                                            # Classification start
        And r13, 0x00ffffff;                                                    # Range start
        Sub r14, r13;                                                           # Offset in range
        Add r12, r14;                                                           # Offset in classification
        Mov "[r15-1]", r12b;                                                    # Save classification
       }
      elsif ($recordOffsetInRange == 2)                                         # Record classification in high byte and offset in classification range in low byte as used for alphabets
       {Vpcompressd "zmm29\{k6}", zmm0;                                         # Place classification byte and start of range at start of xmm29
        Vpextrd r13d, xmm29, 4;                                                 # Extract start of range specification
        Mov r12, r13;                                                           # Range classification code and start of range
        Shr r12, 24;                                                            # Range classification code
        Mov "[r15-1]", r12b;                                                    # Save classification
        And r13, 0x00ffffff;                                                    # Range start

        Vpcompressd "zmm29\{k6}", zmm1;                                         # Place start of alphabet at start of xmm29
        Vpextrd r12d, xmm29, 4;                                                 # Extract offset of alphabet in range
        Shr r12, 24;                                                            # Alphabet offset
        Add r12, r14;                                                           # Range start plus utf32
        Sub r12, r13;                                                           # Offset of utf32 in alphabet range
        Mov "[r15-4]", r12b;                                                    # Save offset of utf32 in alphabet range
        KeepFree r12;
        ClearRegisters r12;                                                     # Zero r12
        Mov "[r15-3]", r12w;                                                    # Clear middle of utf32
       }
      else                                                                      # Record classification in high byte
       {Vpcompressd "zmm29\{k6}", zmm0;                                         # Place classification byte at start of xmm29
        Vpextrb "[r15-1]", xmm29, 3;                                            # Extract and save classification
       }
     });

    SetLabel $finish;
    PopR @save;
   } name => "ClassifyRange_$recordOffsetInRange",
     in   => {address => 3, size => 3};

  $s->call(@parameters);
 } # ClassifyRange

sub ClassifyInRange(@)                                                          # Character classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with each word in zmm1 having the classification in the highest 8 bits and with zmm0 and zmm1 having the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.  The classification bits from the first matching range are copied into the high (unused) byte of each utf32 character in the block of memory.
 {my (@parameters) = @_;                                                        # Parameters
  ClassifyRange(0, @_);
 }

sub ClassifyWithInRange(@)                                                      # Bracket classification: Classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification range in the highest 8 bits of zmm0 and zmm1 and the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.  The classification bits from the position within the first matching range are copied into the high (unused) byte of each utf32 character in the block of memory.
 {my (@parameters) = @_;                                                        # Parameters
  ClassifyRange(1, @_);
 }

sub ClassifyWithInRangeAndSaveOffset(@)                                         # Alphabetic classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification code in the high byte of zmm1 and the offset of the first element in the range in the high byte of zmm0.  The lowest 21 bits of each double word in zmm0 and zmm1  contain the utf32 characters marking the start and end of each range. The classification bits from zmm1 for the first matching range are copied into the high byte of each utf32 character in the block of memory.  The offset in the range is copied into the lowest byte of each utf32 character in the bloxk of memory.  The middle two bytes are cleared.  The nett effect is to reduce 21 bits of utf32 to 16 bits of Nida.
 {my (@parameters) = @_;                                                        # Parameters
  ClassifyRange(2, @_);
 }

sub MatchBrackets(@)                                                            # Replace the low three bytes of a utf32 bracket character with 24 bits of offset to the matching opening or closing bracket. Opening brackets have even codes from 0x10 to 0x4e while the corresponding closing bracket has a code one higher.
 {my (@parameters) = @_;                                                        # Parameters
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Match brackets in utf 32 text";
    my $finish = Label;
    PushR my @save = (xmm0, k7, r10, r11, r12, r13, r14, r15, rbp);             # r15 current character address. r14 is the current classification. r13 the last classification code. r12 the stack depth. r11 the number of opening brackets found. r10  address of first utf32 character.
    Mov rbp, rsp;                                                               # Save stack location so we can use the stack to record the brackets we have found
    ClearRegisters r11, r12, r15;                                               # Count the number of brackets and track the stack depth, index of each character
    Cq(three, 3)->setMaskFirst(k7);                                             # These are the number of bytes that we are going to use for the offsets of brackets which limits the size of a program to 24 million utf32 characters
    $$p{fail}   ->getConst(0);                                                  # Clear failure indicator
    $$p{opens}  ->getConst(0);                                                  # Clear count of opens
    $$p{address}->setReg(r10);                                                  # Address of first utf32 character
    my $w = RegisterSize eax;                                                   # Size of a utf32 character

    $$p{size}->for(sub                                                          # Process each utf32 character in the block of memory
     {my ($index, $start, $next, $end) = @_;
      my $continue = Label;

      Mov r14b, "[r10+$w*r15+3]";                                               # Classification character

      Cmp r14, 0x10;                                                            # First bracket
      IfLt sub {Jmp $continue};                                                 # Less than first bracket
      Cmp r14, 0x4f;                                                            # Last bracket
      IfGt sub {Jmp $continue};                                                 # Greater than last bracket

      Test r14, 1;                                                              # Zero means that the bracket is an opener
      IfZ sub                                                                   # Save an opener then continue
       {Push r15;                                                               # Save position in input
        Push r14;                                                               # Save opening code
        Inc r11;                                                                # Count number of opening brackets
        Inc r12;                                                                # Number of brackets currently open
        Jmp $continue;
       };
      Cmp r12, 1;                                                               # Check that there is a bracket to match on the stack
      IfLt sub                                                                  # Nothing on stack
       {Not r15;                                                                # Minus the offset at which the error occurred so that we can fail at zero
        $$p{fail}->getReg(r15);                                                 # Position in input that caused the failure
        Jmp $finish;                                                            # Return
       };
      Mov r13, "[rsp]";                                                         # Peek at the opening bracket code which is on top of the stack
      Inc r13;                                                                  # Expected closing bracket
      Cmp r13, r14;                                                             # Check for match
      IfNe sub                                                                  # Mismatch
       {Not r15;                                                                # Minus the offset at which the error occurred so that we can fail at zero
        $$p{fail}->getReg(r15);                                                 # Position in input that caused the failure
        Jmp $finish;                                                            # Return
       };
      Pop r13;                                                                  # The closing bracket matches the opening bracket
      Pop r13;                                                                  # Offset of opener
      Dec r12;                                                                  # Close off bracket sequence
      Vpbroadcastq xmm0, r15;                                                   # Load offset of opener
      Vmovdqu8 "[r10+$w*r13]\{k7}", xmm0;                                       # Save offset of opener in the code for the closer - the classification is left intact so we still know what kind of bracket we have
      Vpbroadcastq xmm0, r13;                                                   # Load offset of opener
      Vmovdqu8 "[r10+$w*r15]\{k7}", xmm0;                                       # Save offset of closer in the code for the openercloser - the classification is left intact so we still know what kind of bracket we have
      SetLabel $continue;                                                       # Continue with next character
      Inc r15;                                                                  # Next character
     });

    SetLabel $finish;
    Mov rsp, rbp;                                                               # Restore stack
    $$p{opens}->getReg(r11);                                                    # Number of brackets opened
    PopR @save;
   } in  => {address => 3, size => 3}, out => {fail => 3, opens => 3};

  $s->call(@parameters);
 } # MatchBrackets

sub PrintUtf32($$)                                                              # Print the specified number of utf32 characters at the specified address
 {my ($n, $m) = @_;                                                             # Variable: number of characters to print, variable: address of memory
  PushR my @save = (rax, r14, r15);
  my $count = $n / 2; my $count1 = $count - 1;
  $count->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $a = $m + $index * 8;
    $a->setReg(rax);
    KeepFree rax;
    Mov rax, "[rax]";
    KeepFree rax;
    Mov r14, rax;
    Mov r15, rax;
    Shl r15, 32;
    Shr r14, 32;
    Or r14,r15;
    Mov rax, r14;
    PrintOutRaxInHex;
    If ($index % 8 == 7, sub                                                    #
     {PrintOutNL;                                                               #
     },
    sub
    {If($index != $count1, sub
      {PrintOutString "  ";
      });
    });
   });
  PrintOutNL;
  PopR @save;
 }

#D1 Nida Parsing                                                                # Parse Nida language statements

sub NidaLexType($)                                                              # Convert a classified utf32 character in the specified register into a lexical item in 3:0 bits representing the lexical item.
 {my ($r) = @_;                                                                 # Register to convert
  Shr $r, 24;                                                                   # Move classification byte into position
  And $r, 0xff;                                                                 # Classification byte
  Cmp $r, 0x10;
  IfGe {And $r, 1};                                                             # Brackets
 }

sub Nida_test_b(&$)                                                             #P Check that we have an opening bracket
 {my ($sub, $item) = @_;                                                        # Sub defining action to be taken on a match, register to check,
  Cmp $item, 0x0;
  IfEq {};
 }


sub Nida_test_B($)                                                              #P Check that we have a closing bracket
 {my ($item) = @_;                                                              # Register to check
  Cmp $item, 0x1;
 }


=pod
sub parse(@)                                                                    # Parse an expression.
 {my (@expression) = @_;                                                        # Expression to parse

  my @s;                                                                        # Stack

  my sub test($$)                                                               # Check the type of an item in the stack
   {my ($item, $type) = @_;                                                     # Item to test, expected type of item
    index($type, ref($item) ? 't' : substr $item, 0, 1) > -1                    # Term
   }

  my sub reduce()                                                               # Convert the longest possible expression on top of the stack into a term
   {#lll "TTTT ", scalar(@s), "\n", dump([@s]);

    if (@s >= 3)                                                                # Go for term infix-operator term
     {my ($r, $d, $l) = reverse @s;
      if (test($l, 't') and test($r, 't') and test($d, 'ads'))                  # Parse out infix operator expression
       {pop  @s for 1..3;
        push @s, new $d, $l, $r;
        return 1;
       }
      if (test($l, 'b') and test($r, 'B') and test($d, 't'))                    # Parse parenthesized term
       {pop  @s for 1..3;
        push @s, $d;
        return 1;
       }
     }

    if (@s >= 2)                                                                # Convert an empty pair of parentheses to an empty term
     {my ($r, $l) = reverse @s;
      if (test($l, 'b')  and test($r, 'B'))                                     # Empty pair of parentheses
       {pop  @s for 1..2;
        push @s, new 'empty1';
        return 1;
       }
      if (test($l,'s') and test($r, 'B'))                                       # Semi-colon, close implies remove unneeded semi
       {pop  @s for 1..2;
        push @s, $r;
        return 1;
       }
      if (test($l,'p') and test($r, 't'))                                       # Prefix, term
       {pop  @s for 1..2;
        push @s, new $l, $r;
        return 1;
       }
     }

    undef                                                                       # No move made
   };

  for my $i(keys @expression)                                                   # Each input element
   {my $e = $expression[$i];

    if (!@s)                                                                    # Empty stack
     {my $E = expandElement $e;
      die <<END =~ s(\n) ( )gsr =~ s(\s+\Z) (\n)gsr if !test($e, 'bpsv');
Expression must start with 'opening parenthesis', 'prefix
operator', 'semi-colon' or 'variable', not $E.
END
      if    (test($e, 'v'))                                                     # Single variable
       {@s = (new $e);
       }
      elsif (test($e, 's'))                                                     # Semi
       {@s = (new('empty4'), $e);
       }
      else                                                                      # Not semi or variable
       {@s = ($e);
       }
      next;
     }

    my sub check($)                                                             # Check that the top of the stack has one of the specified elements
     {my ($types) = @_;                                                         # Possible types to match
      return 1 if index($types, type($s[-1])) > -1;                             # Check type allowed
      unexpected $s[-1], $e, $i;                                                # Complain about an unexpected type
     }

    my sub prev($)                                                              # Check that the second item on the stack contains one of the expected items
     {my ($types) = @_;                                                         # Possible types to match
      return undef unless @s >= 2;                                              # Stack not deep enough so cannot contain any of the specified types
      return 1 if index($types, type($s[-2])) > -1;
      undef
     }

    my %action =                                                                # Action on each lexical item
     (a => sub                                                                  # Assign
       {check("t");
        push @s, $e;
       },

      b => sub                                                                  # Open
       {check("bdps");
        push @s, $e;
       },

      B => sub                                                                  # Closing parenthesis
       {check("bst");
        1 while reduce;
        push @s, $e;
        1 while reduce;
        check("bst");
       },

      d => sub                                                                  # Infix but not assign or semi-colon
       {check("t");
        push @s, $e;
       },

      p => sub                                                                  # Prefix
       {check("bdp");
        push @s, $e;
       },

      q => sub                                                                  # Post fix
       {check("t");
        if (test($s[-1], 't'))                                                  # Post fix operator applied to a term
         {my $p = pop @s;
          push @s, new $e, $p;
         }
       },

      s => sub                                                                  # Semi colon
       {check("bst");
        push @s, new 'empty5' if test($s[-1], "sb");                            # Insert an empty element between two consecutive semicolons
        1 while reduce;
        push @s, $e;
       },

      v => sub                                                                  # Variable
       {check("abdps");
        push @s, new $e;
        while(prev("p"))
         {my ($l, $r) = splice @s, -2;
          push @s, new $l, $r;
         }
       },
     );

    $action{substr($e, 0, 1)}->();                                              # Dispatch the action associated with the lexical item
   }

  pop @s while @s > 1 and $s[-1] =~ m(s);                                       # Remove any trailing semi colons
  1 while reduce;                                                               # Final reductions

  if (@s != 1)                                                                  # Incomplete expression
   {my $E = expected $expression[-1];
    die "Incomplete expression. $E.\n";
   }

  if (index($last,   type $expression[-1]) == -1)                               # Incomplete expression
   {my $C = expandElement $expression[-1];
    my $E = expected      $expression[-1];
    die <<END;
$E after final $C.
END
   }

  $s[0]                                                                         # The resulting parse tree
 } # parse

=cut

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

#D1 Byte Strings                                                                # Operations on Byte Strings

sub Cstrlen()                                                                   #P Length of the C style string addressed by rax returning the length in r15
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

sub StringLength(@)                                                             # Length of a zero terminated string
 {my (@parameters) = @_;                                                        # Parameters
  Comment "Length of zero terminated string";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    $$p{string}->setReg(rax);                                                   # Address string
    Cstrlen;                                                                    # Length now in r15
    $$p{size}->getReg(r15);                                                     # Save length
    RestoreFirstFour;
   } in => {string => 3}, out => {size => 3};

  $s->call(@parameters, my $z = Vq(size));                                      # Variable that holds the length of the string
  $z
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
    data      => $data,                                                         # The start of the data
    bs        => $bs,                                                           # Variable that addresses the byte string
   );
 }

sub Nasm::X86::ByteString::chain($$$@)                                          # Return a variable with the end point of a chain of double words in the byte string starting at the specified variable.
 {my ($byteString, $bs, $variable, @offsets) = @_;                              # Byte string descriptor, byte string locator, start variable,  offsets chain
  @_ >= 3 or confess;

  PushR my @save = (r14, r15);                                                  # 14 is the byte string address, 15 the current offset in the byte string
  $bs->setReg(r14);
  $variable->setReg(r15);
  for my $o(@offsets)                                                           # Each offset
   {KeepFree r15;
    Mov r15d, "dword[r14+r15+$o]";                                               # Step through each offset
   }
  my $r = Vq(join (' ', @offsets), r15);                                        # Create a variable with the result
  PopR @save;
  $r
 }

sub Nasm::X86::ByteString::putChain($$$$@)                                      # Write the double word in the specified variable to the double word location at the the specified offset in the specified byte string.
 {my ($byteString, $bs,  $start, $value, @offsets) = @_;                        # Byte string descriptor, byte string locator variable, start variable, value to put as a variable,  offsets chain
  @_ >= 5 or confess;

  PushR my @save = (r14, r15);                                                  # 14 is the byte string address, 15 the current offset in the byte string
  $bs->setReg(r14);
  $start->setReg(r15);
  for my $i(keys @offsets)                                                      # Each offset
   {my $o = $offsets[$i];
    KeepFree r15;
    if ($i < $#offsets)                                                         # Step through each offset
     {Mov r15d, "dword[r14+r15+$o]";
     }
    else                                                                        # Address last location
     {Lea r15,       "[r14+r15+$o]";
     }
   }
  KeepFree r14;
  $value->setReg(r14);
  Mov "[r15]", r14d;
  PopR @save;
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
      $$p{bs}->copy($address);                                                  # Save new byte string address
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

sub Nasm::X86::ByteString::allocZmmBlock($@)                                    # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($byteString, @variables) = @_;                                            # Byte string, variables
  @_ >= 2 or confess;
  my $ffb = $byteString->firstFreeBlock;                                        # Check for a free block
  If ($ffb > 0, sub                                                             # Free block available
   {PushR zmm31;
    $byteString->getBlock($byteString->bs, $ffb, 31);                           # Load the first block on the free chain
    my $second = getDFromZmm(31, 60);                                 # The location of the next pointer is forced upon us by block string which got there first.
    $byteString->setFirstFreeBlock($second);                                    # Set the first free block field to point to the second block
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

sub Nasm::X86::ByteString::allocBlock($)                                        # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($byteString) = @_;                                                        # Byte string
  @_ == 1 or confess;
  $byteString->allocZmmBlock                                                    # Allocate a zmm block
   ($byteString->bs, Vq(size, RegisterSize(zmm0)), my $o = Vq(offset));
  $o                                                                            # Offset as a variable
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
  If ($block < $byteString->data->loc, sub                                      #DEBUG
   {PrintErrStringNL "Attempt to get block below start of byte string";
    Exit(1);
   });
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
  If ($block < $byteString->data->loc, sub                                      #DEBUG
   {PrintErrStringNL "Attempt to put block below start of byte string";
    Exit(1);
   });
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

sub Nasm::X86::ByteString::dump($;$)                                            # Dump details of a byte string
 {my ($byteString, $depth) = @_;                                                # Byte string descriptor, optional amount of memory to dump
  @_ == 1 or @_ == 2  or confess;
  $depth //= 4;                                                                 # Default depth

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
    for my $b(0..$depth-1)                                                      # Print the requested number of blocks
     {my $o = sprintf("%04X: ", 64 * $b);
      PrintOutString($o);
      PrintOutMemoryInHexNL;
      Add rax, 64;
     }

    RestoreFirstFour;
   } name => "Nasm::X86::ByteString::dump$depth";

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

  my $first = $s->allocBlock;                                                   # Allocate first block
  $s->first->copy($first);                                                      # Record offset of first block

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

sub Nasm::X86::BlockString::allocBlock($)                                       # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($blockString) = @_;                                                       # Block string descriptor
  @_ == 1 or confess;

  $blockString->bs->allocBlock;                                                 # Allocate block and return its offset as a variable
 }

sub Nasm::X86::BlockString::getBlockLength($$)                                  # Get the block length of the numbered zmm and return it in a variable
 {my ($blockString, $zmm) = @_;                                                 # Block string descriptor, number of zmm register
  @_ == 2 or confess;
  getBFromZmm $zmm, 0;                                                          # Block length
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
  my $L = getQFromZmm($zmm, $blockString->links);                               # Links in one register
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
    my $length = $blockString->getBlockLength(31);                              # Length of block
    PrintOutStringNL "Block String Dump";
    $block ->out("Offset: ");
    PrintOutString "   ";
    $length->outNL("Length: "); PrintOutRegisterInHex zmm31;                    # Print block

    ForEver                                                                     # Each block in string
     {my ($start, $end) = @_;                                                   #
      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Get links from current block
      If ($next == $block, sub{Jmp $end});                                      # Next block is the first block so we have printed the block string
      $blockString->getBlock($$p{bs}, $next, 31);                               # Next block in zmm
      my $length = $blockString->getBlockLength(31);                            # Length of block
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
    my $length = $blockString->getBlockLength(31);                              # Length of block

    ForEver                                                                     # Each block in string
     {my ($start, $end) = @_;                                                   #
      my ($next, $prev) = $blockString->getNextAndPrevBlockOffsetFromZmm(31);   # Get links from current block
      If ($next == $block, sub{Jmp $end});                                      # Next block is the first block so we have printed the block string
      $blockString->getBlock($$p{bs}, $next, 31);                               # Next block in zmm
      $length += $blockString->getBlockLength(31);                              # Add length of block
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

      my $new = $target->allocBlock;                                            # Allocate new block
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
    my $L = $blockString->getBlockLength(31);                                   # Length of last block
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

          my $new = $blockString->allocBlock;                                   # Allocate new block
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
      $L = $blockString->getBlockLength(31);                                    # Length of block
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
    my $L = $blockString->getBlockLength(31);                                   # Length of last block
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
      $L = $blockString->getBlockLength(31);                                    # Length of block
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
    my $L = $blockString->getBlockLength(31);                                   # Length of last block

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
      $L = $blockString->getBlockLength(31);                                    # Length of block
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
      my $lengthLast      = $blockString->getBlockLength(31);                   # Length of last block
      my $spaceLast       = $L - $lengthLast;                                   # Space in last block
      my $toCopy          = $spaceLast->min($size);                             # Amount of data required to fill first block
      my $startPos        = $O + $lengthLast;                                   # Start position in zmm
      $source->setZmm(31, $startPos, $toCopy);                                  # Append bytes
      $blockString->setBlockLengthInZmm($lengthLast + $toCopy, 31);             # Set the length
      $blockString->putBlock($B, $last, 31);                                    # Put the block
      If ($size <= $spaceLast, sub {Jmp $end});                                 # We are finished because the last block had enough space

      $source += $toCopy;                                                       # Remaining source
      $size   -= $toCopy;                                                       # Remaining source length

      my $new = $blockString->allocBlock;                                       # Allocate new block
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

  my $first = $s->allocBlock;                                                   # Allocate first block
  $s->first->copy($first);                                                      # Save first block
  $s                                                                            # Description of block array
 }

sub Nasm::X86::BlockArray::address($)                                           # Address of a block string
 {my ($blockArray) = @_;                                                        # Block array descriptor
  @_ == 1 or confess;
  $blockArray->bs->bs;
 }

sub Nasm::X86::BlockArray::allocBlock($)                                        # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($blockArray) = @_;                                                        # Block array descriptor
  @_ == 1 or confess;

  $blockArray->bs->allocBlock;
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
    my $size = getDFromZmm(31, 0);                                              # Size of array
    PrintOutStringNL("Block Array");
    $size->out("Size: ", "  ");
    PrintOutRegisterInHex zmm31;

    If ($size > $n, sub                                                         # Array has secondary blocks
     {my $T = $size / $N;                                                       # Number of full blocks

      $T->for(sub                                                               # Print out each block
       {my ($index, $start, $next, $end) = @_;                                  # Execute body
        my $S = getDFromZmm(31, ($index + 1) * $w);                             # Address secondary block from first block
        $b->getBlock($B, $S, 30);                                               # Get the secondary block
        $S->out("Full: ", "  ");
        PrintOutRegisterInHex zmm30;
       });

      my $lastBlockCount = $size % $N;                                          # Number of elements in the last block
      If ($lastBlockCount, sub                                                  # Print non empty last block
       {my $S = getDFromZmm(31, ($T + 1) * $w);                                 # Address secondary block from first block
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
    my $size = getDFromZmm(31, 0);                                              # Size of array

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
      my $new = $b->allocBlock;                                                 # Allocate new block
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
        my $new = $b->allocBlock;                                               # Allocate new block
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
        my $S = getDFromZmm(31, ($size / $N + 1) * $w);                         # Offset of second block in first block
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
    my $size = getDFromZmm(31, 0);                                              # Size of array

    If ($size > 0, sub                                                          # Array has elements
     {If ($size <= $n, sub                                                      # In the first block
       {$E       ->getDFromZmm(31, $size * $w);                                 # Get element
        ($size-1)->putDIntoZmm(31, 0);                                          # Update size
        $b       ->putBlock($B, $F, 31);                                        # Put the first block back into memory
        Jmp $success;                                                           # Element successfully retrieved from secondary block
       });

      If ($size == $N, sub                                                      # Migrate the second block to the first block now that the last slot is empty
       {PushR my @save = (rax, k7, zmm30);
        my $S = getDFromZmm(31, $w);                                            # Offset of second block in first block
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
          my $S = getDFromZmm(31, ($size / $N + 1) * $w);                       # Address secondary block from first block
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
          my $S = getDFromZmm(31, (($size-1) / $N + 1) * $w);                   # Offset of secondary block in first block
          $b       ->getBlock($B, $S, 30);                                      # Get the secondary block
          $E       ->getDFromZmm(30, (($size - 1)  % $N) * $w);                 # Get element from secondary block
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
    my $size = getDFromZmm(31, 0);                                              # Size of array

    If ($I < $size, sub                                                         # Index is in array
     {If ($size <= $n, sub                                                      # Element is in the first block
       {$E->getDFromZmm(31, ($I + 1) * $w);                                     # Get element
        Jmp $success;                                                           # Element successfully inserted in first block
       });

      If ($size <= $N * ($N - 1), sub                                           # Still within two levels
       {my $S = getDFromZmm(31, ($I / $N + 1) * $w);                            # Offset of second block in first block
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
    my $size = getDFromZmm(31, 0          );                                    # Size of array
    If ($I < $size, sub                                                         # Index is in array
     {If ($size <= $n, sub                                                      # Element is in the first block
       {$E->putDIntoZmm(31, ($I + 1) * $w);                                     # Put element
        $b->putBlock($B, $F, 31);                                               # Get the first block
        Jmp $success;                                                           # Element successfully inserted in first block
       });

      If ($size <= $N * ($N - 1), sub                                           # Still within two levels
       {my $S = getDFromZmm(31, ($I / $N + 1) * $w);                            # Offset of second block in first block
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

#D1 Block Multi Way Tree                                                        # Multi Way Tree constructed as a tree of blocks in a byte string

sub Nasm::X86::ByteString::CreateBlockMultiWayTree($)                           # Create a block multi way tree in a byte string
 {my ($byteString) = @_;                                                        # Byte string description
  @_ == 1 or confess;
  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  Comment "Allocate a new block multi way tree in a byte string";

  my $s       = genHash(__PACKAGE__."::BlockMultiWayTree",                      # Block multi way tree
    bs        => $byteString,                                                   # Byte string definition
    first     => undef,                                                         # Variable addressing offset to first block of keys
    width     => $o,                                                            # Width of a key or data slot
    keys      => $o * 1,                                                        # Offset of keys in header
    data      => $o * 2,                                                        # Offset of data in header
    node      => $o * 3,                                                        # Offset of nodes in header
    minKeys   => int($b / 2) - 1,                                               # Minimum number of keys
    maxKeys   => $b / $o - 2,                                                   # Maximum number of keys
    maxNodes  => $b / $o - 1,                                                   # Maximum number of children per parent.
    loop      => $b - $o,                                                       # Offset of keys, data, node loop
    length    => $b - $o * 2,                                                   # Offset of length in keys block
    up        => $b - $o * 2,                                                   # Offset of up in data block
    head      => undef,                                                         # Offset of header block
   );
  confess "Maximum keys must be 14" unless $s->maxKeys == 14;                   # Maximum number of keys is expected to be 14

  my $keys = $s->first = $s->allocBlock;                                        # Allocate first keys block
  my $data = $s->allocBlock;                                                    # Allocate first data block

  ClearRegisters zmm31;                                                         # Initialize first keys, data, node loop
  $s->putLoop($data, 31);                                                       # Keys loops to data
  $byteString->putBlock($s->address, $keys, 31);                                # Write first keys

  $s                                                                            # Description of block array
 }

sub Nasm::X86::BlockMultiWayTree::allocKeysDataNode($$$$@)                      #P Allocate a keys/data/node block and place it in the numbered zmm registers
 {my ($bmt, $K, $D, $N, @variables) = @_;                                       # Block multi way tree descriptor, numbered zmm for keys, numbered zmm for data, numbered zmm for children, variables
  @_ >= 4 or confess;

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters

    my $B = $$parameters{bs};                                                   # Byte string
    $bmt->bs->allocZmmBlock($B, my $k = Vq(offset));                            # Keys
    $bmt->bs->allocZmmBlock($B, my $d = Vq(offset));                            # Data
    $bmt->bs->allocZmmBlock($B, my $n = Vq(offset));                            # Children

    $bmt->putLoop($d, $K);                                                      # Set the link from key to data
    $bmt->putLoop($n, $D);                                                      # Set the link from data to node
    $bmt->putLoop($k, $N);                                                      # Set the link from node  to key
   }
  name=>qq(Nasm::X86::BlockMultiWayTree::allocKeysDataNode::${K}::${D}::${N}),  # Create a subroutine for each combination of registers encountered
  in => {bs => 3};

  $s->call($bmt->address, @variables);
 } # allocKeysDataNode

sub Nasm::X86::BlockMultiWayTree::splitNode($$$$@)                              #P Split a node given its offset in a byte string retaining the key being inserted in the node split while putting the remainder to the left or right.
 {my ($bmt, $bs, $node, $key, @variables) = @_;                                 # Block multi way tree descriptor, backing byte string, offset of node, key, variables
  @_ >= 4 or confess;

  my $K = 31; my $D = 30; my $N = 29;                                           # Key, data, node blocks

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $b = $$parameters{bs};                                                   # Byte string
    my $k = $$parameters{key};                                                  # Key we are looking for
    my $n = $$parameters{node};                                                 # Node to split

    PushR my @save = (zmm 22..31);
    $bmt->getKeysDataNode($n, $K, $D, $N);                                      # Load root node

    If ($bmt->getLengthInKeys($K) != $bmt->maxKeys, sub                         # Only split full blocks
     {Jmp $success;
     });

    my $p = $bmt->getUpFromData($D);                                            # Parent
    If ($p, sub                                                                 # Not the root
     {my $s = getDFromZmm($K, ($bmt->minKeys + 1) * $bmt->width);               # Splitting key
      If ($k < $s, sub                                                          # Split left node pushing remainder right so that we keep the key we are looking for in the left node
       {Vmovdqu64 zmm28, zmm31;                                                 # Load left node
        Vmovdqu64 zmm27, zmm30;
        Vmovdqu64 zmm26, zmm29;
        $bmt->allocKeysDataNode(25, 24, 23);                                    # Create new right node

        KeepFree zmm $N;                                                        # Reloading root
        $bmt->getKeysDataNode($p, $K, $D, $N);                                  # Load parent
        $bmt->splitFullLeftNode($b);
        $bmt->putKeysDataNode($p, $K, $D, $N);                                  # Save parent
        $bmt->putKeysDataNode($n, 28, 27, 26);                                  # Save left
        my $r = $bmt->getLoop    (23);                                          # Offset of right keys
        $bmt->putUpIntoData  ($p, 24);                                          # Reparent new block
        $bmt->putKeysDataNode($r, 25, 24, 23);                                  # Save right back into node we just split
       },
      sub                                                                       # Split right node pushing remainder left  so that we keep the key we are looking for in the right node
       {Vmovdqu64 zmm25, zmm31;                                                 # Load right node
        Vmovdqu64 zmm24, zmm30;
        Vmovdqu64 zmm23, zmm29;
        $bmt->allocKeysDataNode(28, 27, 26);                                    # Create new left node

        KeepFree zmm $N;                                                        # Reloading root
        $bmt->getKeysDataNode($p, $K, $D, $N);                                  # Load parent
        $bmt->splitFullRightNode($b);
        $bmt->putKeysDataNode($p, $K, $D, $N);                                  # Save parent
        my $l = $bmt->getLoop    (26);                                          # Offset of left keys
        $bmt->putUpIntoData  ($p, 27);                                          # Reparent new block
        $bmt->putKeysDataNode($l, 28, 27, 26);                                  # Save left
        $bmt->putKeysDataNode($n, 25, 24, 23);                                  # Save right back into node we just split
       });
     },
    sub
     {$bmt->splitFullRoot($b);                                                  # Root
      my $l = getDFromZmm($N, 0);
      my $r = getDFromZmm($N, $bmt->width);
      $bmt->putKeysDataNode($n, $K, $D, $N);                                    # Save root
      $bmt->putKeysDataNode($l, 28, 27, 26);                                    # Save left
      $bmt->putKeysDataNode($r, 25, 24, 23);                                    # Save right
     });

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in => {bs => 3, node => 3, key => 3};

  $s->call(bs=>$bs, node=>$node, key=>$key, @variables);
 } # splitNode

sub Nasm::X86::BlockMultiWayTree::reParent($$$$$@)                              #P Reparent the children of a node held in registers. The children are in the backing byte string not registers.
 {my ($bmt, $bs, $PK, $PD, $PN, @variables) = @_;                               # Block multi way tree descriptor, backing byte string, numbered zmm key node, numbered zmm data node, numbered zmm child node, variables
  @_ >= 5 or confess;
  my $b = $bmt->bs;                                                             # Underlying byte string

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters

    my $B = $$parameters{bs};                                                   # Byte string
    my $L = $bmt->getLengthInKeys($PK) + 1;                                     # Number of children
    my $p = $bmt->getUpFromData ($PD);                                          # Parent node offset as a variable

    If ($bmt->getLoop($PD), sub                                                 # Not a leaf
     {PushR my @save = (rax, rdi);
      Mov rdi, rsp;                                                             # Save stack base
      PushRR "zmm$PN";                                                          # Child nodes on stack
      my $w = $bmt->width; my $l = $bmt->loop; my $u = $bmt->up;                # Steps we will make along the chain
      my $s = Vq(start);
      $L->for(sub                                                               # Each child
       {my ($index, $start, $next, $end) = @_;
        &PopEax;                                                                # The nodes are double words but we cannot pop a double word from the stack in 64 bit long mode using pop
        $s->getReg(rax);
        KeepFree rax;
        $b->putChain($B, $s, $p, $l, $u);
       });

      Mov rsp, rdi;                                                             # Level stack
      PopR @save;
     });
   }  in => {bs => 3};

  $s->call($bmt->address, @variables);
 } # reParent

sub Nasm::X86::BlockMultiWayTree::splitFullRoot($$)                             #P Split a full root block held in 31..29 and place the left block in 28..26 and the right block in 25..23. The left and right blocks should have their loop offsets set so they can be inserted into the root.
 {my ($bmt, $bs) = @_;                                                          # Block multi way tree descriptor, byte string locator
  @_ == 2 or confess;
  my $length      = $bmt->maxKeys;                                              # Length of block to split
  my $leftLength  = $length / 2;                                                # Left split point
  my $rightLength = $length - 1 - $leftLength;                                  # Right split point

  my $TK = 31; my $TD = 30; my $TN = 29;                                        # Root key, data, node
  my $LK = 28; my $LD = 27; my $LN = 26;                                        # Key, data, node blocks in left child
  my $RK = 25; my $RD = 24; my $RN = 23;                                        # Key, data, node blocks in right child
  my $Test = 22;                                                                # Zmm used to hold test values via broadcast

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push
    my $B = $$parameters{bs};

    PushR my @save = (k6, k7, zmm22);

    If ($bmt->getLengthInKeys($TK) != $bmt->maxKeys, sub                        # Only split full blocks
     {Jmp $success;
     });

    $bmt->allocKeysDataNode(  28, 27, 26);                                      # Allocate immediate children of the root
    my $l = $bmt->getLoop(            26);
    $bmt->putKeysDataNode($l, 28, 27, 26);
    $bmt->allocKeysDataNode  (25, 24, 23);
    my $r = $bmt->getLoop            (23);
    $bmt->putKeysDataNode($l, 25, 24, 23);
    $bmt->reParent       ($B, 28, 27, 26);                                      # Reparent grandchildren
    $bmt->reParent       ($B, 25, 24, 23);

    my $n  = $bmt->getLoop($TD);                                                # Offset of node block or zero if there is no node block
    my $to = $bmt->getLoop($TN);                                                # Offset of root block
    my $lo = $bmt->getLoop($LN);                                                # Offset of left block
    my $ro = $bmt->getLoop($RN);                                                # Offset of right block

    LoadConstantIntoMaskRegister(k7, eval "0b11".'0'x$length);                  # Area to clear preserving loop and up/length
    &Vmovdqu32   (zmm $LK."{k7}{z}",   $LK);                                    # Clear left
    &Vmovdqu32   (zmm $LD."{k7}{z}",   $LD);
    &Vmovdqu32   (zmm $RK."{k7}{z}",   $RK);                                    # Clear right
    &Vmovdqu32   (zmm $RD."{k7}{z}",   $RD);

    LoadConstantIntoMaskRegister(k7, eval "0b10".'0'x$length);                  # Area to clear preserving loop
    &Vmovdqu32   (zmm $LN."{k7}{z}",   $LN);                                    # Clear left
    &Vmovdqu32   (zmm $RK."{k7}{z}",   $RK);                                    # Clear right

    LoadConstantIntoMaskRegister(k7, eval "0b".'1'x$leftLength);                # Constant mask up to the split point
    &Vmovdqu32   (zmm $LK."{k7}",      $TK);                                    # Split keys left
    &Vmovdqu32   (zmm $LD."{k7}",      $TD);                                    # Split data left
    If ($n, sub                                                                 # Split nodes left
     {&Vmovdqu32 (zmm $LN."{k7}",      $TN);
     });

    my $mr = eval "0b".('1'x$rightLength).('0'x($leftLength+1));                # Right mask
    LoadConstantIntoMaskRegister(k6, $mr);                                      # Constant mask from one beyond split point to end of keys
    LoadConstantIntoMaskRegister(k7, eval "0b".'1'x$rightLength);               # Constant mask for compressed right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $TK);                                    # Split right keys
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right keys
    &Vmovdqu32   (zmm $RK.  "{k7}",    $Test);                                  # Save right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $TD);                                    # Split right data
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right data
    &Vmovdqu32   (zmm $RD.  "{k7}",    $Test);                                  # Save right data

    If ($n, sub                                                                 # Split nodes right
     {&Vmovdqu32   (zmm $Test."{k6}{z}", $TN);                                  # Split right nodes
      &Vpcompressd (zmm $Test."{k6}",    $Test);                                # Compress right node
      &Vmovdqu32   (zmm $RN.  "{k7}",    $Test);                                # Save right node
     });

    my $k = getDFromZmm $TK, $leftLength * (my $w = $bmt->width);               # Splitting key
    my $d = getDFromZmm $TD, $leftLength * $w;                                  # Splitting data

    LoadConstantIntoMaskRegister(k7, 1);                                        # Position of key, data in root node
    $k->zBroadCastD($Test);                                                     # Broadcast keys
    &Vmovdqu32 (zmm $TK."{k7}",  $Test);                                        # Insert key in root
    $d->zBroadCastD($Test);                                                     # Broadcast keys
    &Vmovdqu32 (zmm $TD."{k7}",  $Test);                                        # Insert data in root
    LoadConstantIntoMaskRegister(k7, eval "0b11".('0'x($length-1)).'1');        # Unused fields
    &Vmovdqu32 (zmm $TK."{k7}{z}",  $TK);                                       # Clear unused keys in root
    &Vmovdqu32 (zmm $TD."{k7}{z}",  $TD);                                       # Clear unused data in root
    If ($n, sub
     {LoadConstantIntoMaskRegister(k7, eval "0b1".('0'x($length)).'1');         # Unused fields
      &Vmovdqu32 (zmm $TN."{k7}{z}",  $TN);                                     # Clear unused node in root
     });

    $bmt->putLengthInKeys($TK, Cq(one,  1));                                    # Set length of root keys
    $bmt->putLengthInKeys($LK, Cq(leftLength,  $leftLength));                   # Length of left node
    $bmt->putLengthInKeys($RK, Cq(rightLength, $rightLength));                  # Length of right node

    $bmt->putUpIntoData($to, $LD);                                              # Set parent of left node
    $bmt->putUpIntoData($to, $RD);                                              # Set parent of right node

    $lo->putDIntoZmm($TN, 0);                                                   # Insert offset of left node in root nodes
    $ro->putDIntoZmm($TN, $w);                                                  # Insert offset of right node in root nodes

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   } in => {bs => 3};

  $s->call (bs => $bs);
 } # splitFullRoot

sub Nasm::X86::BlockMultiWayTree::splitFullLeftNode($$)                         #P Split a full left node block held in 28..26 whose parent is in 31..29 and place the new right block in 25..23. The parent is assumed to be not full. The loop and length fields are assumed to be authoritative and hence are preserved.
 {my ($bmt, $bs) = @_;                                                          # Block multi way tree descriptor, byte string locator
  @_ == 2 or confess;

  my $length      = $bmt->maxKeys;                                              # Length of block to split
  my $leftLength  = $length / 2;                                                # Left split point
  my $rightLength = $length - 1 - $leftLength;                                  # Right split point

  my $PK = 31; my $PD = 30; my $PN = 29;                                        # Root key, data, node
  my $LK = 28; my $LD = 27; my $LN = 26;                                        # Key, data, node blocks in left child
  my $RK = 25; my $RD = 24; my $RN = 23;                                        # Key, data, node blocks in right child
  my $Test = 22;                                                                # Zmm used to hold test values via broadcast

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push
    my $B = $$parameters{bs};

    PushR my @save = (k6, k7, zmm22);

    If ($bmt->getLengthInKeys($LK) != $bmt->maxKeys, sub                        # Only split full blocks
     {Jmp $success;
     });

    my $n  = $bmt->getLoop($LD);                                                # Offset of node block or zero if there is no node block for the left node
    my $lo = $bmt->getLoop($LN);                                                # Offset of left block
    my $ro = $bmt->getLoop($RN);                                                # Offset of right block

    ClearRegisters k6, k7, zmm22;

    my $k = getDFromZmm $LK, $leftLength * (my $w = $bmt->width);               # Splitting key
    my $d = getDFromZmm $LD, $leftLength * $w;                                  # Splitting data

    my $mr = eval "0b".('1'x$rightLength).('0'x($leftLength+1));                # Right mask
    LoadConstantIntoMaskRegister(k6, $mr);                                      # Constant mask from one beyond split point to end of keys
    LoadConstantIntoMaskRegister(k7, eval "0b".'1'x$rightLength);               # Constant mask for compressed right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $LK);                                    # Split out right keys
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right keys
    &Vmovdqu32   (zmm $RK.  "{k7}",    $Test);                                  # Save right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $LD);                                    # Split out right data
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right data
    &Vmovdqu32   (zmm $RD.  "{k7}",    $Test);                                  # Save right data
    If ($n, sub                                                                 # Split nodes right
     {&Vmovdqu32   (zmm $Test."{k6}{z}", $LN);                                  # Split right nodes
      &Vpcompressd (zmm $Test."{k6}",    $Test);                                # Compress right node
      &Vmovdqu32   (zmm $RN.  "{k7}",    $Test);                                # Save right node
     });

    if (1)                                                                      # Prepare mask to reset moved keys
     {my $B = "0b11".('0'x($rightLength+1)).('1'x($leftLength));                # Areas to retain
      my $b = eval $B;
      LoadConstantIntoMaskRegister(k7, $b);
     }

    &Vmovdqu32   (zmm $LK."{k7}{z}",   $LK);                                    # Remove unused keys
    &Vmovdqu32   (zmm $LD."{k7}{z}",   $LD);                                    # Split data left
    If ($n, sub                                                                 # Split nodes left
     {my $B = "0b10".('0'x($rightLength+1)).('1'x($leftLength));                # Areas to retain
      my $b = eval $B;
      LoadConstantIntoMaskRegister(k7, $b);                                     # Areas to retain
      &Vmovdqu32 (zmm $LN."{k7}{z}",   $LN);
     });

    $lo->zBroadCastD($Test);                                                    # Find index in parent of left node - broadcast offset of left node so we can locate it in the parent
    LoadConstantIntoMaskRegister(k7, eval "0b".('1'x$length));                  # Nodes
    &Vpcmpud("k6{k7}", zmm($PN, $Test), 0);                                     # Check for equal offset - one of them will match to create the single insertion point in k6
    Kandnq k5, k6, k7;                                                          # Expansion mask
    &Vpexpandd (zmm $PK."{k5}", $PK);                                           # Shift up keys
    &Vpexpandd (zmm $PD."{k5}", $PD);                                           # Shift up keys
    $k->zBroadCastD($Test);                                                     # Broadcast new key
    &Vmovdqu32 (zmm $PK."{k6}", $Test);                                         # Insert new key
    $d->zBroadCastD($Test);                                                     # Broadcast new data
    &Vmovdqu32 (zmm $PD."{k6}", $Test);                                         # Insert new data

    If ($n, sub                                                                 # Insert new right node offset into parent nodes
     {Kshiftlq k6, k6, 1;                                                       # Node insertion point
      Kandnq k5, k6, k7;                                                        # Expansion mask
      &Vpexpandd (zmm $PN."{k5}", $PN);                                         # Shift up nodes
      $ro->zBroadCastD($Test);                                                  # Broadcast right node offset
      &Vmovdqu32 (zmm $PN."{k6}", $Test);                                       # Insert right node offset
     });

    my $l = $bmt->getLengthInKeys($PK);                                         # Length of parent
            $bmt->putLengthInKeys($PK, $l + 1);                                 # New length of parent
    $bmt->putLengthInKeys($LK, Cq(leftLength,  $leftLength));                   # Length of left node
    $bmt->putLengthInKeys($RK, Cq(rightLength, $rightLength));                  # Length of right node

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   } in => {bs => 3};

  $s->call (bs => $bs);
 } # splitFullLeftNode

sub Nasm::X86::BlockMultiWayTree::splitFullRightNode($$)                        #P Split a full right node block held in 25..23 whose parent is in 31..29 and place the new left block in 25..23.  The loop and length fields are assumed to be authoritative and hence are preserved.
 {my ($bmt, $bs) = @_;                                                          # Block multi way tree descriptor, byte string locator
  @_ == 2 or confess;
  my $length      = $bmt->maxKeys;                                              # Length of block to split
  my $leftLength  = $length / 2;                                                # Left split point
  my $rightLength = $length - 1 - $leftLength;                                  # Right split point

  my $PK = 31; my $PD = 30; my $PN = 29;                                        # Root key, data, node
  my $LK = 28; my $LD = 27; my $LN = 26;                                        # Key, data, node blocks in left child
  my $RK = 25; my $RD = 24; my $RN = 23;                                        # Key, data, node blocks in right child
  my $Test = 22;                                                                # Zmm used to hold test values via broadcast

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push
    my $B = $$parameters{bs};
    PushR my @save = (k6, k7, zmm22);

    If ($bmt->getLengthInKeys($RK) != $bmt->maxKeys, sub                        # Only split full blocks
     {Jmp $success;
     });

    my $n  = $bmt->getLoop($RD);                                                # Offset of node block or zero if there is no node block for the right node
    my $lo = $bmt->getLoop($LN);                                                # Offset of left block
    my $ro = $bmt->getLoop($RN);                                                # Offset of right block

    ClearRegisters k6, k7;                                                      # Clear mask registers

    LoadConstantIntoMaskRegister k7, eval "0b00".(1)x$length;                   # Left mask for keys and data
    &Vmovdqu32(zmm $LK."{k7}", $RK);                                            # Copy right keys  to left node
    &Vmovdqu32(zmm $LD."{k7}", $RD);                                            # Copy right data  to left node
    LoadConstantIntoMaskRegister k7, eval "0b01".(1)x$length;                   # Left mask for child nodes
    &Vmovdqu32(zmm $LN."{k7}", $RN);                                            # Copy right nodes to left node

    my $k = getDFromZmm $LK, $leftLength * (my $w = $bmt->width);               # Splitting key
    my $d = getDFromZmm $LD, $leftLength * $w;                                  # Splitting data

    my $mr = eval "0b".('1'x$rightLength).('0'x($leftLength+1));                # Right mask
    LoadConstantIntoMaskRegister(k6, $mr);                                      # Constant mask from one beyond split point to end of keys
    LoadConstantIntoMaskRegister(k7, eval "0b".'1'x$rightLength);               # Constant mask for compressed right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $LK);                                    # Split out right keys
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right keys
    &Vmovdqu32   (zmm $RK.  "{k7}",    $Test);                                  # Save right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $LD);                                    # Split out right data
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right data
    &Vmovdqu32   (zmm $RD.  "{k7}",    $Test);                                  # Save right data

    If ($n, sub                                                                 # Split nodes right
     {&Vmovdqu32   (zmm $Test."{k6}{z}", $LN);                                  # Split right nodes
      &Vpcompressd (zmm $Test."{k6}",    $Test);                                # Compress right node
      &Vmovdqu32   (zmm $RN.  "{k7}",    $Test);                                # Save right node
     });

    my $Br = "0b11".('0'x($rightLength+2)).('1'x($leftLength-1));               # Areas to retain on right
    my $br = eval $Br;
    LoadConstantIntoMaskRegister(k7, $br);                                      # Areas to retain

    my $Lr = "0b11".('0'x($rightLength+1)).('1'x($leftLength));                 # Areas to retain on left
    my $lr = eval $Lr;
    LoadConstantIntoMaskRegister(k6, $lr);                                      # Areas to retain

    &Vmovdqu32   (zmm $RK."{k7}{z}",   $RK);                                    # Remove unused keys on right
    &Vmovdqu32   (zmm $RD."{k7}{z}",   $RD);                                    # Remove unused data on right
    If ($n, sub                                                                 # Split nodes left
     {my $Br = "0b10".('0'x($rightLength+2)).('1'x($leftLength-1));             # Areas to retain
      my $br = eval $Br;
      LoadConstantIntoMaskRegister(k7, $br);
      &Vmovdqu32 (zmm $RN."{k7}{z}",   $RN);
     });

    &Vmovdqu32   (zmm $LK."{k6}{z}",   $LK);                                    # Remove unused keys on left
    &Vmovdqu32   (zmm $LD."{k6}{z}",   $LD);                                    # Remove unused data on left
    If ($n, sub                                                                 # Split nodes left
     {my $Lr = "0b10".('0'x($rightLength+1)).('1'x($leftLength));               # Areas to retain
      my $lr = eval $Lr;
      LoadConstantIntoMaskRegister(k6, $lr);
      &Vmovdqu32 (zmm $LN."{k6}{z}",   $LN);
     });

    $ro->zBroadCastD($Test);                                                    # Find index in parent of right node - broadcast offset of right node so we can locate it in the parent
    LoadConstantIntoMaskRegister(k7, eval "0b".('1'x$length));                  # Nodes
    &Vpcmpud("k6{k7}", zmm($PN, $Test), 0);                                     # Check for equal offset - one of them will match to create the single insertion point in k6

    Kandnq k5, k6, k7;                                                          # Expansion mask
    &Vpexpandd (zmm $PK."{k5}", $PK);                                           # Shift up keys
    &Vpexpandd (zmm $PD."{k5}", $PD);                                           # Shift up keys
    $k->zBroadCastD($Test);                                                     # Broadcast new key
    &Vmovdqu32 (zmm $PK."{k6}", $Test);                                         # Insert new key
    $d->zBroadCastD($Test);                                                     # Broadcast new data
    &Vmovdqu32 (zmm $PD."{k6}", $Test);                                         # Insert new data

    If ($n, sub                                                                 # Insert new left node offset into parent nodes
     {Kandnq k5, k6, k7;                                                        # Expansion mask
      &Vpexpandd (zmm $PN."{k5}", $PN);                                         # Shift up nodes
      $lo->zBroadCastD($Test);                                                  # Broadcast left node offset
      &Vmovdqu32 (zmm $PN."{k6}", $Test);                                       # Insert right node offset
     });

    my $l = $bmt->getLengthInKeys($PK);                                         # Length of parent
            $bmt->putLengthInKeys($PK, $l + 1);                                 # New length of parent
    $bmt->putLengthInKeys($LK, Cq(leftLength,  $leftLength));                   # Length of left node
    $bmt->putLengthInKeys($RK, Cq(rightLength, $rightLength));                  # Length of right node

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   } in => {bs => 3};

  $s->call (bs => $bs);
 } # splitFullRightNode

sub Nasm::X86::BlockMultiWayTree::findAndSplit($@)                              #P Find a key in a tree which is known to contain at least one key splitting full nodes along the path to the key.
 {my ($bmt, @variables) = @_;                                                   # Block multi way tree descriptor, variables
  @_ >= 3 or confess;
  my $W = $bmt->width;                                                          # Width of keys and data

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First keys block
    my $K = $$p{key};                                                           # Key to find

    my $tree = $F->clone;                                                       # Start at the first key block
    PushR my @save = (k6, k7, r14, r15, zmm28, zmm29, zmm30, zmm31);
    my $zmmKeys = 31; my $zmmData = 30; my $zmmNode = 29; my $zmmTest = 28;
    my $lengthMask = k6; my $testMask = k7;

    $K->setReg(r15);                                                            # Load key into test register
    Vpbroadcastd "zmm$zmmTest", r15d;
    KeepFree r15;

    $bmt->splitNode($B, $F, $K);                                                # Split the root

    ForEver                                                                     # Step down through tree
     {my ($start, $end) = @_;                                                   # Parameters
      $bmt->getKeysDataNode($tree, $zmmKeys, $zmmData, $zmmNode);               # Get the keys/data/nodes block
      my $node = getDFromZmm($zmmNode, 0);                                      # First element of node block, which will be zero if we are on a leaf

      my $l = $bmt->getLengthInKeys($zmmKeys);                                  # Length of the block
      $l->setMaskFirst($lengthMask);                                            # Set the length mask
      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmKeys", "zmm$zmmTest", 0;       # Check for equal elements
      Ktestw   $testMask, $testMask;
      IfNz                                                                      # Result mask is non zero so we must have found the key
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros gives index
        $$p{compare}->copy(Cq(zero, 0));                                        # Key found
        $$p{index}  ->getReg(r14);                                              # Index from trailing zeros
        $$p{offset} ->copy($tree);                                              # Offset of matching block
        Jmp $success;                                                           # Return
       };

      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmTest", "zmm$zmmKeys", 1;       # Check for greater elements
      Ktestw   $testMask, $testMask;
      IfNz                                                                      # Non zero implies that the key is less than some of the keys in the block
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros
        If ($node == 0, sub                                                     # We are on a leaf
         {$$p{compare}->copy(Cq(minusOne, -1));                                 # Key less than
          $$p{index}  ->getReg(r14);                                            # Index from trailing zeros
          $$p{offset} ->copy($tree);                                            # Offset of matching block
          Jmp $success;                                                         # Return
         });
        $tree->copy(getDFromZmm($zmmNode, "r14*$W"));                           # Corresponding node
        Jmp $start;                                                             # Loop
       };

      if (1)                                                                    # Key greater than all keys in block
       {If ($node == 0, sub                                                     # We have reached a leaf
         {$$p{compare}->copy(Cq(plusOne, +1));                                  # Key greater than last key
          $$p{index}  ->copy($l-1);                                             # Index of last key which we are greater than
          $$p{offset} ->copy($tree);                                            # Offset of matching block
          Jmp $success
         });
       };
      $tree->copy(getDFromZmm($zmmNode, $l * $bmt->width));                     # Greater than all keys so step through last child node
     };

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in  => {bs      => 3, first  => 3, key   => 3},
      out => {compare => 3, offset => 3, index => 3};

  $s->call($bmt->address, first => $bmt->first, @variables);
 } # findAndSplit

sub Nasm::X86::BlockMultiWayTree::find($@)                                      # Find a key in a tree and  return its associated data
 {my ($bmt, @variables) = @_;                                                   # Block multi way tree descriptor, variables
  @_ >= 3 or confess;
  my $W = $bmt->width;                                                          # Width of keys and data

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First keys block
    my $K = $$p{key};                                                           # Key to find

    my $tree = $F->clone;                                                       # Start at the first key block
    PushR my @save = (k6, k7, r14, r15, zmm28, zmm29, zmm30, zmm31);
    my $zmmKeys = 31; my $zmmData = 30; my $zmmNode = 29; my $zmmTest = 28;
    my $lengthMask = k6; my $testMask = k7;

    $K->setReg(r15);                                                            # Load key into test register
    Vpbroadcastd "zmm$zmmTest", r15d;
    KeepFree r15;

    Cq(loop, 99)->for(sub                                                       # Step down through tree
     {my ($index, $start, $next, $end) = @_;
      $bmt->getKeysDataNode($tree, $zmmKeys, $zmmData, $zmmNode);               # Get the keys block
      my $l = $bmt->getLengthInKeys($zmmKeys);                                  # Length of the block
      If ($l == 0, sub                                                          # Empty tree so we have not found the key
       {$$p{found}->copy(Cq(zero, 0));                                          # Key not found
        Jmp $success;                                                           # Return
       });

      $l->setMaskFirst($lengthMask);                                            # Set the length mask
      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmKeys", "zmm$zmmTest", 0;       # Check for equal elements
      Ktestw   $testMask, $testMask;
      IfNz                                                                      # Result mask is non zero so we must have found the key
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros
        $$p{found}->copy(Cq(one, 1));                                           # Key found
        $$p{data}->copy(getDFromZmm($zmmData, "r14*$W"));                       # Data associated with the key
        Jmp $success;                                                           # Return
       };

      my $n = getDFromZmm($zmmNode, 0);                                         # First child empty implies we are on a leaf
      If ($n == 0, sub                                                          # Zero implies that this is a leaf node
       {$$p{found}->copy(Cq(zero, 0));                                          # Key not found
        Jmp $success;                                                           # Return
       });

      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmTest", "zmm$zmmKeys", 1;       # Check for greater elements
      Ktestw   $testMask, $testMask;

      IfNz                                                                      # Non zero implies that the key is less than some of the keys
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros
        $tree->copy(getDFromZmm($zmmNode, "r14*$W"));                           # Corresponding node
        Jmp $next;                                                              # Loop
       };
      $tree->copy(getDFromZmm($zmmNode, $l * $W));                              # Greater than all keys
     });
    PrintErrStringNL "Stuck in find";                                           # We seem to be looping endlessly
    Exit(1);

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in => {bs => 3, first => 3, key => 3}, out => {data => 3, found => 3};

  $s->call($bmt->address, first => $bmt->first, @variables);
 } # find

sub Nasm::X86::BlockMultiWayTree::insert($@)                                    # Insert a (key, data) pair into the tree
 {my ($bmt, @variables) = @_;                                                   # Block multi way tree descriptor, variables
  @_ >= 2 or confess;
  my $b = $bmt->bs;                                                             # Underlying byte string
  my $W = RegisterSize zmm0;                                                    # The size of a block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{first};                                                         # First keys block
    my $K = $$p{key};                                                           # Key  to be inserted
    my $D = $$p{data};                                                          # Data to be inserted

    PushR my @save = (k4, k5, k6, k7, r14, r15, zmm 22..31);
    $bmt->getKeysDataNode($F, 31, 30, 29);                                      # Get the first block

    my $l = $bmt->getLengthInKeys(31);                                          # Length of the block
    If  $l == 0,
    Then                                                                        # Empty tree
     {$K->putDIntoZmm      (31, 0);                                             # Write key
      $bmt->putLengthInKeys (31, Cq(one, 1));                                   # Set the length of the block
      $D->putDIntoZmm      (30, 0);                                             # Write data
      $bmt->putKeysData($F, 31, 30);                                            # Write the data block back into the underlying byte string
      Jmp $success;                                                             # Insert completed successfully
     };

    my $n = $bmt->getLoop(30);                                                  # Get the offset of the node block
    If (($n == 0) & ($l < $bmt->maxKeys),
    Then                                                                        # Node is root with no children and space for more keys
     {$l->setMaskFirst(k7);                                                     # Set the compare bits
      $K->setReg(r15);                                                          # Key to search for
      Vpbroadcastd zmm22, r15d;                                                 # Load key
      KeepFree r15;
      Vpcmpud "k6{k7}", zmm22, zmm31, 0;                                        # Check for equal key
      ClearRegisters k5;                                                        # Zero so we can check the result mask against zero
      Ktestd k5, k6;                                                            # Check whether a key was equal

      IfNz                                                                      # We found a key
       {$bmt->putLengthInKeys(31, $l + 1);                                      # Set the length of the block
        $D->setReg(r14);                                                        # Key to search for
        Vpbroadcastd "zmm30{k6}", r14d;                                         # Load data
        $bmt->putKeysData($F, 31, 30);                                          # Write the data block back into the underlying byte string
        KeepFree r14;
        Jmp $success;                                                           # Insert completed successfully
       };

      Vpcmpud "k6{k7}", zmm22, zmm31, 1;                                        # Check for elements that are greater
      Ktestw   k6, k6;
      IfEq (sub                                                                 # K6 zero implies the latest key goes at the end
       {Kshiftlw k6, k7, 1;                                                     # Reach next empty field
        Kandnw   k6, k7, k6;                                                    # Remove back fill to leave a single bit at the next empty field
       },
      sub
       {Kandw    k5, k6, k7;                                                    # Tested at: # Insert key for BlockMultiWayTree but we could simplify by using a mask for the valid area
        Kandnw   k4, k5, k7;
        Kshiftlw k5, k5, 1;
        Korw     k5, k4, k5;                                                    # Broadcast mask
        Kandnw   k6, k5, k7;                                                    # Expand mask
        Vpexpandd    "zmm31{k5}", zmm31;                                        # Shift up keys
        Vpexpandd    "zmm30{k5}", zmm30;                                        # Shift up data
       });

      Vpbroadcastd "zmm31{k6}", r15d;                                           # Load key
      $D->setReg(r14);                                                          # Corresponding data
      Vpbroadcastd "zmm30{k6}", r14d;                                           # Load data
      KeepFree r14;
      $bmt->putLengthInKeys( 31, $l + 1);                                       # Set the length of the block

      If $l + 1 == $bmt->maxKeys,
      Then                                                                      # Root is now full so we have to allocate node block for it and chain it in
       {$bmt->bs->allocZmmBlock($B, my $n = Vq(offset));                        # Children
        $bmt->putLoop($n, 30);                                                  # Set the link from data to node
        $bmt->putLoop($F, 29);                                                  # Set the link from node to key
       };

      $bmt->putKeysDataNode($F, 31, 30, 29);                                    # Write the data block back into the underlying byte string
      $bmt->splitNode($B, $F, $K);                                              # Split if the leaf has got too big
      Jmp $success;                                                             # Insert completed successfully
     });

    my $compare = Vq(compare);                                                  # Comparison result
    my $offset  = Vq(offset);                                                   # Offset of result
    my $index   = Vq('index');                                                  # Index of result
    $bmt->findAndSplit($K, $compare, $offset, $index);                          # Split node if full

    KeepFree zmm 29;
    $bmt->getKeysDataNode($offset, 31, 30, 29);

    If $compare == 0,
    Then                                                                        # Found an equal key so update the data
     {$D->putDIntoZmm(30, $index * $bmt->width);                                # Update data at key
      $bmt->putKeysDataNode($offset, 31, 30, 29);                               # Rewrite data and keys
     },
    Else                                                                        # We have room for the insert because each block has been split to make it non full
     {If $compare > 0,
      Then                                                                      # Position at which to insert new key if it is greater than the indexed key
       {++$index;
       };

      my $length = $bmt->getLengthInKeys(31);                                   # Number of keys
      If $index < $length,
      Then                                                                      # Need to expand as we cannot push
       {$length->setMaskFirst(k7);                                              # Length as bits
        Kshiftlw k6, k7, 1;                                                     # Length plus one as bits with a  trailing zero
        Korw     k6, k6, k7;                                                    # Length plus one as bits with no trailing zero
        $index->clearMaskBit(k6);                                               # Zero at the index
        Vpexpandd    "zmm31{k6}", zmm31;                                        # Shift up keys
        Vpexpandd    "zmm30{k6}", zmm30;                                        # Shift up data
       };

      ClearRegisters k7;
      $index->setMaskBit(k7);                                                   # Set bit at insertion point
      $K->setReg(r15);                                                          # Corresponding data
      Vpbroadcastd "zmm31{k7}", r15d;                                           # Load key
      $D->setReg(r14);                                                          # Corresponding data
      Vpbroadcastd "zmm30{k7}", r14d;                                           # Load data
      $bmt->putLengthInKeys(31, $length + 1);                                   # Set the new length of the block
      $bmt->putKeysDataNode($offset, 31, 30, 29);                               # Rewrite data and keys
      $bmt->splitNode($B, $offset, $K);                                         # Split if the leaf has got too big
     };

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in => {bs => 3, first => 3, key => 3, data => 3};

  $s->call($bmt->address, first => $bmt->first, @variables);
 } # insert

sub Nasm::X86::BlockMultiWayTree::getKeysData($$$$)                             # Load the keys and data blocks for a node
 {my ($bmt, $offset, $zmmKeys, $zmmData) = @_;                                  # Block multi way tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys
  @_ == 4 or confess;
  my $b = $bmt->bs;                                                             # Underlying byte string
  $b->getBlock($b->bs, $offset, $zmmKeys);                                      # Get the keys block
  my $data = $bmt->getLoop($zmmKeys);                                           # Get the offset of the corresponding data block
  $b->getBlock($b->bs, $data, $zmmData);                                        # Get the data block
 }

sub Nasm::X86::BlockMultiWayTree::putKeysData($$$$)                             # Save the key and data blocks for a node
 {my ($bmt, $offset, $zmmKeys, $zmmData) = @_;                                  # Block multi way tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys
  @_ == 4 or confess;
  my $b = $bmt->bs;                                                             # Underlying byte string
  $b->putBlock($b->bs, $offset, $zmmKeys);                                      # Put the keys block
  my $data = $bmt->getLoop($zmmKeys);                                           # Get the offset of the corresponding data block
  my $up   = $bmt->getUpFromData($zmmData);                                     #DEBUG Check up pointer
  If ($up >= $offset, sub
   {PrintErrStringNL "Up is not less than node";
    Exit(0);
   });
  $b->putBlock($b->bs, $data, $zmmData);                                        # Put the data block
 }

sub Nasm::X86::BlockMultiWayTree::getNode($$$)                                  # Load the child nodes for a node
 {my ($bmt, $offset, $zmmNode) = @_;                                            # Block multi way tree descriptor, offset of nodes, numbered zmm for keys
  @_ == 3 or confess;
  $bmt->bs->getBlock($bmt->bs->bs, $offset, $zmmNode);                          # Get the node block
 }

sub Nasm::X86::BlockMultiWayTree::getKeysDataNode($$$$$)                        # Load the keys, data and child nodes for a node
 {my ($bmt, $offset, $zmmKeys, $zmmData, $zmmNode) = @_;                        # Block multi way tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys, numbered numbered for keys
  @_ == 5 or confess;
  my $b = $bmt->bs;                                                             # Underlying byte string
  $b->getBlock($b->bs, $offset, $zmmKeys);                                      # Get the keys block
  my $data = $bmt->getLoop($zmmKeys);                                           # Get the offset of the corresponding data block
  $b->getBlock($b->bs, $data, $zmmData);                                        # Get the data block
  my $node = $bmt->getLoop($zmmData);                                           # Get the offset of the corresponding node block
  If ($node, sub                                                                # Check for optional node block
   {$b->getBlock($b->bs, $node, $zmmNode);                                      # Get the node block
   },
  sub                                                                           # No children
   {ClearRegisters zmm $zmmNode;                                                # Clear the child block to signal that there was not one - if there were it would have child nodes in it which would be none zero
   });
 }

sub Nasm::X86::BlockMultiWayTree::putKeysDataNode($$$$$)                        # Save the keys, data and child nodes for a node
 {my ($bmt, $offset, $zmmKeys, $zmmData, $zmmNode) = @_;                        # Block multi way tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys, numbered numbered for keys
  @_ == 5 or confess;
  $bmt->putKeysData($offset, $zmmKeys, $zmmData);                               # Put keys and data
  my $node = $bmt->getLoop($zmmData);                                           # Get the offset of the corresponding node block
  If ($node, sub                                                                # Check for optional node block
   {$bmt->bs->putBlock($bmt->bs->bs, $node, $zmmNode);                          # Put the node block
   });
 }

sub Nasm::X86::BlockMultiWayTree::getLengthInKeys($$)                           # Get the length of the keys block in the numbered zmm and return it as a variable
 {my ($bmt, $zmm) = @_;                                                         # Block multi way tree descriptor, zmm number
  @_ == 2 or confess;
  getDFromZmm($zmm, $bmt->length);                                              # The length field as a variable
 }

sub Nasm::X86::BlockMultiWayTree::putLengthInKeys($$$)                          # Get the length of the block in the numbered zmm from the specified variable
 {my ($bmt, $zmm, $length) = @_;                                                # Block multi way tree, zmm number, length variable
  @_ == 3 or confess;
  ref($length) or confess dump($length);
  $length->putDIntoZmm($zmm, $bmt->length);                                     # Set the length field
 }

sub Nasm::X86::BlockMultiWayTree::getUpFromData($$)                             # Get the up offset from the data block in the numbered zmm and return it as a variable
 {my ($bmt, $zmm) = @_;                                                         # Block multi way tree descriptor, zmm number
  @_ == 2 or confess;
  getDFromZmm($zmm, $bmt->length);                                              # The length field as a variable
 }

sub Nasm::X86::BlockMultiWayTree::putUpIntoData($$$)                            # Put the offset of the parent keys block expressed as a variable into the numbered zmm
 {my ($bmt, $offset, $zmm) = @_;                                                # Block multi way tree descriptor, variable containing up offset, zmm number
  @_ == 3 or confess;
  defined($offset) or confess;
  $offset->putDIntoZmm($zmm, $bmt->length);                                     # Save the up offset into the data block
 }

sub Nasm::X86::BlockMultiWayTree::getLoop($$)                                   # Return the value of the loop field as a variable
 {my ($bmt, $zmm) = @_;                                                         # Block multi way tree descriptor, numbered zmm
  @_ >= 1 or confess;
  getDFromZmm($zmm, $bmt->loop);                                                # Get loop field as a variable
 }

sub Nasm::X86::BlockMultiWayTree::putLoop($$$)                                  # Set the value of the loop field from a variable
 {my ($bmt, $value, $zmm) = @_;                                                 # Block multi way tree descriptor, variable containing offset of next loop entry, numbered zmm
  @_ >= 1 or confess;
  $value->putDIntoZmm($zmm, $bmt->loop);                                        # Put loop field as a variable
 }

sub Nasm::X86::BlockMultiWayTree::leftOrRightMost($$@)                          # Return the left most or right most node
 {my ($bmt, $dir, @variables) = @_;                                             # Block multi way tree descriptor, direction: left = 0 or right = 1, variables
  @_ >= 1 or confess;
  my $success = Label;                                                          # Short circuit if ladders by jumping directly to the end after a successful push
  my $b = $bmt->bs;                                                             # Underlying byte string

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    my $B = $$p{bs};                                                            # Byte string
    my $F = $$p{node};                                                          # First block
    PushR my @save = (rax, zmm29, zmm30, zmm31);

    Cq(loopLimit, 9)->for(sub                                                   # Loop a reasonable number of times
     {my ($index, $start, $next, $end) = @_;
      $bmt->getKeysDataNode($F, 31, 30, 29);                                    # Get the first keys block
      my $n = getDFromZmm(29, 0);                                               # Get the node block offset from the data block loop
      If ($n == 0, sub                                                          # Reached the end so return the containing block
       {$$p{offset}->copy($F);
        Jmp $success;
       });
      if ($dir == 0)                                                            # Left most
       {my $l = getDFromZmm(29, 0);                                             # Get the left most node
        $F->copy($l);                                                           # Continue with the next level
       }
      else                                                                      # Right most
       {my $l = $bmt->getLengthInKeys(31);                                      # Length of the node
        my $r = getDFromZmm(31, $l);                                            # Get the right most child
        $F->copy($r);                                                           # Continue with the next level
       }
     });
    PrintErrStringNL "Stuck in LeftOrRightMost";
    Exit(1);

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   } name => $dir == 0 ? "Nasm::X86::BlockMultiWayTree::leftMost"
                       : "Nasm::X86::BlockMultiWayTree::rightMost",
     in => {bs => 3, node => 3}, out => {offset => 3};

  $s->call($bmt->address, @variables);
 }

sub Nasm::X86::BlockMultiWayTree::leftMost($@)                                  # Return the left most node
 {my ($bmt, @variables) = @_;                                                   # Block multi way tree descriptor, variables
  $bmt->leftOrRightMost(0, @variables)                                          # Return the left most node
 }

sub Nasm::X86::BlockMultiWayTree::rightMost($@)                                 # Return the right most node
 {my ($bmt,  @variables) = @_;                                                  # Block multi way tree descriptor, variables
  $bmt->leftOrRightMost(1, @variables)                                          # Return the right most node
 }

sub Nasm::X86::BlockMultiWayTree::nodeFromData($$$)                             # Load the the node block into the numbered zmm corresponding to the data block held in the numbered zmm.
 {my ($bmt, $data, $node) = @_;                                                 # Block multi way tree descriptor, numbered zmm containing data, numbered zmm to hold node block
  @_ == 3 or confess;
  my $loop = $bmt->getLoop($data);                                              # Get loop offset from data
  $bmt->getBlock($bmt->address, $loop, $node);                                  # Node
 }

sub Nasm::X86::BlockMultiWayTree::address($)                                    # Address of the byte string containing a block multi way tree
 {my ($bmt) = @_;                                                               # Block multi way tree descriptor
  @_ == 1 or confess;
  $bmt->bs->bs;
 }

sub Nasm::X86::BlockMultiWayTree::allocBlock($@)                                # Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable
 {my ($bmt, @variables) = @_;                                                   # Block multi way tree descriptor, variables
  @_ == 1 or confess;
  $bmt->bs->allocBlock                                                          # Allocate a block and return its offset as a variable
 }

sub Nasm::X86::BlockMultiWayTree::depth($@)                                     # Return the depth of a node within a tree.
 {my ($bmt, @variables) = @_;                                                   # Block multi way tree descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$parameters{bs};                                                   # Byte string
    my $N = $$parameters{node};                                                 # Starting node

    PushR my @save = (r14, r15, zmm30, zmm31);
    my $tree = $N->clone;                                                       # Start at the specified node

    Cq(loop, 9)->for(sub                                                        # Step up through tree
     {my ($index, $start, $next, $end) = @_;
      $bmt->getKeysData($tree, 31, 30);                                         # Get the keys block
      my $p = $bmt->getUpFromData(30);                                          # Parent
      If ($p == 0, sub                                                          # Empty tree so we have not found the key
       {$$parameters{depth}->copy($index+1);                                    # Key not found
        Jmp $success;                                                           # Return
       });
      $tree->copy($p);                                                          # Up to next level
     });
    PrintErrStringNL "Stuck in depth";                                          # We seem to be looping endlessly
    Exit(1);

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in => {bs => 3, node => 3}, out => {depth => 3};

  $s->call($bmt->address, @variables);
 } # depth

sub Nasm::X86::BlockMultiWayTree::iterator($)                                   # Iterate through a multi way tree
 {my ($b) = @_;                                                                 # Block multi way tree
  @_ == 1 or confess;

  my $node = Vq(node);                                                          # The current node
  $node->copy($b->first);                                                       # Start at the first node in the tree

  my $i = genHash(__PACKAGE__.'::BlockMultiWayTree::Iterator',                  # Iterator
    tree  => $b,                                                                # Tree we are iterating over
    node  => $node,                                                             # Current node within tree
    pos   => Vq('pos'),                                                         # Current position within node
    key   => Vq(key),                                                           # Key at this position
    data  => Vq(data),                                                          # Data at this position
    count => Vq(count),                                                         # Counter - number of node
    more  => Vq(more),                                                          # Iteration not yet finished
   );

  $i->pos  ->copy(Vq('pos', -1));                                               # Initialize iterator
  $i->count->copy(Vq(count,  0));
  $i->more ->copy(Vq(more,   1));
  $i->next;                                                                     # First element if any
 }

sub Nasm::X86::BlockMultiWayTree::Iterator::next($)                             # Next element in the tree
 {my ($iter) = @_;                                                              # Iterator
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $C = $$p{node};                                                          # Current node required
    $$p{count} = $$p{count} + 1;                                                # Count the calls to the iterator

    my $new  = sub                                                              # Load iterator with latest position
     {my ($node, $pos) = @_;                                                    # Parameters
      PushR my @save = (zmm31, zmm30,  zmm29);
      $$p{node}->copy($node);                                                   # Set current node
      $$p{pos} ->copy($pos);                                                    # Set current position in node
      $iter->tree->getKeysData($node, 31, 30);                                  # Load keys and data

      my $offset = $pos * $iter->tree->width;                                   # Load key and data
      $$p{key} ->copy(getDFromZmm(31, $offset));
      $$p{data}->copy(getDFromZmm(30, $offset));
      PopR @save;
     };

    my $done = sub                                                              # The tree has been completely traversed
     {PushR rax;
      Mov rax, 0;
      $$p{more}->getReg(rax);
      PopR rax;
      };

    If ($$p{pos} == -1,  sub                                                    # Initial descent
     {my $t = $iter->tree;

      PushR my @save = (zmm31, zmm30,  zmm29);
      $t->getKeysDataNode($C, 31, 30, 29);                                      # Load keys and data
      my $nodes = $t->getLoop(30);                                              # Nodes

      If ($nodes, sub                                                           # Go left if there are child nodes
       {$t->leftMost($t->address, $C, my $l = Vq(offset));
        &$new($l, Cq(zero, 0));
       },
      sub
       {my $l = $t->getLengthInKeys(31);                                        # Number of keys
        If ($l, sub                                                             # Start with the current node as it is a leaf
         {&$new($C, Cq(zero, 0));
         },
        sub
         {&$done;
         });
       });
      PopR @save;
      Jmp $success;                                                             # Return with iterator loaded
     });

    my $up = sub                                                                # Iterate up to next node that has not been visited
     {my $top = Label;                                                          # Reached the top of the tree
      my $n = $C->clone;
      my $zmmNK = 31; my $zmmPK = 28; my $zmmTest = 25;
      my $zmmND = 30; my $zmmPD = 27;
      my $zmmNN = 29; my $zmmPN = 26;
      PushR my @save = (k7, r14, r15, map {"zmm$_"} 25..31);
      my $t = $iter->tree;

      ForEver                                                                   # Up through the tree
       {my ($start, $end) = @_;                                                 # Parameters
        $t->getKeysData($n, $zmmNK, $zmmND);                                    # Load keys and data for current node
        my $p = $t->getUpFromData($zmmND);
        If ($p == 0, sub{Jmp $end});                                            # Jump to the end if we have reached the top of the tree
        $t->getKeysDataNode($p, $zmmPK, $zmmPD, $zmmPN);                        # Load keys, data and children nodes for parent which must have children
        $n->setReg(r15);                                                        # Offset of child
        Vpbroadcastd "zmm".$zmmTest, r15d;                                      # Current node broadcasted
        Vpcmpud k7, "zmm".$zmmPN, "zmm".$zmmTest, 0;                            # Check for equal offset - one of them will match to create the single insertion point in k6
        Kmovw r14d, k7;                                                         # Bit mask ready for count
        Tzcnt r14, r14;                                                         # Number of leading zeros gives us the position of the child in the parent
        my $i = Vq(indexInParent, r14);                                         # Index in parent
        my $l = $t->getLengthInKeys($zmmPK);                                     # Length of parent

        If ($i < $l, sub                                                        # Continue with this node if all the keys have yet to be finished
         {&$new($p, $i);
          Jmp $top;
         });
        $n->copy($p);                                                           # Continue with parent
       };
      &$done;                                                                   # No nodes not visited
      SetLabel $top;
      PopR @save;
     };

    $$p{pos}->copy(my $i = $$p{pos} + 1);                                       # Next position in block being scanned
    PushR my @save = (zmm31, zmm30, zmm29);
    $iter->tree->getKeysDataNode($C,    31, 30, 29);                            # Load keys and data
    my $l = $iter->tree->getLengthInKeys(31);                                   # Length of keys
    my $n = getDFromZmm(29, 0);                                       # First node will ne zero if on a leaf
    If ($n == 0, sub                                                            # Leaf
     {If ($i < $l, sub
       {&$new($C, $i);
       },
      sub
       {&$up;
       });
     },
    sub                                                                         # Node
     {my $offsetAtI = getDFromZmm(29, $i * $iter->tree->width);
      $iter->tree->leftMost(node=>$offsetAtI, my $l = Vq(offset));
      &$new($l, Cq(zero, 0));
     });

    PopR @save;
    SetLabel $success;
   }  io => {node => 3, pos => 3, key => 3, data => 3, count => 3, more => 3};

  $s->call($iter->node, $iter->pos,   $iter->key,                               # Call with iterator variables
           $iter->data, $iter->count, $iter->more);
  $iter                                                                         # Return the iterator
 }

sub Nasm::X86::BlockMultiWayTree::by($&)                                        # Call the specified body with each (key, data) from the specified tree in order
 {my ($b, $body) = @_;                                                          # Block Multi Way Tree descriptor, body
  @_ == 2 or confess;

  my $iter = $b->iterator;                                                      # Create an iterator
  my $start = SetLabel Label; my $end = Label;                                  # Start and end of loop
  If ($iter->more == 0, sub {Jmp $end});                                        # Jump to end if there are no more elements to process
  &$body($iter, $end);                                                          # Perform the body parameterized by the iterator and the end label
  $iter->next;                                                                  # Next element
  Jmp $start;                                                                   # Process next element
  SetLabel $end;                                                                # End of the loop
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
  PushR my @save = (rax, rdi);
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
  Mov rax, 60;
  Syscall;
  PopR @save;
 }

my $LocateIntelEmulator;                                                        # Location of Intel Software Development Emulator

sub LocateIntelEmulator()                                                       #P Locate the Intel Software Development Emulator
 {my @locations = qw(/var/isde/sde64 sde/sde64 ./sde64);                        # Locations at which we might find the emulator
  my $downloads = q(/home/phil/Downloads);                                      # Downloads folder

  return $LocateIntelEmulator if defined $LocateIntelEmulator;                  # Location has already been discovered

  for my $l(@locations)                                                         # Try each locations
   {return $LocateIntelEmulator = $l if -e $l;                                  # Found it - cache and return
   }

  if (qx(sde64 -version) =~ m(Intel.R. Software Development Emulator))          # Try path
   {return $LocateIntelEmulator = "sde64";
   }

  return undef unless -e $downloads;                                            # Skip local install if not developing
  my $install = <<END =~ s(\n) (  && )gsr =~ s(&&\s*\Z) ()sr;                   # Install sde
cd $downloads
curl https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2 > sde.tar.bz2
tar -xf sde.tar.bz2
sudo mkdir -p /var/isde/
sudo cp -r * /var/isde/
ls -ls /var/isde/
END

  say STDERR qx($install);                                                      # Execute install

  for my $l(@locations)                                                         # Retry install locations after install
   {return $LocateIntelEmulator = $l if -e $l;                                  # Found it - cache and return
   }
  undef                                                                         # Still not found - give up
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
  my $o3 = 'zzzTrace.txt'; my $o3a = 'zzzTraceA.txt';                           # Trace file and previous trace file
  unlink $o1, $o2, $o2;                                                         # Remove output files
  my $out  = $k ? '' : "1>$o1";
  my $err  = $k ? '' : "2>$o2";
  my $trc  =           "3>$o3";
  my $exec = $emulator                                                          # Execute with or without the emulator
             ? qq($sde -ptr-check -- ./$e $err $out $trc)
             :                    qq(./$e $err $out $trc);

  $cmd .= qq( && $exec) unless $k;                                              # Execute automatically unless suppressed by user

  $assembliesPerformed++;
  say STDERR qq($assembliesPerformed: $cmd);
  my $R    = qx($cmd);                                                          # Assemble and perhaps run

  if (!$k and $debug > 0 and -e $o3)                                            # Last trace
   {if (my @l = readFile $o3)
     {say STDERR "Last trace: ", $l[-1] if @l;
      if (-e $o3a)                                                              # Compare with last trace
       {if (my @m = readFile $o3a)
         {while (@l and @m and $l[0] == $m[0])                                  # Remove common prefix
           {shift @l; shift @m;
           }
          if (@m)                                                               # Remove point of departure
           {say STDERR "This  run went to: ".$l[0] if @l;
            say STDERR "Prior run went to: ".$m[0] if @m;
           }
         }
       }
      else                                                                      # Copy trace to back up trace if no back up trace present
       {rename $o3, $o3a;
       }
     }
   }

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
      say STDERR "Want: ", dump($e);
      say STDERR "Got : ", dump($g);
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


Version "20210629".


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

=head2 xmm(@r)

Add xmm to the front of a list of register expressions

     Parameter  Description
  1  @r         Register numbers

=head2 ymm(@r)

Add ymm to the front of a list of register expressions

     Parameter  Description
  1  @r         Register numbers

=head2 zmm(@r)

Add zmm to the front of a list of register expressions

     Parameter  Description
  1  @r         Register numbers

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


=head2 Tracing

Trace the execution of a program

=head3 Trace()

Add tracing code


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

=head2 Mask

Operations on mask registers

=head3 LoadConstantIntoMaskRegister($reg, $value)

Load a constant into a mask register

     Parameter  Description
  1  $reg       Mask register to load
  2  $value     Constant to load

B<Example:>


    Mov r14, 0;
    Kmovq k0, r14;
    KeepFree r14;
    Ktestq k0, k0;
    IfZ {PrintOutStringNL "0 & 0 == 0"};
    PrintOutZF;


    LoadConstantIntoMaskRegister k1, 1;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Ktestq k1, k1;
    IfNz {PrintOutStringNL "1 & 1 != 0"};
    PrintOutZF;


    LoadConstantIntoMaskRegister k2, eval "0b".(('1'x4).('0'x4))x2;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    PrintOutRegisterInHex k0, k1, k2;

    Mov  r15, 0x89abcdef;
    Mov  r14, 0x01234567;
    Shl  r14, 32;
    Or r15, r14;
    Push r15;
    Push r15;
    KeepFree r15;
    PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;

    my $a = Vq('aaaa');
    $a->pop;
    $a->push;
    $a->outNL;

    PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;

    ok Assemble(debug => 0, eq => <<END);
  0 & 0 == 0
  ZF=1
  1 & 1 != 0
  ZF=0
      k0: 0000 0000 0000 0000
      k1: 0000 0000 0000 0001
      k2: 0000 0000 0000 F0F0
  89AB CDEF
  aaaa: 89AB CDEF 0123 4567
  0123 4567
  END


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


=head2 Then($body)

Then body for an If statement

     Parameter  Description
  1  $body      Then body

=head2 Else($body)

Else body for an If statement

     Parameter  Description
  1  $body      Else body

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

If the zero is not set then execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

=head2 IfZ($then, $else)

If the zero is set then execute the then body else the else body

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


=head2 PrintRaxInHex($channel, $end)

Write the content of register rax in hexadecimal in big endian notation to the specified channel

     Parameter  Description
  1  $channel   Channel
  2  $end       Optional end byte

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


=head2 PrintErrZF()

Print the zero flag without disturbing it on stderr


=head2 PrintOutZF()

Print the zero flag without disturbing it on stdout


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

=head3 Variable($size, $name, $expr, %options)

Create a new variable with the specified size and name initialized via an expression

     Parameter  Description
  1  $size      Size as a power of 2
  2  $name      Name of variable
  3  $expr      Optional expression initializing variable
  4  %options   Options

=head3 Vb($name, $expr, %options)

Define a byte variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression
  3  %options   Options

=head3 Vw($name, $expr, %options)

Define a word variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression
  3  %options   Options

=head3 Vd($name, $expr, %options)

Define a double word variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression
  3  %options   Options

=head3 Vq($name, $expr, %options)

Define a quad variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression
  3  %options   Options

=head3 Cq($name, $expr, %options)

Define a quad constant

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression
  3  %options   Options

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

=head3 Nasm::X86::Variable::clone($var)

Clone a variable to create a new variable

     Parameter  Description
  1  $var       Variable to clone

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

=head2 Print variables

Print the values of variables or the memory addressed by them

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

    If ($a == 3, sub{PrintOutStringNL "a == 3"});
    ++$a; $a->outNL;
    --$a; $a->outNL;

    ok Assemble(debug => 0, eq => <<END);
  a: 0000 0000 0000 0003
  b: 0000 0000 0000 0002
  (a add b): 0000 0000 0000 0005
  ((a add b) sub a): 0000 0000 0000 0002
  (((a add b) sub a) eq b): 0000 0000 0000 0001
  (((a add b) sub a) ne b): 0000 0000 0000 0000
  (a times b): 0000 0000 0000 0006
  ((a times b) / b): 0000 0000 0000 0003
  (a % b): 0000 0000 0000 0001
  a == 3
  a: 0000 0000 0000 0004
  a: 0000 0000 0000 0003
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

=head3 Nasm::X86::Variable::getConst($variable, $constant)

Load the variable from a constant in effect setting a variable to a specified value

     Parameter  Description
  1  $variable  Variable
  2  $constant  Constant to load

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


=head3 Nasm::X86::Variable::setMaskFirst($length, $mask)

Set the first bits in the specified mask register

     Parameter  Description
  1  $length    Variable containing length to set
  2  $mask      Mask register

=head3 Nasm::X86::Variable::setMaskBit($length, $mask)

Set a bit in the specified mask register retaining the other bits

     Parameter  Description
  1  $length    Variable containing bit position to set
  2  $mask      Mask register

=head3 Nasm::X86::Variable::clearMaskBit($length, $mask)

Clear a bit in the specified mask register retaining the other bits

     Parameter  Description
  1  $length    Variable containing bit position to clear
  2  $mask      Mask register

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

=head3 Nasm::X86::Variable::saveZmm2222($target, $zmm)

Save bytes into the memory addressed by the target variable from the numbered zmm register.

     Parameter  Description
  1  $target    Variable containing the address of the source
  2  $zmm       Number of zmm to put

=head3 getBwdqFromMm($size, $mm, $offset)

Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $size      Size of get
  2  $mm        Register
  3  $offset    Offset in bytes either as a constant or as a variable

=head3 getBFromXmm($xmm, $offset)

Get the byte from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getWFromXmm($xmm, $offset)

Get the word from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getDFromXmm($xmm, $offset)

Get the double word from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getQFromXmm($xmm, $offset)

Get the quad word from the numbered xmm register and return it in a variable

     Parameter  Description
  1  $xmm       Numbered xmm
  2  $offset    Offset in bytes

=head3 getBFromZmm($zmm, $offset)

Get the byte from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $zmm       Numbered zmm
  2  $offset    Offset in bytes

=head3 getWFromZmm($zmm, $offset)

Get the word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $zmm       Numbered zmm
  2  $offset    Offset in bytes

=head3 getDFromZmm($zmm, $offset)

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
    getBFromZmm(0, 12)->outNL;
    getWFromZmm(0, 12)->outNL;

    getDFromZmm(0, 12)->outNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    getQFromZmm(0, 12)->outNL;

    is_deeply Assemble, <<END;
    zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0706 0504 0302 0100   0000 0302 0100 0000   0100 0000 0000 0000
  b at offset 12 in zmm0: 0000 0000 0000 0002
  w at offset 12 in zmm0: 0000 0000 0000 0302
  d at offset 12 in zmm0: 0000 0000 0000 0302
  q at offset 12 in zmm0: 0302 0100 0000 0302
  END


=head3 getQFromZmm($zmm, $offset)

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
    getBFromZmm(0, 12)->outNL;
    getWFromZmm(0, 12)->outNL;
    getDFromZmm(0, 12)->outNL;
    getQFromZmm(0, 12)->outNL;

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

=head2 Broadcast

Broadcast from a variable into a zmm

=head3 Nasm::X86::Variable::zBroadCastD($variable, $zmm)

Broadcast a double word in a variable into the numbered zmm.

     Parameter  Description
  1  $variable  Variable containing value to broadcast
  2  $zmm       Numbered zmm to broadcast to

=head2 Stack

Push and pop variables to and from the stack

=head3 Nasm::X86::Variable::push($variable)

Push a variable onto the stack

     Parameter  Description
  1  $variable  Variable

=head3 Nasm::X86::Variable::pop($variable)

Pop a variable from the stack

     Parameter  Description
  1  $variable  Variable

=head2 Memory

Actions on memory described by variables

=head3 Nasm::X86::Variable::clearMemory($address, $size)

Clear the memory described in this variable

     Parameter  Description
  1  $address   Address of memory to clear
  2  $size      Size of the memory to clear

=head3 Nasm::X86::Variable::copyMemory($target, $source, $size)

Copy from one block of memory to another

     Parameter  Description
  1  $target    Address of target
  2  $source    Address of source
  3  $size      Length to copy

=head3 Nasm::X86::Variable::printMemoryInHexNL($address, $channel, $size)

Write the memory addressed by a variable to stdout or stderr

     Parameter  Description
  1  $address   Address of memory
  2  $channel   Channel to print on
  3  $size      Number of bytes to print

=head3 Nasm::X86::Variable::printErrMemoryInHexNL($address, $size)

Write the memory addressed by a variable to stderr

     Parameter  Description
  1  $address   Address of memory
  2  $size      Number of bytes to print

=head3 Nasm::X86::Variable::printOutMemoryInHexNL($address, $size)

Write the memory addressed by a variable to stdout

     Parameter  Description
  1  $address   Address of memory
  2  $size      Number of bytes to print

=head3 Nasm::X86::Variable::freeMemory($address, $size)

Free the memory addressed by this variable for the specified length

     Parameter  Description
  1  $address   Address of memory to free
  2  $size      Size of the memory to free

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


=head3 Nasm::X86::Variable::allocateMemory($size)

Allocate the specified amount of memory via mmap and return its address

     Parameter  Description
  1  $size      Size

=head2 Structured Programming with variables

Structured programming operations driven off variables.

=head3 Nasm::X86::Variable::for($limit, $body)

Iterate the body limit times.

     Parameter  Description
  1  $limit     Limit
  2  $body      Body

B<Example:>


    Vq(limit,10)->for(sub
     {my ($i, $start, $next, $end) = @_;
      $i->outNL;
     });

    is_deeply Assemble, <<END;
  index: 0000 0000 0000 0000
  index: 0000 0000 0000 0001
  index: 0000 0000 0000 0002
  index: 0000 0000 0000 0003
  index: 0000 0000 0000 0004
  index: 0000 0000 0000 0005
  index: 0000 0000 0000 0006
  index: 0000 0000 0000 0007
  index: 0000 0000 0000 0008
  index: 0000 0000 0000 0009
  END


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


=head3 PopEax()

We cannot pop a double word from the stack in 64 bit long mode using pop so we improvise


B<Example:>


    Mov r14, 0;
    Kmovq k0, r14;
    KeepFree r14;
    Ktestq k0, k0;
    IfZ {PrintOutStringNL "0 & 0 == 0"};
    PrintOutZF;

    LoadConstantIntoMaskRegister k1, 1;
    Ktestq k1, k1;
    IfNz {PrintOutStringNL "1 & 1 != 0"};
    PrintOutZF;

    LoadConstantIntoMaskRegister k2, eval "0b".(('1'x4).('0'x4))x2;

    PrintOutRegisterInHex k0, k1, k2;

    Mov  r15, 0x89abcdef;
    Mov  r14, 0x01234567;
    Shl  r14, 32;
    Or r15, r14;
    Push r15;
    Push r15;
    KeepFree r15;

    PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $a = Vq('aaaa');
    $a->pop;
    $a->push;
    $a->outNL;


    PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble(debug => 0, eq => <<END);
  0 & 0 == 0
  ZF=1
  1 & 1 != 0
  ZF=0
      k0: 0000 0000 0000 0000
      k1: 0000 0000 0000 0001
      k2: 0000 0000 0000 F0F0
  89AB CDEF
  aaaa: 89AB CDEF 0123 4567
  0123 4567
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

=head1 Operating system

Interacting with the operating system.

=head2 Processes

Create and manage processes

=head3 Fork()

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


=head3 GetPid()

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


=head3 GetPidInHex()

Get process identifier in hex as 8 zero terminated bytes in rax


B<Example:>



    GetPidInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    ok Assemble =~ m(rax: 00);


=head3 GetPPid()

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


=head3 GetUid()

Get userid of current process


B<Example:>



    GetUid;                                                                       # Userid  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    my $r = Assemble;
    ok $r =~ m(rax:( 0000){3});


=head3 WaitPid()

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


=head3 ReadTimeStampCounter()

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


=head2 Memory

Allocate and print memory

=head3 PrintMemoryInHex($channel)

Dump memory from the address in rax for the length in rdi on the specified channel. As this method prints in blocks of 8 up to 7 bytes will be missing from the end unless the length is a multiple of 8 .

     Parameter  Description
  1  $channel   Channel

=head3 PrintErrMemoryInHex()

Dump memory from the address in rax for the length in rdi on stderr


=head3 PrintOutMemoryInHex()

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


=head3 PrintErrMemoryInHexNL()

Dump memory from the address in rax for the length in rdi and then print a new line


=head3 PrintOutMemoryInHexNL()

Dump memory from the address in rax for the length in rdi and then print a new line


B<Example:>


    my $N = 256;
    my $s = Rb 0..$N-1;
    AllocateMemory(Cq(size, $N), my $a = Vq(address));
    CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);

    AllocateMemory(Cq(size, $N), my $b = Vq(address));
    CopyMemory(source => $a, target => $b, Cq(size, $N));

    $b->setReg(rax);
    Mov rdi, $N;

    PrintOutMemoryInHexNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble(debug=>0, eq => <<END);
  0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
  END


=head3 PrintMemory()

Print the memory addressed by rax for a length of rdi on the specified channel


B<Example:>


    ReadFile(Vq(file, Rs($0)), (my $s = Vq(size)), my $a = Vq(address));          # Read file
    $a->setReg(rax);                                                              # Address of file in memory
    $s->setReg(rdi);                                                              # Length  of file in memory
    PrintOutMemory;                                                               # Print contents of memory to stdout

    my $r = Assemble;                                                             # Assemble and execute
    ok stringMd5Sum($r) eq fileMd5Sum($0);                                          # Output contains this file


=head3 PrintErrMemory()

Print the memory addressed by rax for a length of rdi on stderr


=head3 PrintOutMemory()

Print the memory addressed by rax for a length of rdi on stdout


B<Example:>


    Comment "Print a string from memory";
    my $s = "Hello World";
    Mov rax, Rs($s);
    Mov rdi, length $s;

    PrintOutMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(Hello World);


=head3 PrintErrMemoryNL()

Print the memory addressed by rax for a length of rdi followed by a new line on stderr


=head3 PrintOutMemoryNL()

Print the memory addressed by rax for a length of rdi followed by a new line on stdout


=head3 AllocateMemory(@variables)

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

    AllocateMemory(Cq(size, $N), my $a = Vq(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);


    AllocateMemory(Cq(size, $N), my $b = Vq(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CopyMemory(source => $a, target => $b, Cq(size, $N));

    $b->setReg(rax);
    Mov rdi, $N;
    PrintOutMemoryInHexNL;

    ok Assemble(debug=>0, eq => <<END);
  0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
  END


=head3 FreeMemory(@variables)

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


=head3 ClearMemory(@variables)

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


=head3 MaskMemory(@variables)

Write the specified byte into locations in the target mask that correspond to the locations in the source that contain the specified byte.

     Parameter   Description
  1  @variables  Variables

=head3 MaskMemoryInRange4(@variables)

Write the specified byte into locations in the target mask that correspond to the locations in the source that contain 4 bytes in the specified range.

     Parameter   Description
  1  @variables  Variables

=head3 CopyMemory(@variables)

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
    AllocateMemory(Cq(size, $N), my $a = Vq(address));

    CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    AllocateMemory(Cq(size, $N), my $b = Vq(address));

    CopyMemory(source => $a, target => $b, Cq(size, $N));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    $b->setReg(rax);
    Mov rdi, $N;
    PrintOutMemoryInHexNL;

    ok Assemble(debug=>0, eq => <<END);
  0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
  END


=head2 Files

Interact with the operating system via files.

=head3 OpenRead()

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

    is_deeply Assemble, <<END;                                                    # Channel  is now used for tracing
     rax: 0000 0000 0000 0004
     rax: 0000 0000 0000 0000
  END
    ok -e $f;                                                                     # Created file
    unlink $f;


=head3 OpenWrite()

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

    is_deeply Assemble, <<END;                                                    # Channel  is now used for tracing
     rax: 0000 0000 0000 0004
     rax: 0000 0000 0000 0000
  END
    ok -e $f;                                                                     # Created file
    unlink $f;


=head3 CloseFile()

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


    is_deeply Assemble, <<END;                                                    # Channel  is now used for tracing
     rax: 0000 0000 0000 0004
     rax: 0000 0000 0000 0000
  END
    ok -e $f;                                                                     # Created file
    unlink $f;


=head3 StatSize()

Stat a file whose name is addressed by rax to get its size in rax


B<Example:>


    Mov rax, Rs($0);                                                              # File to stat

    StatSize;                                                                     # Stat the file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    my $r = Assemble =~ s( ) ()gsr;
    if ($r =~ m(rax:([0-9a-f]{16}))is)                                            # Compare file size obtained with that from fileSize()
     {is_deeply $1, sprintf("%016X", fileSize($0));
     }


=head3 ReadFile(@variables)

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


=head3 executeFileViaBash(@variables)

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


=head3 unlinkFile(@variables)

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


=head1 Unicode

Convert utf8 to utf32

=head2 GetNextUtf8CharAsUtf32(@parameters)

Get the next utf8 encoded character from the addressed memory and return it as a utf32 char

     Parameter    Description
  1  @parameters  Parameters

=head2 ConvertUtf8ToUtf32(@parameters)

Convert a string of utf8 to an allocated block of utf32 and return its address and length.

     Parameter    Description
  1  @parameters  Parameters

B<Example:>


    my @p = my ($out, $size, $fail) = (Vq(out), Vq(size), Vq('fail'));
    my $opens = Vq(opens);
    my $class = Vq(class);

    my $Chars = Rb(0x24, 0xc2, 0xa2, 0xc9, 0x91, 0xE2, 0x82, 0xAC, 0xF0, 0x90, 0x8D, 0x88);
    my $chars = Vq(chars, $Chars);

    GetNextUtf8CharAsUtf32 in=>$chars, @p;                                        # Dollar               UTF-8 Encoding: 0x24                UTF-32 Encoding: 0x00000024
    $out->out('out1 : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$chars+1, @p;                                      # Cents                UTF-8 Encoding: 0xC2 0xA2           UTF-32 Encoding: 0x000000a2
    $out->out('out2 : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$chars+3, @p;                                      # Alpha                UTF-8 Encoding: 0xC9 0x91           UTF-32 Encoding: 0x00000251
    $out->out('out3 : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$chars+5, @p;                                      # Euro                 UTF-8 Encoding: 0xE2 0x82 0xAC      UTF-32 Encoding: 0x000020AC
    $out->out('out4 : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$chars+8, @p;                                      # Gothic Letter Hwair  UTF-8 Encoding  0xF0 0x90 0x8D 0x88 UTF-32 Encoding: 0x00010348
    $out->out('out5 : ');     $size->outNL(' size : ');

    my $statement = qq(𝖺
 𝑎𝑠𝑠𝑖𝑔𝑛 【【𝖻 𝐩𝐥𝐮𝐬 𝖼】】
AAAAAAAA);                                # A sample sentence to parse

    my $s = Cq(statement, Rs($statement));
    my $l = Cq(size,  length($statement));

    AllocateMemory($l, my $address = Vq(address));                                # Allocate enough memory for a copy of the string
    CopyMemory(source => $s, target => $address, $l);

    GetNextUtf8CharAsUtf32 in=>$address, @p;
    $out->out('outA : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$address+4, @p;
    $out->out('outB : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$address+5, @p;
    $out->out('outC : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$address+30, @p;
    $out->out('outD : ');     $size->outNL(' size : ');

    GetNextUtf8CharAsUtf32 in=>$address+35, @p;
    $out->out('outE : ');     $size->outNL(' size : ');

    $address->printOutMemoryInHexNL($l);

    Cq('newLine', 0x0A)->putBIntoZmm(0, 0);                                       # Single character classifications
    Cq('newLine', 0x01)->putBIntoZmm(0, 3);
    Cq('space',   0x20)->putBIntoZmm(0, 4);
    Cq('space',   0x02)->putBIntoZmm(0, 7);

    if (1)                                                                        # Classify a utf32 string
     {my $a = Dd(0x0001d5ba, 0x00000020, 0x0001d44e, 0x0000000a, 0x0001d5bb, 0x0001d429);
      my $t = Cq('test', $a);
      my $s = Cq('size', 6);

      ClassifyCharacters4 address=>$t, size=>$s;
      PrintOutStringNL "Convert some utf8 to utf32";
      $s->for(sub
       {my ($index, $start, $next, $end) = @_;
        my $a = $t+$index * 4;
        $a->setReg(r15);
        KeepFree r15;
        Mov r15d, "[r15]";
        KeepFree r15;
        PrintOutRegisterInHex r15;
       });
     }

    if (1)                                                                        # Convert utf8 test string to utf32
     {my @p = my ($u32, $size32, $count) = (Vq(u32), Vq(size32), Vq(count));


      ConvertUtf8ToUtf32 u8 => $s, size8 => $l,  @p;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      ClassifyCharacters4 address=>$u32, size=>$count;

      PrintOutStringNL "Convert test statement - special characters";
      $count->for(sub
       {my ($index, $start, $next, $end) = @_;
        my $a = $u32 + $index * 4;
        $a->setReg(r15);
        KeepFree r15;
        Mov r15d, "[r15]";
        KeepFree r15;
        PrintOutRegisterInHex r15;
       });

      Cq('variable', 0x0)     ->putDIntoZmm(0,  0);                               # Range classifications
      Cq('variable', 0x03)    ->putBIntoZmm(0,  3);
      Cq('variable', 0x01D5A0)->putDIntoZmm(0,  4);
      Cq('variable', 0x04)    ->putBIntoZmm(0,  7);
      Cq('variable', 0x01D434)->putDIntoZmm(0,  8);
      Cq('variable', 0x05)    ->putBIntoZmm(0, 11);
      Cq('variable', 0x01D400)->putDIntoZmm(0, 12);
      Cq('variable', 0x06)    ->putBIntoZmm(0, 15);

      Cq('variable', 0x7f)    ->putDIntoZmm(1,  0);
      Cq('variable', 0x03)    ->putBIntoZmm(1,  3);
      Cq('variable', 0x01D5D3)->putDIntoZmm(1,  4);
      Cq('variable', 0x04)    ->putBIntoZmm(1,  7);
      Cq('variable', 0x01D467)->putDIntoZmm(1,  8);
      Cq('variable', 0x05)    ->putBIntoZmm(1, 11);
      Cq('variable', 0x01D433)->putDIntoZmm(1, 12);
      Cq('variable', 0x06)    ->putBIntoZmm(1, 15);
      ClassifyInRange address=>$u32, size=>$count;

      PrintOutStringNL "Convert test statement - ranges";
      $count->for(sub
       {my ($index, $start, $next, $end) = @_;
        my $a = $u32 + $index * 4;
        $a->setReg(r15);
        KeepFree r15;
        Mov r15d, "[r15]";
        KeepFree r15;
        PrintOutRegisterInHex r15;
       });

      my $bl = Rd(0x10002045, 0x12002329, 0x1400276c, 0x16002770, 0x1c0027e6, 0x24002983, 0x26002987, 0x380029fc, 0x3a003008, 0x3e003010, 0x40003014, 0x4800ff3b, 0x4900ff3d, 0x4a00ff5b, 0x4b00ff5d, 0);
      my $bh = Rd(0x11002046, 0x1300232a, 0x1500276d, 0x1b002775, 0x230027ed, 0x25002984, 0x37002998, 0x390029fd, 0x3d00300b, 0x3f003011, 0x4700301b, 0x4800ff3b, 0x4900ff3d, 0x4a00ff5b, 0x4b00ff5d, 0);

      Vmovdqu8 zmm0, "[$bl]";
      Vmovdqu8 zmm1, "[$bh]";
      ClassifyWithInRange address=>$u32, size=>$count;

      PrintOutStringNL "Convert test statement - brackets";
      $count->for(sub
       {my ($index, $start, $next, $end) = @_;
        my $a = $u32 + $index * 4;
        $a->setReg(r15);
        KeepFree r15;
        Mov r15d, "[r15]";
        KeepFree r15;
        PrintOutRegisterInHex r15;
       });

      MatchBrackets address=>$u32, size=>$count, $opens, $fail;

      PrintOutStringNL "Convert test statement - bracket matching";
      $count->for(sub
       {my ($index, $start, $next, $end) = @_;
        my $a = $u32 + $index * 4;
        $a->setReg(r15);
        KeepFree r15;
        Mov r15d, "[r15]";
        KeepFree r15;
        PrintOutRegisterInHex r15;
       });
     }

    $address->clearMemory($l);
    $address->printOutMemoryInHexNL($l);

    ok Assemble(debug => 0, eq => <<END);
  out1 : 0000 0000 0000 0024 size : 0000 0000 0000 0001
  out2 : 0000 0000 0000 00A2 size : 0000 0000 0000 0002
  out3 : 0000 0000 0000 0251 size : 0000 0000 0000 0002
  out4 : 0000 0000 0000 20AC size : 0000 0000 0000 0003
  out5 : 0000 0000 0001 0348 size : 0000 0000 0000 0004
  outA : 0000 0000 0001 D5BA size : 0000 0000 0000 0004
  outB : 0000 0000 0000 000A size : 0000 0000 0000 0001
  outC : 0000 0000 0000 0020 size : 0000 0000 0000 0001
  outD : 0000 0000 0000 0020 size : 0000 0000 0000 0001
  outE : 0000 0000 0000 0010 size : 0000 0000 0000 0002
  F09D 96BA 0A20 F09D918E F09D 91A0 F09D91A0 F09D 9196 F09D9194 F09D 919B 20E38090 E380 90F0 9D96BB20 F09D 90A9 F09D90A5 F09D 90AE F09D90AC 20F0 9D96 BCE38091 E380 910A 4141
  Convert some utf8 to utf32
     r15: 0000 0000 0001 D5BA
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0001 D44E
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0001 D5BB
     r15: 0000 0000 0001 D429
  Convert test statement - special characters
     r15: 0000 0000 0001 D5BA
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0001 D44E
     r15: 0000 0000 0001 D460
     r15: 0000 0000 0001 D460
     r15: 0000 0000 0001 D456
     r15: 0000 0000 0001 D454
     r15: 0000 0000 0001 D45B
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0000 3010
     r15: 0000 0000 0000 3010
     r15: 0000 0000 0001 D5BB
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0001 D429
     r15: 0000 0000 0001 D425
     r15: 0000 0000 0001 D42E
     r15: 0000 0000 0001 D42C
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0001 D5BC
     r15: 0000 0000 0000 3011
     r15: 0000 0000 0000 3011
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0000 0041
     r15: 0000 0000 0000 0041
     r15: 0000 0000 0000 0041
     r15: 0000 0000 0000 0041
     r15: 0000 0000 0000 0041
     r15: 0000 0000 0000 0041
     r15: 0000 0000 0000 0041
     r15: 0000 0000 0000 0041
  Convert test statement - ranges
     r15: 0000 0000 0401 D5BA
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0501 D44E
     r15: 0000 0000 0501 D460
     r15: 0000 0000 0501 D460
     r15: 0000 0000 0501 D456
     r15: 0000 0000 0501 D454
     r15: 0000 0000 0501 D45B
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0000 3010
     r15: 0000 0000 0000 3010
     r15: 0000 0000 0401 D5BB
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0601 D429
     r15: 0000 0000 0601 D425
     r15: 0000 0000 0601 D42E
     r15: 0000 0000 0601 D42C
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0401 D5BC
     r15: 0000 0000 0000 3011
     r15: 0000 0000 0000 3011
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
  Convert test statement - brackets
     r15: 0000 0000 0401 D5BA
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0501 D44E
     r15: 0000 0000 0501 D460
     r15: 0000 0000 0501 D460
     r15: 0000 0000 0501 D456
     r15: 0000 0000 0501 D454
     r15: 0000 0000 0501 D45B
     r15: 0000 0000 0200 0020
     r15: 0000 0000 3E00 3010
     r15: 0000 0000 3E00 3010
     r15: 0000 0000 0401 D5BB
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0601 D429
     r15: 0000 0000 0601 D425
     r15: 0000 0000 0601 D42E
     r15: 0000 0000 0601 D42C
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0401 D5BC
     r15: 0000 0000 3F00 3011
     r15: 0000 0000 3F00 3011
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
  Convert test statement - bracket matching
     r15: 0000 0000 0401 D5BA
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0501 D44E
     r15: 0000 0000 0501 D460
     r15: 0000 0000 0501 D460
     r15: 0000 0000 0501 D456
     r15: 0000 0000 0501 D454
     r15: 0000 0000 0501 D45B
     r15: 0000 0000 0200 0020
     r15: 0000 0000 3E00 0015
     r15: 0000 0000 3E00 0014
     r15: 0000 0000 0401 D5BB
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0601 D429
     r15: 0000 0000 0601 D425
     r15: 0000 0000 0601 D42E
     r15: 0000 0000 0601 D42C
     r15: 0000 0000 0200 0020
     r15: 0000 0000 0401 D5BC
     r15: 0000 0000 3F00 000B
     r15: 0000 0000 3F00 000A
     r15: 0000 0000 0100 000A
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
     r15: 0000 0000 0300 0041
  0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head2 ClassifyCharacters4(@parameters)

Classify the utf32 characters in a block of memory of specified length using zmm0 formatted in double words with each word having the classification in the highest 8 bits and the utf32 character in the lower 21 bits.  The classification bits are copied into each utf32 character in the block of memory.

     Parameter    Description
  1  @parameters  Parameters

=head2 ClassifyInRange(@parameters)

Classify the utf32 characters in a block of memory of specified length using zmm0, zmm1 formatted in double words with each word in zmm1 having the classification in the highest 8 bits and with zmm0 and zmm1 having the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.  The classification bits from the first matching range are copied into each utf32 character in the block of memory.

     Parameter    Description
  1  @parameters  Parameters

=head2 ClassifyWithInRange(@parameters)

Classify the utf32 characters in a block of memory of specified length using zmm0, zmm1 formatted in double words with the classification range in the highest 8 bits of zmm0 and zmm1 and the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.  The classification bits from the position within the first matching range are copied into each utf32 character in the block of memory.

     Parameter    Description
  1  @parameters  Parameters

=head2 MatchBrackets(@parameters)

Replace a utf32 character with 24 bits of offset to the matching opening or closing bracket. Opening brackets have even codes from 0x10 to 0x4e while the corresponding closing bracket has a code one higher.

     Parameter    Description
  1  @parameters  Parameters

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


=head2 Nasm::X86::ByteString::chain($byteString, $bs, $variable, @offsets)

Return a variable with the end point of a chain of double words in the byte string starting at the specified variable.

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $bs          Byte string locator
  3  $variable    Start variable
  4  @offsets     Offsets chain

B<Example:>


    my $format = Rd(map{4*$_+24} 0..64);

    my $b = CreateByteString;
    my $a = $b->allocBlock;
    Vmovdqu8 zmm31, "[$format]";
    $b->putBlock($b->bs, $a, 31);
    my $r = $b->chain($b->bs, Vq(start, 0x18), 4);       $r->outNL("chain1: ");
    my $s = $b->chain($b->bs, $r, 4);                    $s->outNL("chain2: ");
    my $t = $b->chain($b->bs, $s, 4);                    $t->outNL("chain3: ");
    my $A = $b->chain($b->bs, Vq(start, 0x18), 4, 4, 4); $A->outNL("chain4: ");           # Get a long chain

    $b->putChain($b->bs, Vq(start, 0x18), Vq(end, 0xff), 4, 4, 4);                # Put at the end of a long chain

    $b->dump;

    my $sub = Subroutine
     {my ($p) = @_;                                                               # Parameters
      If ($$p{c} == -1,
        sub {PrintOutStringNL "C is minus one"},
        sub {PrintOutStringNL "C is NOT minus one"},
       );
      If ($$p{d} == -1,
        sub {PrintOutStringNL "D is minus one"},
        sub {PrintOutStringNL "D is NOT minus one"},
       );

      my $C = $$p{c}->clone;
      $C->outNL;

      $$p{e} += 1;
      $$p{e}->outNL('E: ');

      $$p{f}->outNL('F1: ');
      $$p{f}++;
      $$p{f}->outNL('F2: ');
     } name=> 'aaa', in => {c => 3}, io => {d => 3, e => 3, f => 3};

    my $c = Cq(c, -1);
    my $d = Cq(d, -1);
    my $e = Vq(e,  1);
    my $f = Vq(f,  2);

    $sub->call($c, $d, $e, $f);
    $f->outNL('F3: ');

    ok Assemble(debug => 0, eq => <<END);
  chain1: 0000 0000 0000 001C
  chain2: 0000 0000 0000 0020
  chain3: 0000 0000 0000 0024
  chain4: 0000 0000 0000 0024
  Byte String
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0058
  0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00001800 0000 1C00 00002000 0000 FF00 00002800 0000 2C00 00003000 0000 3400 00003800 0000 3C00 0000
  0040: 4000 0000 4400 00004800 0000 4C00 00005000 0000 5400 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  C is minus one
  D is minus one
  Clone of c: FFFF FFFF FFFF FFFF
  E: 0000 0000 0000 0002
  F1: 0000 0000 0000 0002
  F2: 0000 0000 0000 0003
  F3: 0000 0000 0000 0003
  END


=head2 Nasm::X86::ByteString::putChain($byteString, $bs, $start, $value, @offsets)

Write the double word in the specified variable to the double word location at the the specified offset in the specified byte string.

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $bs          Byte string locator variable
  3  $start       Start variable
  4  $value       Value to put as a variable
  5  @offsets     Offsets chain

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

=head2 Nasm::X86::ByteString::allocZmmBlock($byteString, @variables)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter    Description
  1  $byteString  Byte string
  2  @variables   Variables

=head2 Nasm::X86::ByteString::allocBlock($byteString)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter    Description
  1  $byteString  Byte string

B<Example:>


    my $a = CreateByteString; $a->dump;
    my $b1 = $a->allocBlock;  $a->dump;
    my $b2 = $a->allocBlock;  $a->dump;
    $a->freeBlock($b2);       $a->dump;
    $a->freeBlock($b1);       $a->dump;

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


    my $a = CreateByteString; $a->dump;
    my $b1 = $a->allocBlock;  $a->dump;
    my $b2 = $a->allocBlock;  $a->dump;
    $a->freeBlock($b2);       $a->dump;
    $a->freeBlock($b1);       $a->dump;

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

=head2 Nasm::X86::ByteString::dump($byteString, $depth)

Dump details of a byte string

     Parameter    Description
  1  $byteString  Byte string descriptor
  2  $depth       Optional amount of memory to dump

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

=head2 Nasm::X86::BlockString::allocBlock($blockString)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter     Description
  1  $blockString  Block string descriptor

=head2 Nasm::X86::BlockString::getBlockLength($blockString, $zmm)

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

=head2 Nasm::X86::BlockArray::allocBlock($blockArray)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter    Description
  1  $blockArray  Block array descriptor

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

=head1 Block Multi Way Tree

Multi Way Tree constructed as a tree of blocks in a byte string

=head2 Nasm::X86::ByteString::CreateBlockMultiWayTree($byteString)

Create a block multi way tree in a byte string

     Parameter    Description
  1  $byteString  Byte string description

B<Example:>


    Mov r14, 0;
    Kmovq k0, r14;
    KeepFree r14;
    Ktestq k0, k0;
    IfZ {PrintOutStringNL "0 & 0 == 0"};
    PrintOutZF;

    LoadConstantIntoMaskRegister k1, 1;
    Ktestq k1, k1;
    IfNz {PrintOutStringNL "1 & 1 != 0"};
    PrintOutZF;

    LoadConstantIntoMaskRegister k2, eval "0b".(('1'x4).('0'x4))x2;

    PrintOutRegisterInHex k0, k1, k2;

    Mov  r15, 0x89abcdef;
    Mov  r14, 0x01234567;
    Shl  r14, 32;
    Or r15, r14;
    Push r15;
    Push r15;
    KeepFree r15;
    PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;

    my $a = Vq('aaaa');
    $a->pop;
    $a->push;
    $a->outNL;

    PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;

    ok Assemble(debug => 0, eq => <<END);
  0 & 0 == 0
  ZF=1
  1 & 1 != 0
  ZF=0
      k0: 0000 0000 0000 0000
      k1: 0000 0000 0000 0001
      k2: 0000 0000 0000 F0F0
  89AB CDEF
  aaaa: 89AB CDEF 0123 4567
  0123 4567
  END


=head2 Nasm::X86::BlockMultiWayTree::find($bmt, @variables)

Find a key in a tree and  return its associated data

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::insert($bmt, @variables)

Insert a (key, data) pair into the tree

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::getKeysData($bmt, $offset, $zmmKeys, $zmmData)

Load the keys and data blocks for a node

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys

=head2 Nasm::X86::BlockMultiWayTree::putKeysData($bmt, $offset, $zmmKeys, $zmmData)

Save the key and data blocks for a node

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys

=head2 Nasm::X86::BlockMultiWayTree::getNode($bmt, $offset, $zmmNode)

Load the child nodes for a node

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $offset    Offset of nodes
  3  $zmmNode   Numbered zmm for keys

=head2 Nasm::X86::BlockMultiWayTree::getKeysDataNode($bmt, $offset, $zmmKeys, $zmmData, $zmmNode)

Load the keys, data and child nodes for a node

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys
  5  $zmmNode   Numbered numbered for keys

=head2 Nasm::X86::BlockMultiWayTree::putKeysDataNode($bmt, $offset, $zmmKeys, $zmmData, $zmmNode)

Save the keys, data and child nodes for a node

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys
  5  $zmmNode   Numbered numbered for keys

=head2 Nasm::X86::BlockMultiWayTree::getLengthInKeys($bmt, $zmm)

Get the length of the keys block in the numbered zmm and return it as a variable

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $zmm       Zmm number

=head2 Nasm::X86::BlockMultiWayTree::putLengthInKeys($bmt, $zmm, $length)

Get the length of the block in the numbered zmm from the specified variable

     Parameter  Description
  1  $bmt       Block multi way tree
  2  $zmm       Zmm number
  3  $length    Length variable

=head2 Nasm::X86::BlockMultiWayTree::getUpFromData($bmt, $zmm)

Get the up offset from the data block in the numbered zmm and return it as a variable

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $zmm       Zmm number

=head2 Nasm::X86::BlockMultiWayTree::putUpIntoData($bmt, $offset, $zmm)

Put the offset of the parent keys block expressed as a variable into the numbered zmm

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $offset    Variable containing up offset
  3  $zmm       Zmm number

=head2 Nasm::X86::BlockMultiWayTree::getLoop($bmt, $zmm)

Return the value of the loop field as a variable

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $zmm       Numbered zmm

=head2 Nasm::X86::BlockMultiWayTree::putLoop($bmt, $value, $zmm)

Set the value of the loop field from a variable

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $value     Variable containing offset of next loop entry
  3  $zmm       Numbered zmm

=head2 Nasm::X86::BlockMultiWayTree::leftOrRightMost($bmt, $dir, @variables)

Return the left most or right most node

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  $dir        Direction: left = 0 or right = 1
  3  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::leftMost($bmt, @variables)

Return the left most node

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::rightMost($bmt, @variables)

Return the right most node

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::nodeFromData($bmt, $data, $node)

Load the the node block into the numbered zmm corresponding to the data block held in the numbered zmm.

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $data      Numbered zmm containing data
  3  $node      Numbered zmm to hold node block

=head2 Nasm::X86::BlockMultiWayTree::address($bmt)

Address of the byte string containing a block multi way tree

     Parameter  Description
  1  $bmt       Block multi way tree descriptor

=head2 Nasm::X86::BlockMultiWayTree::allocBlock($bmt, @variables)

Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::depth($bmt, @variables)

Return the depth of a node within a tree.

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::iterator($b)

Iterate through a multi way tree

     Parameter  Description
  1  $b         Block multi way tree

=head2 Nasm::X86::BlockMultiWayTree::Iterator::next($iter)

Next element in the tree

     Parameter  Description
  1  $iter      Iterator

=head2 Nasm::X86::BlockMultiWayTree::by($b, $body)

Call the specified body with each (key, data) from the specified tree in order

     Parameter  Description
  1  $b         Block Multi Way Tree descriptor
  2  $body      Body

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



=head1 Hash Definitions




=head2 Nasm::X86 Definition


Iterator




=head3 Output fields


=head4 bs

Byte string definition

=head4 constant

Constant if true

=head4 count

Counter - number of node

=head4 data

Data at this position

=head4 depth

Lexical depth of scope

=head4 expr

Expression that initializes the variable

=head4 first

Variable addressing offset to first block of keys

=head4 free

Free chain offset

=head4 head

Offset of header block

=head4 key

Key at this position

=head4 keys

Offset of keys in header

=head4 label

Address in memory

=head4 laneSize

Size of the lanes in this variable

=head4 length

Offset of length in keys block

=head4 links

Location of links in bytes in zmm

=head4 loop

Offset of keys, data, node loop

=head4 maxKeys

Maximum number of keys

=head4 maxNodes

Maximum number of children per parent.

=head4 minKeys

Minimum number of keys

=head4 more

Iteration not yet finished

=head4 name

Name of the variable

=head4 next

Location of next offset in block in bytes

=head4 node

Current node within tree

=head4 number

Number of this scope

=head4 parent

Parent scope

=head4 pos

Current position within node

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

=head4 tree

Tree we are iterating over

=head4 up

Offset of up in data block

=head4 used

Used field details

=head4 width

Width of a key or data slot



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

=head2 ClassifyRange($recordOffsetInRange, @parameters)

Implementation of ClassifyInRange and ClassifyWithinRange

     Parameter             Description
  1  $recordOffsetInRange  Record offset in range if true
  2  @parameters           Parameters

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

=head2 Nasm::X86::BlockMultiWayTree::allocKeysDataNode($bmt, $K, $D, $N, @variables)

Allocate a keys/data/node block and place it in the numbered zmm registers

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  $K          Numbered zmm for keys
  3  $D          Numbered zmm for data
  4  $N          Numbered zmm for children
  5  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::splitNode($bmt, $bs, $node, $key, @variables)

Split a node given its offset in a byte string retaining the key being inserted in the node split while putting the remainder to the left or right.

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  $bs         Backing byte string
  3  $node       Offset of node
  4  $key        Key
  5  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::reParent($bmt, $bs, $PK, $PD, $PN, @variables)

Reparent the children of a node held in registers. The children are in the backing byte string not registers.

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  $bs         Backing byte string
  3  $PK         Numbered zmm key node
  4  $PD         Numbered zmm data node
  5  $PN         Numbered zmm child node
  6  @variables  Variables

=head2 Nasm::X86::BlockMultiWayTree::splitFullRoot($bmt, $bs)

Split a full root block held in 31..29 and place the left block in 28..26 and the right block in 25..23. The left and right blocks should have their loop offsets set so they can be inserted into the root.

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $bs        Byte string locator

=head2 Nasm::X86::BlockMultiWayTree::splitFullLeftNode($bmt, $bs)

Split a full left node block held in 28..26 whose parent is in 31..29 and place the new right block in 25..23. The parent is assumed to be not full. The loop and length fields are assumed to be authoritative and hence are preserved.

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $bs        Byte string locator

B<Example:>


    my $Sk = Rd(17..28, 0, 0, 12,   0xFF);
    my $Sd = Rd(17..28, 0, 0, 0xDD, 0xEE);
    my $Sn = Rd(1..13,     0, 0,    0xCC);

    my $sk = Rd(1..14, 14,   0xA1);
    my $sd = Rd(1..14, 0xCC, 0xA2);
    my $sn = Rd(1..15,       0xA3);

    my $rk = Rd((0)x14, 14,   0xB1);
    my $rd = Rd((0)x14, 0xCC, 0xB2);
    my $rn = Rd((0)x15,       0xB3);

    my $b = CreateByteString;
    my $t = $b->CreateBlockMultiWayTree;

    Vmovdqu8 zmm31, "[$Sk]";
    Vmovdqu8 zmm30, "[$Sd]";
    Vmovdqu8 zmm29, "[$Sn]";

    Vmovdqu8 zmm28, "[$sk]";
    Vmovdqu8 zmm27, "[$sd]";
    Vmovdqu8 zmm26, "[$sn]";

    Vmovdqu8 zmm25, "[$rk]";
    Vmovdqu8 zmm24, "[$rd]";
    Vmovdqu8 zmm23, "[$rn]";

     $t->splitFullLeftNode($b->bs);

    PrintOutRegisterInHex reverse zmm(23..31);

    ok Assemble(debug => 0, eq => <<END);
   zmm31: 0000 00FF 0000 000D   0000 0000 0000 0000   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
   zmm30: 0000 00EE 0000 00DD   0000 0000 0000 0000   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
   zmm29: 0000 00CC 0000 0000   0000 0000 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
   zmm28: 0000 00A1 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
   zmm27: 0000 00A2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
   zmm26: 0000 00A3 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
   zmm25: 0000 00B1 0000 0006   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
   zmm24: 0000 00B2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
   zmm23: 0000 00B3 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
  END


=head2 Nasm::X86::BlockMultiWayTree::splitFullRightNode($bmt, $bs)

Split a full right node block held in 25..23 whose parent is in 31..29 and place the new left block in 25..23.  The loop and length fields are assumed to be authoritative and hence are preserved.

     Parameter  Description
  1  $bmt       Block multi way tree descriptor
  2  $bs        Byte string locator

B<Example:>


    my $tk = Rd(1..12, 0, 0, 12,      0xC1);
    my $td = Rd(1..12, 0, 0,  0,      0xC2);
    my $tn = Rd(1, 0xBB, 3..13, 0, 0, 0xCC);

    my $lk = Rd(17..30, 14,   0xA1);
    my $ld = Rd(17..30, 0xCC, 0xA2);
    my $ln = Rd(17..31,       0xAA);

    my $rk = Rd(17..30, 14,   0xB1);
    my $rd = Rd(17..30, 0xCC, 0xB2);
    my $rn = Rd(17..31,       0xBB);

    my $b = CreateByteString;
    my $t = $b->CreateBlockMultiWayTree;

    Vmovdqu8 zmm31, "[$tk]";
    Vmovdqu8 zmm30, "[$td]";
    Vmovdqu8 zmm29, "[$tn]";

    Vmovdqu8 zmm28, "[$lk]";
    Vmovdqu8 zmm27, "[$ld]";
    Vmovdqu8 zmm26, "[$ln]";

    Vmovdqu8 zmm25, "[$rk]";
    Vmovdqu8 zmm24, "[$rd]";
    Vmovdqu8 zmm23, "[$rn]";

    $t->splitFullRightNode($b->bs);

    PrintOutRegisterInHex reverse zmm(23..31);

    ok Assemble(debug => 0, eq => <<END);
   zmm31: 0000 00C1 0000 000D   0000 0000 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0018 0000 0001
   zmm30: 0000 00C2 0000 0000   0000 0000 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0018 0000 0001
   zmm29: 0000 00CC 0000 0000   0000 000D 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 00BB   0000 00AA 0000 0001
   zmm28: 0000 00A1 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
   zmm27: 0000 00A2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
   zmm26: 0000 00AA 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
   zmm25: 0000 00B1 0000 0006   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
   zmm24: 0000 00B2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
   zmm23: 0000 00BB 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
  END


=head2 Nasm::X86::BlockMultiWayTree::findAndSplit($bmt, @variables)

Find a key in a tree which is known to contain at least one key splitting full nodes along the path to the key.

     Parameter   Description
  1  $bmt        Block multi way tree descriptor
  2  @variables  Variables

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

6 L<ClassifyCharacters4|/ClassifyCharacters4> - Classify the utf32 characters in a block of memory of specified length using zmm0 formatted in double words with each word having the classification in the highest 8 bits and the utf32 character in the lower 21 bits.

7 L<ClassifyInRange|/ClassifyInRange> - Classify the utf32 characters in a block of memory of specified length using zmm0, zmm1 formatted in double words with each word in zmm1 having the classification in the highest 8 bits and with zmm0 and zmm1 having the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.

8 L<ClassifyRange|/ClassifyRange> - Implementation of ClassifyInRange and ClassifyWithinRange

9 L<ClassifyWithInRange|/ClassifyWithInRange> - Classify the utf32 characters in a block of memory of specified length using zmm0, zmm1 formatted in double words with the classification range in the highest 8 bits of zmm0 and zmm1 and the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.

10 L<ClearMemory|/ClearMemory> - Clear memory - the address of the memory is in rax, the length in rdi

11 L<ClearRegisters|/ClearRegisters> - Clear registers by setting them to zero

12 L<ClearZF|/ClearZF> - Clear the zero flag

13 L<CloseFile|/CloseFile> - Close the file whose descriptor is in rax

14 L<Comment|/Comment> - Insert a comment into the assembly code

15 L<ConcatenateShortStrings|/ConcatenateShortStrings> - Concatenate the numbered source zmm containing a short string with the short string in the numbered target zmm.

16 L<ConvertUtf8ToUtf32|/ConvertUtf8ToUtf32> - Convert a string of utf8 to an allocated block of utf32 and return its address and length.

17 L<CopyMemory|/CopyMemory> - Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi

18 L<Cq|/Cq> - Define a quad constant

19 L<cr|/cr> - Call a subroutine with a reordering of the registers.

20 L<CreateByteString|/CreateByteString> - Create an relocatable string of bytes in an arena and returns its address in rax.

21 L<Cstrlen|/Cstrlen> - Length of the C style string addressed by rax returning the length in r15

22 L<Db|/Db> - Layout bytes in the data segment and return their label

23 L<Dbwdq|/Dbwdq> - Layout data

24 L<DComment|/DComment> - Insert a comment into the data segment

25 L<Dd|/Dd> - Layout double words in the data segment and return their label

26 L<Dq|/Dq> - Layout quad words in the data segment and return their label

27 L<Ds|/Ds> - Layout bytes in memory and return their label

28 L<Dw|/Dw> - Layout words in the data segment and return their label

29 L<Else|/Else> - Else body for an If statement

30 L<executeFileViaBash|/executeFileViaBash> - Execute the file named in the byte string addressed by rax with bash

31 L<Exit|/Exit> - Exit with the specified return code or zero if no return code supplied.

32 L<Extern|/Extern> - Name external references

33 L<Float32|/Float32> - 32 bit float

34 L<Float64|/Float64> - 64 bit float

35 L<For|/For> - For - iterate the body as long as register is less than limit incrementing by increment each time

36 L<ForEver|/ForEver> - Iterate for ever

37 L<ForIn|/ForIn> - For - iterate the full body as long as register plus increment is less than than limit incrementing by increment each time then increment the last body for the last non full block.

38 L<Fork|/Fork> - Fork

39 L<FreeMemory|/FreeMemory> - Free memory

40 L<getBFromXmm|/getBFromXmm> - Get the byte from the numbered xmm register and return it in a variable

41 L<getBFromZmm|/getBFromZmm> - Get the byte from the numbered zmm register and return it in a variable

42 L<getBwdqFromMm|/getBwdqFromMm> - Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable

43 L<getDFromXmm|/getDFromXmm> - Get the double word from the numbered xmm register and return it in a variable

44 L<getDFromZmm|/getDFromZmm> - Get the double word from the numbered zmm register and return it in a variable

45 L<GetLengthOfShortString|/GetLengthOfShortString> - Get the length of the short string held in the numbered zmm register into the specified register

46 L<GetNextUtf8CharAsUtf32|/GetNextUtf8CharAsUtf32> - Get the next utf8 encoded character from the addressed memory and return it as a utf32 char

47 L<GetPid|/GetPid> - Get process identifier

48 L<GetPidInHex|/GetPidInHex> - Get process identifier in hex as 8 zero terminated bytes in rax

49 L<GetPPid|/GetPPid> - Get parent process identifier

50 L<getQFromXmm|/getQFromXmm> - Get the quad word from the numbered xmm register and return it in a variable

51 L<getQFromZmm|/getQFromZmm> - Get the quad word from the numbered zmm register and return it in a variable

52 L<GetUid|/GetUid> - Get userid of current process

53 L<getWFromXmm|/getWFromXmm> - Get the word from the numbered xmm register and return it in a variable

54 L<getWFromZmm|/getWFromZmm> - Get the word from the numbered zmm register and return it in a variable

55 L<Hash|/Hash> - Hash a string addressed by rax with length held in rdi and return the hash code in r15

56 L<hexTranslateTable|/hexTranslateTable> - Create/address a hex translate table and return its label

57 L<If|/If> - If

58 L<IfEq|/IfEq> - If equal execute the then body else the else body

59 L<IfGe|/IfGe> - If greater than or equal execute the then body else the else body

60 L<IfGt|/IfGt> - If greater than execute the then body else the else body

61 L<IfLe|/IfLe> - If less than or equal execute the then body else the else body

62 L<IfLt|/IfLt> - If less than execute the then body else the else body

63 L<IfNe|/IfNe> - If not equal execute the then body else the else body

64 L<IfNz|/IfNz> - If the zero is not set then execute the then body else the else body

65 L<IfZ|/IfZ> - If the zero is set then execute the then body else the else body

66 L<Keep|/Keep> - Mark free registers so that they are not updated until we Free them or complain if the register is already in use.

67 L<KeepFree|/KeepFree> - Free registers so that they can be reused

68 L<KeepPop|/KeepPop> - Reset the status of the specified registers to the status quo ante the last push

69 L<KeepPush|/KeepPush> - Push the current status of the specified registers and then mark them as free

70 L<KeepReturn|/KeepReturn> - Pop the specified register and mark it as in use to effect a subroutine return with this register.

71 L<KeepSet|/KeepSet> - Confirm that the specified registers are in use

72 L<Label|/Label> - Create a unique label

73 L<Link|/Link> - Libraries to link with

74 L<LoadConstantIntoMaskRegister|/LoadConstantIntoMaskRegister> - Load a constant into a mask register

75 L<LoadShortStringFromMemoryToZmm|/LoadShortStringFromMemoryToZmm> - Load the short string addressed by rax into the zmm register with the specified number

76 L<LoadShortStringFromMemoryToZmm2|/LoadShortStringFromMemoryToZmm2> - Load the short string addressed by rax into the zmm register with the specified number

77 L<LocalData|/LocalData> - Map local data

78 L<LocateIntelEmulator|/LocateIntelEmulator> - Locate the Intel Software Development Emulator

79 L<Macro|/Macro> - Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub

80 L<MaskMemory|/MaskMemory> - Write the specified byte into locations in the target mask that correspond to the locations in the source that contain the specified byte.

81 L<MaskMemoryInRange4|/MaskMemoryInRange4> - Write the specified byte into locations in the target mask that correspond to the locations in the source that contain 4 bytes in the specified range.

82 L<MatchBrackets|/MatchBrackets> - Replace a utf32 character with 24 bits of offset to the matching opening or closing bracket.

83 L<Nasm::X86::BlockArray::address|/Nasm::X86::BlockArray::address> - Address of a block string

84 L<Nasm::X86::BlockArray::allocBlock|/Nasm::X86::BlockArray::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

85 L<Nasm::X86::BlockArray::dump|/Nasm::X86::BlockArray::dump> - Dump a block array

86 L<Nasm::X86::BlockArray::get|/Nasm::X86::BlockArray::get> - Get an element from the array

87 L<Nasm::X86::BlockArray::pop|/Nasm::X86::BlockArray::pop> - Pop an element from an array

88 L<Nasm::X86::BlockArray::push|/Nasm::X86::BlockArray::push> - Push an element onto the array

89 L<Nasm::X86::BlockArray::put|/Nasm::X86::BlockArray::put> - Put an element into an array as long as it is with in its limits established by pushing.

90 L<Nasm::X86::BlockMultiWayTree::address|/Nasm::X86::BlockMultiWayTree::address> - Address of the byte string containing a block multi way tree

91 L<Nasm::X86::BlockMultiWayTree::allocBlock|/Nasm::X86::BlockMultiWayTree::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

92 L<Nasm::X86::BlockMultiWayTree::allocKeysDataNode|/Nasm::X86::BlockMultiWayTree::allocKeysDataNode> - Allocate a keys/data/node block and place it in the numbered zmm registers

93 L<Nasm::X86::BlockMultiWayTree::by|/Nasm::X86::BlockMultiWayTree::by> - Call the specified body with each (key, data) from the specified tree in order

94 L<Nasm::X86::BlockMultiWayTree::depth|/Nasm::X86::BlockMultiWayTree::depth> - Return the depth of a node within a tree.

95 L<Nasm::X86::BlockMultiWayTree::find|/Nasm::X86::BlockMultiWayTree::find> - Find a key in a tree and  return its associated data

96 L<Nasm::X86::BlockMultiWayTree::findAndSplit|/Nasm::X86::BlockMultiWayTree::findAndSplit> - Find a key in a tree which is known to contain at least one key splitting full nodes along the path to the key.

97 L<Nasm::X86::BlockMultiWayTree::getKeysData|/Nasm::X86::BlockMultiWayTree::getKeysData> - Load the keys and data blocks for a node

98 L<Nasm::X86::BlockMultiWayTree::getKeysDataNode|/Nasm::X86::BlockMultiWayTree::getKeysDataNode> - Load the keys, data and child nodes for a node

99 L<Nasm::X86::BlockMultiWayTree::getLengthInKeys|/Nasm::X86::BlockMultiWayTree::getLengthInKeys> - Get the length of the keys block in the numbered zmm and return it as a variable

100 L<Nasm::X86::BlockMultiWayTree::getLoop|/Nasm::X86::BlockMultiWayTree::getLoop> - Return the value of the loop field as a variable

101 L<Nasm::X86::BlockMultiWayTree::getNode|/Nasm::X86::BlockMultiWayTree::getNode> - Load the child nodes for a node

102 L<Nasm::X86::BlockMultiWayTree::getUpFromData|/Nasm::X86::BlockMultiWayTree::getUpFromData> - Get the up offset from the data block in the numbered zmm and return it as a variable

103 L<Nasm::X86::BlockMultiWayTree::insert|/Nasm::X86::BlockMultiWayTree::insert> - Insert a (key, data) pair into the tree

104 L<Nasm::X86::BlockMultiWayTree::iterator|/Nasm::X86::BlockMultiWayTree::iterator> - Iterate through a multi way tree

105 L<Nasm::X86::BlockMultiWayTree::Iterator::next|/Nasm::X86::BlockMultiWayTree::Iterator::next> - Next element in the tree

106 L<Nasm::X86::BlockMultiWayTree::leftMost|/Nasm::X86::BlockMultiWayTree::leftMost> - Return the left most node

107 L<Nasm::X86::BlockMultiWayTree::leftOrRightMost|/Nasm::X86::BlockMultiWayTree::leftOrRightMost> - Return the left most or right most node

108 L<Nasm::X86::BlockMultiWayTree::nodeFromData|/Nasm::X86::BlockMultiWayTree::nodeFromData> - Load the the node block into the numbered zmm corresponding to the data block held in the numbered zmm.

109 L<Nasm::X86::BlockMultiWayTree::putKeysData|/Nasm::X86::BlockMultiWayTree::putKeysData> - Save the key and data blocks for a node

110 L<Nasm::X86::BlockMultiWayTree::putKeysDataNode|/Nasm::X86::BlockMultiWayTree::putKeysDataNode> - Save the keys, data and child nodes for a node

111 L<Nasm::X86::BlockMultiWayTree::putLengthInKeys|/Nasm::X86::BlockMultiWayTree::putLengthInKeys> - Get the length of the block in the numbered zmm from the specified variable

112 L<Nasm::X86::BlockMultiWayTree::putLoop|/Nasm::X86::BlockMultiWayTree::putLoop> - Set the value of the loop field from a variable

113 L<Nasm::X86::BlockMultiWayTree::putUpIntoData|/Nasm::X86::BlockMultiWayTree::putUpIntoData> - Put the offset of the parent keys block expressed as a variable into the numbered zmm

114 L<Nasm::X86::BlockMultiWayTree::reParent|/Nasm::X86::BlockMultiWayTree::reParent> - Reparent the children of a node held in registers.

115 L<Nasm::X86::BlockMultiWayTree::rightMost|/Nasm::X86::BlockMultiWayTree::rightMost> - Return the right most node

116 L<Nasm::X86::BlockMultiWayTree::splitFullLeftNode|/Nasm::X86::BlockMultiWayTree::splitFullLeftNode> - Split a full left node block held in 28.

117 L<Nasm::X86::BlockMultiWayTree::splitFullRightNode|/Nasm::X86::BlockMultiWayTree::splitFullRightNode> - Split a full right node block held in 25.

118 L<Nasm::X86::BlockMultiWayTree::splitFullRoot|/Nasm::X86::BlockMultiWayTree::splitFullRoot> - Split a full root block held in 31.

119 L<Nasm::X86::BlockMultiWayTree::splitNode|/Nasm::X86::BlockMultiWayTree::splitNode> - Split a node given its offset in a byte string retaining the key being inserted in the node split while putting the remainder to the left or right.

120 L<Nasm::X86::BlockString::address|/Nasm::X86::BlockString::address> - Address of a block string

121 L<Nasm::X86::BlockString::allocBlock|/Nasm::X86::BlockString::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

122 L<Nasm::X86::BlockString::append|/Nasm::X86::BlockString::append> - Append the specified content in memory to the specified block string

123 L<Nasm::X86::BlockString::clear|/Nasm::X86::BlockString::clear> - Clear the block by freeing all but the first block

124 L<Nasm::X86::BlockString::concatenate|/Nasm::X86::BlockString::concatenate> - Concatenate two block strings by appending a copy of the source to the target block string.

125 L<Nasm::X86::BlockString::deleteChar|/Nasm::X86::BlockString::deleteChar> - Delete a character in a block string

126 L<Nasm::X86::BlockString::dump|/Nasm::X86::BlockString::dump> - Dump a block string to sysout

127 L<Nasm::X86::BlockString::getBlock|/Nasm::X86::BlockString::getBlock> - Get the block with the specified offset in the specified block string and return it in the numbered zmm

128 L<Nasm::X86::BlockString::getBlockLength|/Nasm::X86::BlockString::getBlockLength> - Get the block length of the numbered zmm and return it in a variable

129 L<Nasm::X86::BlockString::getCharacter|/Nasm::X86::BlockString::getCharacter> - Get a character from a block string

130 L<Nasm::X86::BlockString::getNextAndPrevBlockOffsetFromZmm|/Nasm::X86::BlockString::getNextAndPrevBlockOffsetFromZmm> - Get the offsets of the next and previous blocks as variables from the specified zmm

131 L<Nasm::X86::BlockString::insertChar|/Nasm::X86::BlockString::insertChar> - Insert a character into a block string

132 L<Nasm::X86::BlockString::len|/Nasm::X86::BlockString::len> - Find the length of a block string

133 L<Nasm::X86::BlockString::putBlock|/Nasm::X86::BlockString::putBlock> - Write the numbered zmm to the block at the specified offset in the specified byte string

134 L<Nasm::X86::BlockString::putNextandPrevBlockOffsetIntoZmm|/Nasm::X86::BlockString::putNextandPrevBlockOffsetIntoZmm> - Save next and prev offsets into a zmm representing a block

135 L<Nasm::X86::BlockString::setBlockLengthInZmm|/Nasm::X86::BlockString::setBlockLengthInZmm> - Set the block length of the numbered zmm to the specified length

136 L<Nasm::X86::ByteString::allocate|/Nasm::X86::ByteString::allocate> - Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi

137 L<Nasm::X86::ByteString::allocBlock|/Nasm::X86::ByteString::allocBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

138 L<Nasm::X86::ByteString::allocZmmBlock|/Nasm::X86::ByteString::allocZmmBlock> - Allocate a block to hold a zmm register in the specified byte string and return the offset of the block in a variable

139 L<Nasm::X86::ByteString::append|/Nasm::X86::ByteString::append> - Append one byte string to another

140 L<Nasm::X86::ByteString::blockSize|/Nasm::X86::ByteString::blockSize> - Size of a block

141 L<Nasm::X86::ByteString::chain|/Nasm::X86::ByteString::chain> - Return a variable with the end point of a chain of double words in the byte string starting at the specified variable.

142 L<Nasm::X86::ByteString::char|/Nasm::X86::ByteString::char> - Append a character expressed as a decimal number to the byte string addressed by rax

143 L<Nasm::X86::ByteString::clear|/Nasm::X86::ByteString::clear> - Clear the byte string addressed by rax

144 L<Nasm::X86::ByteString::CreateBlockArray|/Nasm::X86::ByteString::CreateBlockArray> - Create a block array in a byte string

145 L<Nasm::X86::ByteString::CreateBlockMultiWayTree|/Nasm::X86::ByteString::CreateBlockMultiWayTree> - Create a block multi way tree in a byte string

146 L<Nasm::X86::ByteString::CreateBlockString|/Nasm::X86::ByteString::CreateBlockString> - Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the byte string addressed by rax and return its descriptor

147 L<Nasm::X86::ByteString::dump|/Nasm::X86::ByteString::dump> - Dump details of a byte string

148 L<Nasm::X86::ByteString::firstFreeBlock|/Nasm::X86::ByteString::firstFreeBlock> - Create and load a variable with the first free block on the free block chain or zero if no such block in the given byte string

149 L<Nasm::X86::ByteString::freeBlock|/Nasm::X86::ByteString::freeBlock> - Free a block in a byte string by placing it on the free chain

150 L<Nasm::X86::ByteString::getBlock|/Nasm::X86::ByteString::getBlock> - Get the block with the specified offset in the specified block string and return it in the numbered zmm

151 L<Nasm::X86::ByteString::length|/Nasm::X86::ByteString::length> - Get the length of a byte string

152 L<Nasm::X86::ByteString::m|/Nasm::X86::ByteString::m> - Append the content with length rdi addressed by rsi to the byte string addressed by rax

153 L<Nasm::X86::ByteString::makeReadOnly|/Nasm::X86::ByteString::makeReadOnly> - Make a byte string read only

154 L<Nasm::X86::ByteString::makeWriteable|/Nasm::X86::ByteString::makeWriteable> - Make a byte string writable

155 L<Nasm::X86::ByteString::nl|/Nasm::X86::ByteString::nl> - Append a new line to the byte string addressed by rax

156 L<Nasm::X86::ByteString::out|/Nasm::X86::ByteString::out> - Print the specified byte string addressed by rax on sysout

157 L<Nasm::X86::ByteString::putBlock|/Nasm::X86::ByteString::putBlock> - Write the numbered zmm to the block at the specified offset in the specified byte string

158 L<Nasm::X86::ByteString::putChain|/Nasm::X86::ByteString::putChain> - Write the double word in the specified variable to the double word location at the the specified offset in the specified byte string.

159 L<Nasm::X86::ByteString::q|/Nasm::X86::ByteString::q> - Append a constant string to the byte string

160 L<Nasm::X86::ByteString::ql|/Nasm::X86::ByteString::ql> - Append a quoted string containing new line characters to the byte string addressed by rax

161 L<Nasm::X86::ByteString::read|/Nasm::X86::ByteString::read> - Read the named file (terminated with a zero byte) and place it into the named byte string.

162 L<Nasm::X86::ByteString::setFirstFreeBlock|/Nasm::X86::ByteString::setFirstFreeBlock> - Set the first free block field from a variable

163 L<Nasm::X86::ByteString::updateSpace|/Nasm::X86::ByteString::updateSpace> - Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi

164 L<Nasm::X86::ByteString::write|/Nasm::X86::ByteString::write> - Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file

165 L<Nasm::X86::ByteString::z|/Nasm::X86::ByteString::z> - Append a trailing zero to the byte string addressed by rax

166 L<Nasm::X86::LocalData::allocate8|/Nasm::X86::LocalData::allocate8> - Add some 8 byte local variables and return an array of variable definitions

167 L<Nasm::X86::LocalData::free|/Nasm::X86::LocalData::free> - Free a local data area on the stack

168 L<Nasm::X86::LocalData::start|/Nasm::X86::LocalData::start> - Start a local data area on the stack

169 L<Nasm::X86::LocalData::variable|/Nasm::X86::LocalData::variable> - Add a local variable

170 L<Nasm::X86::LocalVariable::stack|/Nasm::X86::LocalVariable::stack> - Address a local variable on the stack

171 L<Nasm::X86::Scope::contains|/Nasm::X86::Scope::contains> - Check that the named parent scope contains the specified child scope.

172 L<Nasm::X86::Scope::currentlyVisible|/Nasm::X86::Scope::currentlyVisible> - Check that the named parent scope is currently visible

173 L<Nasm::X86::Structure::field|/Nasm::X86::Structure::field> - Add a field of the specified length with an optional comment

174 L<Nasm::X86::StructureField::addr|/Nasm::X86::StructureField::addr> - Address a field in a structure by either the default register or the named register

175 L<Nasm::X86::Sub::call|/Nasm::X86::Sub::call> - Call a sub passing it some parameters

176 L<Nasm::X86::Variable::add|/Nasm::X86::Variable::add> - Add the right hand variable to the left hand variable and return the result as a new variable

177 L<Nasm::X86::Variable::address|/Nasm::X86::Variable::address> - Get the address of a variable with an optional offset

178 L<Nasm::X86::Variable::allocateMemory|/Nasm::X86::Variable::allocateMemory> - Allocate the specified amount of memory via mmap and return its address

179 L<Nasm::X86::Variable::and|/Nasm::X86::Variable::and> - And two variables

180 L<Nasm::X86::Variable::arithmetic|/Nasm::X86::Variable::arithmetic> - Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables

181 L<Nasm::X86::Variable::assign|/Nasm::X86::Variable::assign> - Assign to the left hand side the value of the right hand side

182 L<Nasm::X86::Variable::boolean|/Nasm::X86::Variable::boolean> - Combine the left hand variable with the right hand variable via a boolean operator

183 L<Nasm::X86::Variable::clearMaskBit|/Nasm::X86::Variable::clearMaskBit> - Clear a bit in the specified mask register retaining the other bits

184 L<Nasm::X86::Variable::clearMemory|/Nasm::X86::Variable::clearMemory> - Clear the memory described in this variable

185 L<Nasm::X86::Variable::clone|/Nasm::X86::Variable::clone> - Clone a variable to create a new variable

186 L<Nasm::X86::Variable::copy|/Nasm::X86::Variable::copy> - Copy one variable into another

187 L<Nasm::X86::Variable::copyAddress|/Nasm::X86::Variable::copyAddress> - Copy a reference to a variable

188 L<Nasm::X86::Variable::copyMemory|/Nasm::X86::Variable::copyMemory> - Copy from one block of memory to another

189 L<Nasm::X86::Variable::debug|/Nasm::X86::Variable::debug> - Dump the value of a variable on stdout with an indication of where the dump came from

190 L<Nasm::X86::Variable::dec|/Nasm::X86::Variable::dec> - Decrement a variable

191 L<Nasm::X86::Variable::divide|/Nasm::X86::Variable::divide> - Divide the left hand variable by the right hand variable and return the result as a new variable

192 L<Nasm::X86::Variable::division|/Nasm::X86::Variable::division> - Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side

193 L<Nasm::X86::Variable::dump|/Nasm::X86::Variable::dump> - Dump the value of a variable to the specified channel adding an optional title and new line if requested

194 L<Nasm::X86::Variable::eq|/Nasm::X86::Variable::eq> - Check whether the left hand variable is equal to the right hand variable

195 L<Nasm::X86::Variable::equals|/Nasm::X86::Variable::equals> - Equals operator

196 L<Nasm::X86::Variable::err|/Nasm::X86::Variable::err> - Dump the value of a variable on stderr

197 L<Nasm::X86::Variable::errNL|/Nasm::X86::Variable::errNL> - Dump the value of a variable on stderr and append a new line

198 L<Nasm::X86::Variable::for|/Nasm::X86::Variable::for> - Iterate the body limit times.

199 L<Nasm::X86::Variable::freeMemory|/Nasm::X86::Variable::freeMemory> - Free the memory addressed by this variable for the specified length

200 L<Nasm::X86::Variable::ge|/Nasm::X86::Variable::ge> - Check whether the left hand variable is greater than or equal to the right hand variable

201 L<Nasm::X86::Variable::getBFromZmm|/Nasm::X86::Variable::getBFromZmm> - Get the byte from the numbered zmm register and put it in a variable

202 L<Nasm::X86::Variable::getConst|/Nasm::X86::Variable::getConst> - Load the variable from a constant in effect setting a variable to a specified value

203 L<Nasm::X86::Variable::getDFromZmm|/Nasm::X86::Variable::getDFromZmm> - Get the double word from the numbered zmm register and put it in a variable

204 L<Nasm::X86::Variable::getQFromZmm|/Nasm::X86::Variable::getQFromZmm> - Get the quad word from the numbered zmm register and put it in a variable

205 L<Nasm::X86::Variable::getReg|/Nasm::X86::Variable::getReg> - Load the variable from the named registers

206 L<Nasm::X86::Variable::getWFromZmm|/Nasm::X86::Variable::getWFromZmm> - Get the word from the numbered zmm register and put it in a variable

207 L<Nasm::X86::Variable::gt|/Nasm::X86::Variable::gt> - Check whether the left hand variable is greater than the right hand variable

208 L<Nasm::X86::Variable::inc|/Nasm::X86::Variable::inc> - Increment a variable

209 L<Nasm::X86::Variable::incDec|/Nasm::X86::Variable::incDec> - Increment or decrement a variable

210 L<Nasm::X86::Variable::isRef|/Nasm::X86::Variable::isRef> - Check whether the specified  variable is a reference to another variable

211 L<Nasm::X86::Variable::le|/Nasm::X86::Variable::le> - Check whether the left hand variable is less than or equal to the right hand variable

212 L<Nasm::X86::Variable::loadZmm|/Nasm::X86::Variable::loadZmm> - Load bytes from the memory addressed by the specified source variable into the numbered zmm register.

213 L<Nasm::X86::Variable::lt|/Nasm::X86::Variable::lt> - Check whether the left hand variable is less than the right hand variable

214 L<Nasm::X86::Variable::max|/Nasm::X86::Variable::max> - Maximum of two variables

215 L<Nasm::X86::Variable::min|/Nasm::X86::Variable::min> - Minimum of two variables

216 L<Nasm::X86::Variable::minusAssign|/Nasm::X86::Variable::minusAssign> - Implement minus and assign

217 L<Nasm::X86::Variable::mod|/Nasm::X86::Variable::mod> - Divide the left hand variable by the right hand variable and return the remainder as a new variable

218 L<Nasm::X86::Variable::ne|/Nasm::X86::Variable::ne> - Check whether the left hand variable is not equal to the right hand variable

219 L<Nasm::X86::Variable::or|/Nasm::X86::Variable::or> - Or two variables

220 L<Nasm::X86::Variable::out|/Nasm::X86::Variable::out> - Dump the value of a variable on stdout

221 L<Nasm::X86::Variable::outNL|/Nasm::X86::Variable::outNL> - Dump the value of a variable on stdout and append a new line

222 L<Nasm::X86::Variable::plusAssign|/Nasm::X86::Variable::plusAssign> - Implement plus and assign

223 L<Nasm::X86::Variable::pop|/Nasm::X86::Variable::pop> - Pop a variable from the stack

224 L<Nasm::X86::Variable::printErrMemoryInHexNL|/Nasm::X86::Variable::printErrMemoryInHexNL> - Write the memory addressed by a variable to stderr

225 L<Nasm::X86::Variable::printMemoryInHexNL|/Nasm::X86::Variable::printMemoryInHexNL> - Write the memory addressed by a variable to stdout or stderr

226 L<Nasm::X86::Variable::printOutMemoryInHexNL|/Nasm::X86::Variable::printOutMemoryInHexNL> - Write the memory addressed by a variable to stdout

227 L<Nasm::X86::Variable::push|/Nasm::X86::Variable::push> - Push a variable onto the stack

228 L<Nasm::X86::Variable::putBIntoXmm|/Nasm::X86::Variable::putBIntoXmm> - Place the value of the content variable at the byte in the numbered xmm register

229 L<Nasm::X86::Variable::putBIntoZmm|/Nasm::X86::Variable::putBIntoZmm> - Place the value of the content variable at the byte in the numbered zmm register

230 L<Nasm::X86::Variable::putBwdqIntoMm|/Nasm::X86::Variable::putBwdqIntoMm> - Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register

231 L<Nasm::X86::Variable::putDIntoXmm|/Nasm::X86::Variable::putDIntoXmm> - Place the value of the content variable at the double word in the numbered xmm register

232 L<Nasm::X86::Variable::putDIntoZmm|/Nasm::X86::Variable::putDIntoZmm> - Place the value of the content variable at the double word in the numbered zmm register

233 L<Nasm::X86::Variable::putQIntoXmm|/Nasm::X86::Variable::putQIntoXmm> - Place the value of the content variable at the quad word in the numbered xmm register

234 L<Nasm::X86::Variable::putQIntoZmm|/Nasm::X86::Variable::putQIntoZmm> - Place the value of the content variable at the quad word in the numbered zmm register

235 L<Nasm::X86::Variable::putWIntoXmm|/Nasm::X86::Variable::putWIntoXmm> - Place the value of the content variable at the word in the numbered xmm register

236 L<Nasm::X86::Variable::putWIntoZmm|/Nasm::X86::Variable::putWIntoZmm> - Place the value of the content variable at the word in the numbered zmm register

237 L<Nasm::X86::Variable::saveZmm2222|/Nasm::X86::Variable::saveZmm2222> - Save bytes into the memory addressed by the target variable from the numbered zmm register.

238 L<Nasm::X86::Variable::setMask|/Nasm::X86::Variable::setMask> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

239 L<Nasm::X86::Variable::setMaskBit|/Nasm::X86::Variable::setMaskBit> - Set a bit in the specified mask register retaining the other bits

240 L<Nasm::X86::Variable::setMaskFirst|/Nasm::X86::Variable::setMaskFirst> - Set the first bits in the specified mask register

241 L<Nasm::X86::Variable::setReg|/Nasm::X86::Variable::setReg> - Set the named registers from the content of the variable

242 L<Nasm::X86::Variable::setZmm|/Nasm::X86::Variable::setZmm> - Load bytes from the memory addressed by specified source variable into the numbered zmm register at the offset in the specified offset moving the number of bytes in the specified variable

243 L<Nasm::X86::Variable::str|/Nasm::X86::Variable::str> - The name of the variable

244 L<Nasm::X86::Variable::sub|/Nasm::X86::Variable::sub> - Subtract the right hand variable from the left hand variable and return the result as a new variable

245 L<Nasm::X86::Variable::times|/Nasm::X86::Variable::times> - Multiply the left hand variable by the right hand variable and return the result as a new variable

246 L<Nasm::X86::Variable::zBroadCastD|/Nasm::X86::Variable::zBroadCastD> - Broadcast a double word in a variable into the numbered zmm.

247 L<OpenRead|/OpenRead> - Open a file, whose name is addressed by rax, for read and return the file descriptor in rax

248 L<OpenWrite|/OpenWrite> - Create the file named by the terminated string addressed by rax for write

249 L<PeekR|/PeekR> - Peek at register on stack

250 L<PopEax|/PopEax> - We cannot pop a double word from the stack in 64 bit long mode using pop so we improvise

251 L<PopR|/PopR> - Pop registers from the stack

252 L<PopRR|/PopRR> - Pop registers from the stack without tracking

253 L<PrintErrMemory|/PrintErrMemory> - Print the memory addressed by rax for a length of rdi on stderr

254 L<PrintErrMemoryInHex|/PrintErrMemoryInHex> - Dump memory from the address in rax for the length in rdi on stderr

255 L<PrintErrMemoryInHexNL|/PrintErrMemoryInHexNL> - Dump memory from the address in rax for the length in rdi and then print a new line

256 L<PrintErrMemoryNL|/PrintErrMemoryNL> - Print the memory addressed by rax for a length of rdi followed by a new line on stderr

257 L<PrintErrNL|/PrintErrNL> - Print a new line to stderr

258 L<PrintErrRaxInHex|/PrintErrRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to stderr

259 L<PrintErrRegisterInHex|/PrintErrRegisterInHex> - Print the named registers as hex strings on stderr

260 L<PrintErrString|/PrintErrString> - Print a constant string to stderr.

261 L<PrintErrStringNL|/PrintErrStringNL> - Print a constant string followed by a new line to stderr

262 L<PrintErrZF|/PrintErrZF> - Print the zero flag without disturbing it on stderr

263 L<PrintMemory|/PrintMemory> - Print the memory addressed by rax for a length of rdi on the specified channel

264 L<PrintMemoryInHex|/PrintMemoryInHex> - Dump memory from the address in rax for the length in rdi on the specified channel.

265 L<PrintNL|/PrintNL> - Print a new line to stdout  or stderr

266 L<PrintOutMemory|/PrintOutMemory> - Print the memory addressed by rax for a length of rdi on stdout

267 L<PrintOutMemoryInHex|/PrintOutMemoryInHex> - Dump memory from the address in rax for the length in rdi on stdout

268 L<PrintOutMemoryInHexNL|/PrintOutMemoryInHexNL> - Dump memory from the address in rax for the length in rdi and then print a new line

269 L<PrintOutMemoryNL|/PrintOutMemoryNL> - Print the memory addressed by rax for a length of rdi followed by a new line on stdout

270 L<PrintOutNL|/PrintOutNL> - Print a new line to stderr

271 L<PrintOutRaxInHex|/PrintOutRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to stderr

272 L<PrintOutRaxInReverseInHex|/PrintOutRaxInReverseInHex> - Write the content of register rax to stderr in hexadecimal in little endian notation

273 L<PrintOutRegisterInHex|/PrintOutRegisterInHex> - Print the named registers as hex strings on stdout

274 L<PrintOutRegistersInHex|/PrintOutRegistersInHex> - Print the general purpose registers in hex

275 L<PrintOutRflagsInHex|/PrintOutRflagsInHex> - Print the flags register in hex

276 L<PrintOutRipInHex|/PrintOutRipInHex> - Print the instruction pointer in hex

277 L<PrintOutString|/PrintOutString> - Print a constant string to stdout.

278 L<PrintOutStringNL|/PrintOutStringNL> - Print a constant string followed by a new line to stdout

279 L<PrintOutZF|/PrintOutZF> - Print the zero flag without disturbing it on stdout

280 L<PrintRaxInHex|/PrintRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to the specified channel

281 L<PrintRegisterInHex|/PrintRegisterInHex> - Print the named registers as hex strings

282 L<PrintString|/PrintString> - Print a constant string to the specified channel

283 L<PushR|/PushR> - Push registers onto the stack

284 L<PushRR|/PushRR> - Push registers onto the stack without tracking

285 L<Rb|/Rb> - Layout bytes in the data segment and return their label

286 L<Rbwdq|/Rbwdq> - Layout data

287 L<RComment|/RComment> - Insert a comment into the read only data segment

288 L<Rd|/Rd> - Layout double words in the data segment and return their label

289 L<ReadFile|/ReadFile> - Read a file whose name is addressed by rax into memory.

290 L<ReadTimeStampCounter|/ReadTimeStampCounter> - Read the time stamp counter and return the time in nanoseconds in rax

291 L<RegisterSize|/RegisterSize> - Return the size of a register

292 L<removeNonAsciiChars|/removeNonAsciiChars> - Return a copy of the specified string with all the non ascii characters removed

293 L<ReorderSyscallRegisters|/ReorderSyscallRegisters> - Map the list of registers provided to the 64 bit system call sequence

294 L<RestoreFirstFour|/RestoreFirstFour> - Restore the first 4 parameter registers

295 L<RestoreFirstFourExceptRax|/RestoreFirstFourExceptRax> - Restore the first 4 parameter registers except rax so it can return its value

296 L<RestoreFirstFourExceptRaxAndRdi|/RestoreFirstFourExceptRaxAndRdi> - Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values

297 L<RestoreFirstSeven|/RestoreFirstSeven> - Restore the first 7 parameter registers

298 L<RestoreFirstSevenExceptRax|/RestoreFirstSevenExceptRax> - Restore the first 7 parameter registers except rax which is being used to return the result

299 L<RestoreFirstSevenExceptRaxAndRdi|/RestoreFirstSevenExceptRaxAndRdi> - Restore the first 7 parameter registers except rax and rdi which are being used to return the results

300 L<Rq|/Rq> - Layout quad words in the data segment and return their label

301 L<Rs|/Rs> - Layout bytes in read only memory and return their label

302 L<Rw|/Rw> - Layout words in the data segment and return their label

303 L<SaveFirstFour|/SaveFirstFour> - Save the first 4 parameter registers making any parameter registers read only

304 L<SaveFirstSeven|/SaveFirstSeven> - Save the first 7 parameter registers

305 L<Scope|/Scope> - Create and stack a new scope and continue with it as the current scope

306 L<ScopeEnd|/ScopeEnd> - End the current scope and continue with the containing parent scope

307 L<SetLabel|/SetLabel> - Set a label in the code section

308 L<SetLengthOfShortString|/SetLengthOfShortString> - Set the length of the short string held in the numbered zmm register into the specified register

309 L<SetMaskRegister|/SetMaskRegister> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

310 L<SetZF|/SetZF> - Set the zero flag

311 L<Start|/Start> - Initialize the assembler

312 L<StatSize|/StatSize> - Stat a file whose name is addressed by rax to get its size in rax

313 L<Structure|/Structure> - Create a structure addressed by a register

314 L<Subroutine|/Subroutine> - Create a subroutine that can be called in assembler code

315 L<Then|/Then> - Then body for an If statement

316 L<totalBytesAssembled|/totalBytesAssembled> - Total size in bytes of all files assembled during testing

317 L<Trace|/Trace> - Add tracing code

318 L<unlinkFile|/unlinkFile> - Unlink the named file

319 L<UnReorderSyscallRegisters|/UnReorderSyscallRegisters> - Recover the initial values in registers that were reordered

320 L<Variable|/Variable> - Create a new variable with the specified size and name initialized via an expression

321 L<Vb|/Vb> - Define a byte variable

322 L<Vd|/Vd> - Define a double word variable

323 L<Vq|/Vq> - Define a quad variable

324 L<Vr|/Vr> - Define a reference variable

325 L<Vw|/Vw> - Define a word variable

326 L<Vx|/Vx> - Define an xmm variable

327 L<VxyzInit|/VxyzInit> - Initialize an xyz register from general purpose registers

328 L<Vy|/Vy> - Define an ymm variable

329 L<Vz|/Vz> - Define an zmm variable

330 L<WaitPid|/WaitPid> - Wait for the pid in rax to complete

331 L<xmm|/xmm> - Add xmm to the front of a list of register expressions

332 L<ymm|/ymm> - Add ymm to the front of a list of register expressions

333 L<zmm|/zmm> - Add zmm to the front of a list of register expressions

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
   {plan tests => 110;
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

  is_deeply Assemble, <<END;                                                    # Channel  is now used for tracing
   rax: 0000 0000 0000 0004
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

#latest:;
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

if (1) {                                                                        # Print rdi in hex into a byte string #TGetPidInHex
  GetPidInHex;
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: 00);
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

#latest:;
if (1) {                                                                        #TAllocateMemory #TPrintOutMemoryInHexNL #TCopyMemory
  my $N = 256;
  my $s = Rb 0..$N-1;
  AllocateMemory(Cq(size, $N), my $a = Vq(address));
  CopyMemory(Vq(source, $s), Vq(size, $N), target => $a);

  AllocateMemory(Cq(size, $N), my $b = Vq(address));
  CopyMemory(source => $a, target => $b, Cq(size, $N));

  $b->setReg(rax);
  Mov rdi, $N;
  PrintOutMemoryInHexNL;

  ok Assemble(debug=>0, eq => <<END);
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
#   0 eq    1 lt    2 le    4 ne    5 ge    6 gt   comparisons
 }

if (1) {                                                                        #TStringLength
  StringLength(Vq(string, Rs("abcd")))->outNL;
  Assemble(debug => 0, eq => <<END);
size: 0000 0000 0000 0004
END
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
      $@ and confess $@;
     }
   };
  &$cmp(1,1);
  &$cmp(1,2);
  &$cmp(3,2);
  Assemble(debug => 0, eq => <<END);
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

#latest:;
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

  If ($a == 3, sub{PrintOutStringNL "a == 3"});
  ++$a; $a->outNL;
  --$a; $a->outNL;

  ok Assemble(debug => 0, eq => <<END);
a: 0000 0000 0000 0003
b: 0000 0000 0000 0002
(a add b): 0000 0000 0000 0005
((a add b) sub a): 0000 0000 0000 0002
(((a add b) sub a) eq b): 0000 0000 0000 0001
(((a add b) sub a) ne b): 0000 0000 0000 0000
(a times b): 0000 0000 0000 0006
((a times b) / b): 0000 0000 0000 0003
(a % b): 0000 0000 0000 0001
a == 3
a: 0000 0000 0000 0004
a: 0000 0000 0000 0003
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::for
  Vq(limit,10)->for(sub
   {my ($i, $start, $next, $end) = @_;
    $i->outNL;
   });

  is_deeply Assemble, <<END;
index: 0000 0000 0000 0000
index: 0000 0000 0000 0001
index: 0000 0000 0000 0002
index: 0000 0000 0000 0003
index: 0000 0000 0000 0004
index: 0000 0000 0000 0005
index: 0000 0000 0000 0006
index: 0000 0000 0000 0007
index: 0000 0000 0000 0008
index: 0000 0000 0000 0009
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

if (1) {                                                                        #TgetDFromZmm #TNasm::X86::Variable::putDIntoZmm
  my $s = Rb(0..8);
  my $c = Vq("Content",   "[$s]");
     $c->putBIntoZmm(0,  4);
     $c->putWIntoZmm(0,  6);
     $c->putDIntoZmm(0, 10);
     $c->putQIntoZmm(0, 16);
  PrintOutRegisterInHex zmm0;
  getBFromZmm(0, 12)->outNL;
  getWFromZmm(0, 12)->outNL;
  getDFromZmm(0, 12)->outNL;
  getQFromZmm(0, 12)->outNL;

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
  my $a = CreateByteString; $a->dump;
  my $b1 = $a->allocBlock;  $a->dump;
  my $b2 = $a->allocBlock;  $a->dump;
  $a->freeBlock($b2);       $a->dump;
  $a->freeBlock($b1);       $a->dump;

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

#latest:
if (1) {
  my $a = Rb((reverse 0..16)x16);
  my $b = Rb((        0..16)x16);
  KeepFree rax; Mov rax, $a;  Vmovdqu8 zmm0, "[rax]";
  KeepFree rax; Mov rax, $b;  Vmovdqu8 zmm1, "[rax]";
  Vpcmpeqb k0, zmm0, zmm1;

  KeepFree rax; Kmovq rax, k0; Popcnt rax, rax;
  PrintOutRegisterInHex zmm0, zmm1, k0, rax;

  ok Assemble(eq => <<END);
  zmm0: 0405 0607 0809 0A0B   0C0D 0E0F 1000 0102   0304 0506 0708 090A   0B0C 0D0E 0F10 0001   0203 0405 0607 0809   0A0B 0C0D 0E0F 1000   0102 0304 0506 0708   090A 0B0C 0D0E 0F10
  zmm1: 0C0B 0A09 0807 0605   0403 0201 0010 0F0E   0D0C 0B0A 0908 0706   0504 0302 0100 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0010   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
    k0: 0800 0400 0200 0100
   rax: 0000 0000 0000 0004
END
 }

#latest:
if (1) {                                                                        # Insert key for BlockMultiWayTree
# 0000000001111111 A Length    = k7
# .........1111000 B Greater   = k6
# 0000000001111000 C =  A&B    = k5
# 0000000000000111 D = !C&A    = k4
# 0000000011110000 E Shift left 1 C = K5
# 0000000011110111 F Want expand mask =   E&D =  k5&K4 ->k5
# 0000000000001000 G Want broadcast mask !F&A =  K5!&k7->k6

  Mov eax, 0x007f; Kmovw k7, eax;
  Mov esi, 0x0F78; Kmovw k6, esi;
  Kandw    k5, k6, k7;
  Kandnw   k4, k5, k7;
  Kshiftlw k5, k5, 1;
  Korw     k5, k4, k5;
  Kandnw   k6, k5, k7;
  PrintOutRegisterInHex k7, k5, k6;

  ok Assemble(eq => <<END);
    k7: 0000 0000 0000 007F
    k5: 0000 0000 0000 00F7
    k6: 0000 0000 0000 0008
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::ByteString::chain
  my $format = Rd(map{4*$_+24} 0..64);

  my $b = CreateByteString;
  my $a = $b->allocBlock;
  Vmovdqu8 zmm31, "[$format]";
  $b->putBlock($b->bs, $a, 31);
  my $r = $b->chain($b->bs, Vq(start, 0x18), 4);       $r->outNL("chain1: ");
  my $s = $b->chain($b->bs, $r, 4);                    $s->outNL("chain2: ");
  my $t = $b->chain($b->bs, $s, 4);                    $t->outNL("chain3: ");
  my $A = $b->chain($b->bs, Vq(start, 0x18), 4, 4, 4); $A->outNL("chain4: ");           # Get a long chain

  $b->putChain($b->bs, Vq(start, 0x18), Vq(end, 0xff), 4, 4, 4);                # Put at the end of a long chain

  $b->dump;

  my $sub = Subroutine
   {my ($p) = @_;                                                               # Parameters
    If ($$p{c} == -1,
      sub {PrintOutStringNL "C is minus one"},
      sub {PrintOutStringNL "C is NOT minus one"},
     );
    If ($$p{d} == -1,
      sub {PrintOutStringNL "D is minus one"},
      sub {PrintOutStringNL "D is NOT minus one"},
     );

    my $C = $$p{c}->clone;
    $C->outNL;

    $$p{e} += 1;
    $$p{e}->outNL('E: ');

    $$p{f}->outNL('F1: ');
    $$p{f}++;
    $$p{f}->outNL('F2: ');
   } name=> 'aaa', in => {c => 3}, io => {d => 3, e => 3, f => 3};

  my $c = Cq(c, -1);
  my $d = Cq(d, -1);
  my $e = Vq(e,  1);
  my $f = Vq(f,  2);

  $sub->call($c, $d, $e, $f);
  $f->outNL('F3: ');

  ok Assemble(debug => 0, eq => <<END);
chain1: 0000 0000 0000 001C
chain2: 0000 0000 0000 0020
chain3: 0000 0000 0000 0024
chain4: 0000 0000 0000 0024
Byte String
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0058
0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00001800 0000 1C00 00002000 0000 FF00 00002800 0000 2C00 00003000 0000 3400 00003800 0000 3C00 0000
0040: 4000 0000 4400 00004800 0000 4C00 00005000 0000 5400 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
C is minus one
D is minus one
Clone of c: FFFF FFFF FFFF FFFF
E: 0000 0000 0000 0002
F1: 0000 0000 0000 0002
F2: 0000 0000 0000 0003
F3: 0000 0000 0000 0003
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::ByteString::CreateBlockMultiWayTree #TLoadConstantIntoMaskRegister #TPopEax
  Mov r14, 0;
  Kmovq k0, r14;
  KeepFree r14;
  Ktestq k0, k0;
  IfZ {PrintOutStringNL "0 & 0 == 0"};
  PrintOutZF;

  LoadConstantIntoMaskRegister k1, 1;
  Ktestq k1, k1;
  IfNz {PrintOutStringNL "1 & 1 != 0"};
  PrintOutZF;

  LoadConstantIntoMaskRegister k2, eval "0b".(('1'x4).('0'x4))x2;

  PrintOutRegisterInHex k0, k1, k2;

  Mov  r15, 0x89abcdef;
  Mov  r14, 0x01234567;
  Shl  r14, 32;
  Or r15, r14;
  Push r15;
  Push r15;
  KeepFree r15;
  PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;

  my $a = Vq('aaaa');
  $a->pop;
  $a->push;
  $a->outNL;

  PopEax;  PrintRaxInHex($stdout, 3); PrintOutNL; KeepFree rax;

  ok Assemble(debug => 0, eq => <<END);
0 & 0 == 0
ZF=1
1 & 1 != 0
ZF=0
    k0: 0000 0000 0000 0000
    k1: 0000 0000 0000 0001
    k2: 0000 0000 0000 F0F0
89AB CDEF
aaaa: 89AB CDEF 0123 4567
0123 4567
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::BlockMultiWayTree::splitFullLeftNode
  my $Sk = Rd(17..28, 0, 0, 12,   0xFF);
  my $Sd = Rd(17..28, 0, 0, 0xDD, 0xEE);
  my $Sn = Rd(1..13,     0, 0,    0xCC);

  my $sk = Rd(1..14, 14,   0xA1);
  my $sd = Rd(1..14, 0xCC, 0xA2);
  my $sn = Rd(1..15,       0xA3);

  my $rk = Rd((0)x14, 14,   0xB1);
  my $rd = Rd((0)x14, 0xCC, 0xB2);
  my $rn = Rd((0)x15,       0xB3);

  my $b = CreateByteString;
  my $t = $b->CreateBlockMultiWayTree;

  Vmovdqu8 zmm31, "[$Sk]";
  Vmovdqu8 zmm30, "[$Sd]";
  Vmovdqu8 zmm29, "[$Sn]";

  Vmovdqu8 zmm28, "[$sk]";
  Vmovdqu8 zmm27, "[$sd]";
  Vmovdqu8 zmm26, "[$sn]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

   $t->splitFullLeftNode($b->bs);

  PrintOutRegisterInHex reverse zmm(23..31);

  ok Assemble(debug => 0, eq => <<END);
 zmm31: 0000 00FF 0000 000D   0000 0000 0000 0000   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm30: 0000 00EE 0000 00DD   0000 0000 0000 0000   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm29: 0000 00CC 0000 0000   0000 0000 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm28: 0000 00A1 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm27: 0000 00A2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm26: 0000 00A3 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm25: 0000 00B1 0000 0006   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
 zmm24: 0000 00B2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
 zmm23: 0000 00B3 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
END
 }

#latest:
if (1) {                                                                        # Concatenate at end rather than insert in middle
  my $tk = Rd(1, (0) x 13, 1, 0xC1);
  my $td = Rd(1, (0) x 14,    0xC2);
  my $tn = Rd(1, 0xAA, (0) x 13, 0xCC);

  my $lk = Rd(1..14, 14,   0xA1);
  my $ld = Rd(1..14, 0xCC, 0xA2);
  my $ln = Rd(1..15,       0xAA);

  my $rk = Rd((0)x14, 14,   0xB1);
  my $rd = Rd((0)x14, 0xCC, 0xB2);
  my $rn = Rd((0)x15,       0xBB);

  my $b = CreateByteString;
  my $t = $b->CreateBlockMultiWayTree;

  Vmovdqu8 zmm31, "[$tk]";
  Vmovdqu8 zmm30, "[$td]";
  Vmovdqu8 zmm29, "[$tn]";

  Vmovdqu8 zmm28, "[$lk]";
  Vmovdqu8 zmm27, "[$ld]";
  Vmovdqu8 zmm26, "[$ln]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

  $t->splitFullLeftNode($b->bs);

  PrintOutRegisterInHex reverse zmm(23..31);

  ok Assemble(debug => 0, eq => <<END);
 zmm31: 0000 00C1 0000 0002   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0008 0000 0001
 zmm30: 0000 00C2 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0008 0000 0001
 zmm29: 0000 00CC 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 00BB   0000 00AA 0000 0001
 zmm28: 0000 00A1 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm27: 0000 00A2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm26: 0000 00AA 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm25: 0000 00B1 0000 0006   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
 zmm24: 0000 00B2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
 zmm23: 0000 00BB 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::BlockMultiWayTree::splitFullRightNode
  my $tk = Rd(1..12, 0, 0, 12,      0xC1);
  my $td = Rd(1..12, 0, 0,  0,      0xC2);
  my $tn = Rd(1, 0xBB, 3..13, 0, 0, 0xCC);

  my $lk = Rd(17..30, 14,   0xA1);
  my $ld = Rd(17..30, 0xCC, 0xA2);
  my $ln = Rd(17..31,       0xAA);

  my $rk = Rd(17..30, 14,   0xB1);
  my $rd = Rd(17..30, 0xCC, 0xB2);
  my $rn = Rd(17..31,       0xBB);

  my $b = CreateByteString;
  my $t = $b->CreateBlockMultiWayTree;

  Vmovdqu8 zmm31, "[$tk]";
  Vmovdqu8 zmm30, "[$td]";
  Vmovdqu8 zmm29, "[$tn]";

  Vmovdqu8 zmm28, "[$lk]";
  Vmovdqu8 zmm27, "[$ld]";
  Vmovdqu8 zmm26, "[$ln]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

  $t->splitFullRightNode($b->bs);

  PrintOutRegisterInHex reverse zmm(23..31);

  ok Assemble(debug => 0, eq => <<END);
 zmm31: 0000 00C1 0000 000D   0000 0000 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0018 0000 0001
 zmm30: 0000 00C2 0000 0000   0000 0000 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0018 0000 0001
 zmm29: 0000 00CC 0000 0000   0000 000D 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 00BB   0000 00AA 0000 0001
 zmm28: 0000 00A1 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm27: 0000 00A2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm26: 0000 00AA 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm25: 0000 00B1 0000 0006   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
 zmm24: 0000 00B2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
 zmm23: 0000 00BB 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
END
 }

#latest:
if (1) {                                                                        # Insert at start rather than insert in middle
  my $tk = Rd(1..12, 0, 0, 12,      0xC1);
  my $td = Rd(1..12, 0, 0,  0,      0xC2);
  my $tn = Rd(0xBB, 2, 3..13, 0, 0, 0xCC);

  my $lk = Rd(17..30, 14,   0xA1);
  my $ld = Rd(17..30, 0xCC, 0xA2);
  my $ln = Rd(17..31,       0xAA);

  my $rk = Rd(17..30, 14,   0xB1);
  my $rd = Rd(17..30, 0xCC, 0xB2);
  my $rn = Rd(17..31,       0xBB);

  my $b = CreateByteString;
  my $t = $b->CreateBlockMultiWayTree;

  Vmovdqu8 zmm31, "[$tk]";
  Vmovdqu8 zmm30, "[$td]";
  Vmovdqu8 zmm29, "[$tn]";

  Vmovdqu8 zmm28, "[$lk]";
  Vmovdqu8 zmm27, "[$ld]";
  Vmovdqu8 zmm26, "[$ln]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

  $t->splitFullRightNode($b->bs);

  PrintOutRegisterInHex reverse zmm(23..31);

  ok Assemble(debug => 0, eq => <<END);
 zmm31: 0000 00C1 0000 000D   0000 0000 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 0018
 zmm30: 0000 00C2 0000 0000   0000 0000 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 0018
 zmm29: 0000 00CC 0000 0000   0000 000D 0000 000C   0000 000B 0000 000A   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 00BB 0000 00AA
 zmm28: 0000 00A1 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm27: 0000 00A2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm26: 0000 00AA 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm25: 0000 00B1 0000 0006   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
 zmm24: 0000 00B2 0000 00CC   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
 zmm23: 0000 00BB 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019
END
 }

#latest:
if (1) {
  my $b = CreateByteString;
  my $t = $b->CreateBlockMultiWayTree;
  my $d = Vq(data);
  my $f = Vq(found);

  Vq(count, 24)->for(sub       # 24
   {my ($index, $start, $next, $end) = @_;
    my $k = $index + 1; my $d = $k + 0x100;
    $t->insert(key => $k, data => $d);
   });

  $t->getKeysDataNode($t->first, 31, 30, 29);
  PrintOutStringNL "Root"; $t->first->outNL('First: ');
  PrintOutRegisterInHex zmm31, zmm30, zmm29;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0xd8), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0x258), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0x198), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  $t->by(sub
   {my ($iter, $end) = @_;
    $iter->key ->out('key: ');
    $iter->data->out(' data: ');
    $iter->tree->depth($iter->node, my $D = Vq(depth));

    $t->find(key => $iter->key, $d, $f);
    $f->out(' found: '); $d->out(' data: '); $D->outNL(' depth: ');
   });

  $t->find(key => Vq(key, 0xffff), $d, $f);  $f->outNL('Found: ');
  $t->find(key => Vq(key, 0xd),    $d, $f);  $f->outNL('Found: ');

  ok Assemble(debug => 0, eq => <<END);
Root
First: 0000 0000 0000 0018
 zmm31: 0000 0058 0000 0002   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0010 0000 0008
 zmm30: 0000 0098 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0110 0000 0108
 zmm29: 0000 0018 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0198   0000 0258 0000 00D8
Left
 zmm28: 0000 0118 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm27: 0000 0158 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0107   0000 0106 0000 0105   0000 0104 0000 0103   0000 0102 0000 0101
 zmm26: 0000 00D8 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Left
 zmm28: 0000 0298 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
 zmm27: 0000 02D8 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 010F   0000 010E 0000 010D   0000 010C 0000 010B   0000 010A 0000 0109
 zmm26: 0000 0258 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Left
 zmm28: 0000 01D8 0000 0008   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0018 0000 0017   0000 0016 0000 0015   0000 0014 0000 0013   0000 0012 0000 0011
 zmm27: 0000 0218 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0118 0000 0117   0000 0116 0000 0115   0000 0114 0000 0113   0000 0112 0000 0111
 zmm26: 0000 0198 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
key: 0000 0000 0000 0001 data: 0000 0000 0000 0101 found: 0000 0000 0000 0001 data: 0000 0000 0000 0101 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0002 data: 0000 0000 0000 0102 found: 0000 0000 0000 0001 data: 0000 0000 0000 0102 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0003 data: 0000 0000 0000 0103 found: 0000 0000 0000 0001 data: 0000 0000 0000 0103 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0004 data: 0000 0000 0000 0104 found: 0000 0000 0000 0001 data: 0000 0000 0000 0104 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0005 data: 0000 0000 0000 0105 found: 0000 0000 0000 0001 data: 0000 0000 0000 0105 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0006 data: 0000 0000 0000 0106 found: 0000 0000 0000 0001 data: 0000 0000 0000 0106 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0007 data: 0000 0000 0000 0107 found: 0000 0000 0000 0001 data: 0000 0000 0000 0107 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0008 data: 0000 0000 0000 0108 found: 0000 0000 0000 0001 data: 0000 0000 0000 0108 depth: 0000 0000 0000 0001
key: 0000 0000 0000 0009 data: 0000 0000 0000 0109 found: 0000 0000 0000 0001 data: 0000 0000 0000 0109 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000A data: 0000 0000 0000 010A found: 0000 0000 0000 0001 data: 0000 0000 0000 010A depth: 0000 0000 0000 0002
key: 0000 0000 0000 000B data: 0000 0000 0000 010B found: 0000 0000 0000 0001 data: 0000 0000 0000 010B depth: 0000 0000 0000 0002
key: 0000 0000 0000 000C data: 0000 0000 0000 010C found: 0000 0000 0000 0001 data: 0000 0000 0000 010C depth: 0000 0000 0000 0002
key: 0000 0000 0000 000D data: 0000 0000 0000 010D found: 0000 0000 0000 0001 data: 0000 0000 0000 010D depth: 0000 0000 0000 0002
key: 0000 0000 0000 000E data: 0000 0000 0000 010E found: 0000 0000 0000 0001 data: 0000 0000 0000 010E depth: 0000 0000 0000 0002
key: 0000 0000 0000 000F data: 0000 0000 0000 010F found: 0000 0000 0000 0001 data: 0000 0000 0000 010F depth: 0000 0000 0000 0002
key: 0000 0000 0000 0010 data: 0000 0000 0000 0110 found: 0000 0000 0000 0001 data: 0000 0000 0000 0110 depth: 0000 0000 0000 0001
key: 0000 0000 0000 0011 data: 0000 0000 0000 0111 found: 0000 0000 0000 0001 data: 0000 0000 0000 0111 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0012 data: 0000 0000 0000 0112 found: 0000 0000 0000 0001 data: 0000 0000 0000 0112 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0013 data: 0000 0000 0000 0113 found: 0000 0000 0000 0001 data: 0000 0000 0000 0113 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0014 data: 0000 0000 0000 0114 found: 0000 0000 0000 0001 data: 0000 0000 0000 0114 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0015 data: 0000 0000 0000 0115 found: 0000 0000 0000 0001 data: 0000 0000 0000 0115 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0016 data: 0000 0000 0000 0116 found: 0000 0000 0000 0001 data: 0000 0000 0000 0116 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0017 data: 0000 0000 0000 0117 found: 0000 0000 0000 0001 data: 0000 0000 0000 0117 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0018 data: 0000 0000 0000 0118 found: 0000 0000 0000 0001 data: 0000 0000 0000 0118 depth: 0000 0000 0000 0002
Found: 0000 0000 0000 0000
Found: 0000 0000 0000 0001
END
 }

#latest:
if (1) {
  for (0..7)
   {ClearRegisters "k$_";
    Cq($_,$_)->setMaskBit("k$_");
    PrintOutRegisterInHex "k$_";
   }

  ok Assemble(debug => 0, eq => <<END);
    k0: 0000 0000 0000 0001
    k1: 0000 0000 0000 0002
    k2: 0000 0000 0000 0004
    k3: 0000 0000 0000 0008
    k4: 0000 0000 0000 0010
    k5: 0000 0000 0000 0020
    k6: 0000 0000 0000 0040
    k7: 0000 0000 0000 0080
END
 }

#latest:
if (1) {
  my $b = CreateByteString;
  my $t = $b->CreateBlockMultiWayTree;
  my $d = Vq(data);
  my $f = Vq(found);

  my $N = 24;
  Vq(count, $N)->for(sub
   {my ($index, $start, $next, $end) = @_;
    if (1)
     {my $k = $index *  2 + 1;      my $d = $k + 0x100;
      $t->insert(key => $k, data => $d);
     }
    if (1)
     {my $k = $index * -2 + 2 * $N; my $d = $k + 0x100;
      $t->insert(key => $k, data => $d);
     }
   });

  $t->getKeysDataNode($t->first, 31, 30, 29);
  PrintOutStringNL "Root"; $t->first->outNL('First: ');
  PrintOutRegisterInHex zmm31, zmm30, zmm29;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0x258), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0x3d8), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0x318), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0xd8), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(Vq(offset, 0x198), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;


  $t->find(key => Vq(key, 0xffff), $d, $f);  $f->outNL('Found: ');
  $t->find(key => Vq(key, 0x1b),   $d, $f);  $f->outNL('Found: ');

  ok Assemble(debug => 0, eq => <<END);
Root
First: 0000 0000 0000 0018
 zmm31: 0000 0058 0000 0004   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0024 0000 001A   0000 000F 0000 0008
 zmm30: 0000 0098 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0124 0000 011A   0000 010F 0000 0108
 zmm29: 0000 0018 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0198   0000 00D8 0000 0318   0000 03D8 0000 0258
Left
 zmm28: 0000 0298 0000 0007   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
 zmm27: 0000 02D8 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0107   0000 0106 0000 0105   0000 0104 0000 0103   0000 0102 0000 0101
 zmm26: 0000 0258 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Left
 zmm28: 0000 0418 0000 0006   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 000E 0000 000D   0000 000C 0000 000B   0000 000A 0000 0009
 zmm27: 0000 0458 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 010E 0000 010D   0000 010C 0000 010B   0000 010A 0000 0109
 zmm26: 0000 03D8 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Left
 zmm28: 0000 0358 0000 000A   0000 0000 0000 0000   0000 0000 0000 0000   0000 0019 0000 0018   0000 0017 0000 0016   0000 0015 0000 0014   0000 0013 0000 0012   0000 0011 0000 0010
 zmm27: 0000 0398 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0119 0000 0118   0000 0117 0000 0116   0000 0115 0000 0114   0000 0113 0000 0112   0000 0111 0000 0110
 zmm26: 0000 0318 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Left
 zmm28: 0000 0118 0000 0009   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0023   0000 0022 0000 0021   0000 0020 0000 001F   0000 001E 0000 001D   0000 001C 0000 001B
 zmm27: 0000 0158 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0123   0000 0122 0000 0121   0000 0120 0000 011F   0000 011E 0000 011D   0000 011C 0000 011B
 zmm26: 0000 00D8 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Left
 zmm28: 0000 01D8 0000 000C   0000 0000 0000 0000   0000 0030 0000 002F   0000 002E 0000 002D   0000 002C 0000 002B   0000 002A 0000 0029   0000 0028 0000 0027   0000 0026 0000 0025
 zmm27: 0000 0218 0000 0018   0000 0000 0000 0000   0000 0130 0000 012F   0000 012E 0000 012D   0000 012C 0000 012B   0000 012A 0000 0129   0000 0128 0000 0127   0000 0126 0000 0125
 zmm26: 0000 0198 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Found: 0000 0000 0000 0000
Found: 0000 0000 0000 0001
END
 }

#latest:
if (1) {                                                                        #TConvertUtf8ToUtf32
  my @p = my ($out, $size, $fail) = (Vq(out), Vq(size), Vq('fail'));
  my $opens = Vq(opens);
  my $class = Vq(class);

  my $Chars = Rb(0x24, 0xc2, 0xa2, 0xc9, 0x91, 0xE2, 0x82, 0xAC, 0xF0, 0x90, 0x8D, 0x88);
  my $chars = Vq(chars, $Chars);

  GetNextUtf8CharAsUtf32 in=>$chars, @p;                                        # Dollar               UTF-8 Encoding: 0x24                UTF-32 Encoding: 0x00000024
  $out->out('out1 : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$chars+1, @p;                                      # Cents                UTF-8 Encoding: 0xC2 0xA2           UTF-32 Encoding: 0x000000a2
  $out->out('out2 : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$chars+3, @p;                                      # Alpha                UTF-8 Encoding: 0xC9 0x91           UTF-32 Encoding: 0x00000251
  $out->out('out3 : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$chars+5, @p;                                      # Euro                 UTF-8 Encoding: 0xE2 0x82 0xAC      UTF-32 Encoding: 0x000020AC
  $out->out('out4 : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$chars+8, @p;                                      # Gothic Letter Hwair  UTF-8 Encoding  0xF0 0x90 0x8D 0x88 UTF-32 Encoding: 0x00010348
  $out->out('out5 : ');     $size->outNL(' size : ');

  my $statement = qq(𝖺\n 𝑎𝑠𝑠𝑖𝑔𝑛 【【𝖻 𝐩𝐥𝐮𝐬 𝖼】】\nAAAAAAAA);                        # A sample sentence to parse

  my $s = Cq(statement, Rs($statement));
  my $l = Cq(size,  length($statement));

  AllocateMemory($l, my $address = Vq(address));                                # Allocate enough memory for a copy of the string
  CopyMemory(source => $s, target => $address, $l);

  GetNextUtf8CharAsUtf32 in=>$address, @p;
  $out->out('outA : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$address+4, @p;
  $out->out('outB : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$address+5, @p;
  $out->out('outC : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$address+30, @p;
  $out->out('outD : ');     $size->outNL(' size : ');

  GetNextUtf8CharAsUtf32 in=>$address+35, @p;
  $out->out('outE : ');     $size->outNL(' size : ');

  $address->printOutMemoryInHexNL($l);
                                                                                # Single character classifications
  Cq('newLine', 0x0A)->putBIntoZmm(0, 0);                                       #r 0x0 - open bracket  #r 0x1 - close bracket
  Cq('newLine', 0x02)->putBIntoZmm(0, 3);                                       #r 0x2 - new line,     #r 0x3 - new line acting as a semi-colon
  Cq('space',   0x20)->putBIntoZmm(0, 4);
  Cq('space',   0x05)->putBIntoZmm(0, 7);                                       #r 0x5 - space

  my sub pu32($$)                                                               # Print some utf32 characters
   {my ($n, $m) = @_;                                                           # Variable: number of characters to print, variable: address of memory
    $n->for(sub
     {my ($index, $start, $next, $end) = @_;
      my $a = $m + $index * 4;
      $a->setReg(r15);
      KeepFree r15;
      Mov r15d, "[r15]";
      KeepFree r15;
      PrintOutRegisterInHex r15;
     });
   }

  if (1)                                                                        # Classify a utf32 string
   {my $a = Dd(0x0001d5ba, 0x00000020, 0x0001d44e, 0x0000000a, 0x0001d5bb, 0x0001d429);
    my $t = Cq('test', $a);
    my $s = Cq('size', 6);

    ClassifyCharacters4 address=>$t, size=>$s;
    PrintOutStringNL "Convert some utf8 to utf32";
    pu32($s, $t);
   }

# circledLatinLetter               : assign             ⒶⒷⒸⒹⒺⒻⒼⒽⒾⒿⓀⓁⓂⓃⓄⓅⓆⓇⓈⓉⓊⓋⓌⓍⓎⓏⓐⓑⓒⓓⓔⓕⓖⓗⓘⓙⓚⓛⓜⓝⓞⓟⓠⓡⓢⓣⓤⓥⓦⓧⓨⓩ
# mathematicalBold                 : dyad lr 3          𝐀𝐁𝐂𝐃𝐄𝐅𝐆𝐇𝐈𝐉𝐊𝐋𝐌𝐍𝐎𝐏𝐐𝐑𝐒𝐓𝐔𝐕𝐖𝐗𝐘𝐙𝐚𝐛𝐜𝐝𝐞𝐟𝐠𝐡𝐢𝐣𝐤𝐥𝐦𝐧𝐨𝐩𝐪𝐫𝐬𝐭𝐮𝐯𝐰𝐱𝐲𝐳𝚨𝚩𝚪𝚫𝚬𝚭𝚮𝚯𝚰𝚱𝚲𝚳𝚴𝚵𝚶𝚷𝚸𝚺𝚻𝚼𝚽𝚾𝚿𝛀𝛂𝛃𝛄𝛅𝛆𝛇𝛈𝛉𝛊𝛋𝛌𝛍𝛎𝛏𝛐𝛑𝛒𝛔𝛕𝛖𝛗𝛘𝛙𝛚𝟊𝟋
# mathematicalBoldFraktur          :                    𝕬𝕭𝕮𝕯𝕰𝕱𝕲𝕳𝕴𝕵𝕶𝕷𝕸𝕹𝕺𝕻𝕼𝕽𝕾𝕿𝖀𝖁𝖂𝖃𝖄𝖅𝖆𝖇𝖈𝖉𝖊𝖋𝖌𝖍𝖎𝖏𝖐𝖑𝖒𝖓𝖔𝖕𝖖𝖗𝖘𝖙𝖚𝖛𝖜𝖝𝖞𝖟
# mathematicalBoldItalic           : prefix             𝑨𝑩𝑪𝑫𝑬𝑭𝑮𝑯𝑰𝑱𝑲𝑳𝑴𝑵𝑶𝑷𝑸𝑹𝑺𝑻𝑼𝑽𝑾𝑿𝒀𝒁𝒂𝒃𝒄𝒅𝒆𝒇𝒈𝒉𝒊𝒋𝒌𝒍𝒎𝒏𝒐𝒑𝒒𝒓𝒔𝒕𝒖𝒗𝒘𝒙𝒚𝒛𝜜𝜝𝜞𝜟𝜠𝜡𝜢𝜣𝜤𝜥𝜦𝜧𝜨𝜩𝜪𝜫𝜬𝜮𝜯𝜰𝜱𝜲𝜳𝜴𝜶𝜷𝜸𝜹𝜺𝜻𝜼𝜽𝜾𝜿𝝀𝝁𝝂𝝃𝝄𝝅𝝆𝝈𝝉𝝊𝝋𝝌𝝍𝝎
# mathematicalBoldScript           :                    𝓐𝓑𝓒𝓓𝓔𝓕𝓖𝓗𝓘𝓙𝓚𝓛𝓜𝓝𝓞𝓟𝓠𝓡𝓢𝓣𝓤𝓥𝓦𝓧𝓨𝓩𝓪𝓫𝓬𝓭𝓮𝓯𝓰𝓱𝓲𝓳𝓴𝓵𝓶𝓷𝓸𝓹𝓺𝓻𝓼𝓽𝓾𝓿𝔀𝔁𝔂𝔃
# mathematicalDouble-struck        :                    𝔸𝔹𝔻𝔼𝔽𝔾𝕀𝕁𝕂𝕃𝕄𝕆𝕊𝕋𝕌𝕍𝕎𝕏𝕐𝕒𝕓𝕔𝕕𝕖𝕗𝕘𝕙𝕚𝕛𝕜𝕝𝕞𝕟𝕠𝕡𝕢𝕣𝕤𝕥𝕦𝕧𝕨𝕩𝕪𝕫
# mathematicalFraktur              :                    𝔄𝔅𝔇𝔈𝔉𝔊𝔍𝔎𝔏𝔐𝔑𝔒𝔓𝔔𝔖𝔗𝔘𝔙𝔚𝔛𝔜𝔞𝔟𝔠𝔡𝔢𝔣𝔤𝔥𝔦𝔧𝔨𝔩𝔪𝔫𝔬𝔭𝔮𝔯𝔰𝔱𝔲𝔳𝔴𝔵𝔶𝔷
# mathematicalItalic               :                    𝐴𝐵𝐶𝐷𝐸𝐹𝐺𝐻𝐼𝐽𝐾𝐿𝑀𝑁𝑂𝑃𝑄𝑅𝑆𝑇𝑈𝑉𝑊𝑋𝑌𝑍𝑎𝑏𝑐𝑑𝑒𝑓𝑔𝑖𝑗𝑘𝑙𝑚𝑛𝑜𝑝𝑞𝑟𝑠𝑡𝑢𝑣𝑤𝑥𝑦𝑧𝛢𝛣𝛤𝛥𝛦𝛧𝛨𝛩𝛪𝛫𝛬𝛭𝛮𝛯𝛰𝛱𝛲𝛴𝛵𝛶𝛷𝛸𝛹𝛺𝛼𝛽𝛾𝛿𝜀𝜁𝜂𝜃𝜄𝜅𝜆𝜇𝜈𝜉𝜊𝜋𝜌𝜎𝜏𝜐𝜑𝜒𝜓𝜔
# mathematicalMonospace            :                    𝙰𝙱𝙲𝙳𝙴𝙵𝙶𝙷𝙸𝙹𝙺𝙻𝙼𝙽𝙾𝙿𝚀𝚁𝚂𝚃𝚄𝚅𝚆𝚇𝚈𝚉𝚊𝚋𝚌𝚍𝚎𝚏𝚐𝚑𝚒𝚓𝚔𝚕𝚖𝚗𝚘𝚙𝚚𝚛𝚜𝚝𝚞𝚟𝚠𝚡𝚢𝚣
# mathematicalSans-serif           : variable           𝖠𝖡𝖢𝖣𝖤𝖥𝖦𝖧𝖨𝖩𝖪𝖫𝖬𝖭𝖮𝖯𝖰𝖱𝖲𝖳𝖴𝖵𝖶𝖷𝖸𝖹𝖺𝖻𝖼𝖽𝖾𝖿𝗀𝗁𝗂𝗃𝗄𝗅𝗆𝗇𝗈𝗉𝗊𝗋𝗌𝗍𝗎𝗏𝗐𝗑𝗒𝗓
# mathematicalSans-serifBold       :                    𝗔𝗕𝗖𝗗𝗘𝗙𝗚𝗛𝗜𝗝𝗞𝗟𝗠𝗡𝗢𝗣𝗤𝗥𝗦𝗧𝗨𝗩𝗪𝗫𝗬𝗭𝗮𝗯𝗰𝗱𝗲𝗳𝗴𝗵𝗶𝗷𝗸𝗹𝗺𝗻𝗼𝗽𝗾𝗿𝘀𝘁𝘂𝘃𝘄𝘅𝘆𝘇𝝖𝝗𝝘𝝙𝝚𝝛𝝜𝝝𝝞𝝟𝝠𝝡𝝢𝝣𝝤𝝥𝝦𝝨𝝩𝝪𝝫𝝬𝝭𝝮𝝰𝝱𝝲𝝳𝝴𝝵𝝶𝝷𝝸𝝹𝝺𝝻𝝼𝝽𝝾𝝿𝞀𝞂𝞃𝞄𝞅𝞆𝞇𝞈
# mathematicalSans-serifBoldItalic : postfix            𝘼𝘽𝘾𝘿𝙀𝙁𝙂𝙃𝙄𝙅𝙆𝙇𝙈𝙉𝙊𝙋𝙌𝙍𝙎𝙏𝙐𝙑𝙒𝙓𝙔𝙕𝙖𝙗𝙘𝙙𝙚𝙛𝙜𝙝𝙞𝙟𝙠𝙡𝙢𝙣𝙤𝙥𝙦𝙧𝙨𝙩𝙪𝙫𝙬𝙭𝙮𝙯𝞐𝞑𝞒𝞓𝞔𝞕𝞖𝞗𝞘𝞙𝞚𝞛𝞜𝞝𝞞𝞟𝞠𝞢𝞣𝞤𝞥𝞦𝞧𝞨𝞪𝞫𝞬𝞭𝞮𝞯𝞰𝞱𝞲𝞳𝞴𝞵𝞶𝞷𝞸𝞹𝞺𝞼𝞽𝞾𝞿𝟀𝟁𝟂
# mathematicalSans-serifItalic     :                    𝘈𝘉𝘊𝘋𝘌𝘍𝘎𝘏𝘐𝘑𝘒𝘓𝘔𝘕𝘖𝘗𝘘𝘙𝘚𝘛𝘜𝘝𝘞𝘟𝘠𝘡𝘢𝘣𝘤𝘥𝘦𝘧𝘨𝘩𝘪𝘫𝘬𝘭𝘮𝘯𝘰𝘱𝘲𝘳𝘴𝘵𝘶𝘷𝘸𝘹𝘺𝘻
# mathematicalScript               :                    𝒜𝒞𝒟𝒢𝒥𝒦𝒩𝒪𝒫𝒬𝒮𝒯𝒰𝒱𝒲𝒳𝒴𝒵𝒶𝒷𝒸𝒹𝒻𝒽𝒾𝒿𝓀𝓁𝓂𝓃𝓅𝓆𝓇𝓈𝓉𝓊𝓋𝓌𝓍𝓎𝓏
# negativeCircledLatinLetter       :                    🅐🅑🅒🅓🅔🅕🅖🅗🅘🅙🅚🅛🅜🅝🅞🅟🅠🅡🅢🅣🅤🅥🅦🅧🅨🅩
# negativeSquaredLatinLetter       :                    🅰🅱🅲🅳🅴🅵🅶🅷🅸🅹🅺🅻🅼🅽🅾🅿🆀🆁🆂🆃🆄🆅🆆🆇🆈🆉
# squaredLatinLetter               :                    🄰🄱🄲🄳🄴🄵🄶🄷🄸🄹🄺🄻🄼🄽🄾🄿🅀🅁🅂🅃🅄🅅🅆🅇🅈🅉🆥
# semiColon                        : semicolon          ⟢

# Delete following code when the following test is completed
  if (0)                                                                        # Convert utf8 test string to utf32
   {my @p = my ($u32, $size32, $count) = (Vq(u32), Vq(size32), Vq(count));

    ClassifyCharacters4 address=>$u32, size=>$count;

    PrintOutStringNL "Convert test statement - special characters";
    pu32($count, $u32);

    Cq('variable', 0x0)     ->putDIntoZmm(0,  0);                               # Range classifications
    Cq('variable', 0x06)    ->putBIntoZmm(0,  3);                               #r 0x6 - ascii
    Cq('variable', 0x01D5A0)->putDIntoZmm(0,  4);
    Cq('variable', 0x07)    ->putBIntoZmm(0,  7);                               #r 0x7 - variable
    Cq('variable', 0x01D434)->putDIntoZmm(0,  8);
    Cq('variable', 0x08)    ->putBIntoZmm(0, 11);                               #r 0x8 - assign
    Cq('variable', 0x01D400)->putDIntoZmm(0, 12);
    Cq('variable', 0x09)    ->putBIntoZmm(0, 15);                               #r 0x9 -

    Cq('variable', 0x7f)    ->putDIntoZmm(1,  0);
    Cq('variable', 0x06)    ->putBIntoZmm(1,  3);
    Cq('variable', 0x01D5D3)->putDIntoZmm(1,  4);
    Cq('variable', 0x07)    ->putBIntoZmm(1,  7);
    Cq('variable', 0x01D467)->putDIntoZmm(1,  8);
    Cq('variable', 0x08)    ->putBIntoZmm(1, 11);
    Cq('variable', 0x01D433)->putDIntoZmm(1, 12);
    Cq('variable', 0x09)    ->putBIntoZmm(1, 15);

    ClassifyInRange address=>$u32, size=>$count;

    PrintOutStringNL "Convert test statement - ranges";
    pu32($count, $u32);

    my $bl = Rd(0x10002045, 0x12002329, 0x1400276c, 0x16002770, 0x1c0027e6, 0x24002983, 0x26002987, 0x380029fc, 0x3a003008, 0x3e003010, 0x40003014, 0x4800ff3b, 0x4900ff3d, 0x4a00ff5b, 0x4b00ff5d, 0);
    my $bh = Rd(0x11002046, 0x1300232a, 0x1500276d, 0x1b002775, 0x230027ed, 0x25002984, 0x37002998, 0x390029fd, 0x3d00300b, 0x3f003011, 0x4700301b, 0x4800ff3b, 0x4900ff3d, 0x4a00ff5b, 0x4b00ff5d, 0);

    Vmovdqu8 zmm0, "[$bl]";
    Vmovdqu8 zmm1, "[$bh]";
    ClassifyWithInRange address=>$u32, size=>$count;

    PrintOutStringNL "Convert test statement - brackets";
    pu32($count, $u32);

    MatchBrackets address=>$u32, size=>$count, $opens, $fail;

    PrintOutStringNL "Convert test statement - bracket matching";
    pu32($count, $u32);
   }

  $address->clearMemory($l);
  $address->printOutMemoryInHexNL($l);

  ok Assemble(debug => 0, eq => <<END);
out1 : 0000 0000 0000 0024 size : 0000 0000 0000 0001
out2 : 0000 0000 0000 00A2 size : 0000 0000 0000 0002
out3 : 0000 0000 0000 0251 size : 0000 0000 0000 0002
out4 : 0000 0000 0000 20AC size : 0000 0000 0000 0003
out5 : 0000 0000 0001 0348 size : 0000 0000 0000 0004
outA : 0000 0000 0001 D5BA size : 0000 0000 0000 0004
outB : 0000 0000 0000 000A size : 0000 0000 0000 0001
outC : 0000 0000 0000 0020 size : 0000 0000 0000 0001
outD : 0000 0000 0000 0020 size : 0000 0000 0000 0001
outE : 0000 0000 0000 0010 size : 0000 0000 0000 0002
F09D 96BA 0A20 F09D918E F09D 91A0 F09D91A0 F09D 9196 F09D9194 F09D 919B 20E38090 E380 90F0 9D96BB20 F09D 90A9 F09D90A5 F09D 90AE F09D90AC 20F0 9D96 BCE38091 E380 910A 4141
Convert some utf8 to utf32
   r15: 0000 0000 0001 D5BA
   r15: 0000 0000 0500 0020
   r15: 0000 0000 0001 D44E
   r15: 0000 0000 0200 000A
   r15: 0000 0000 0001 D5BB
   r15: 0000 0000 0001 D429
0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

latest:
if (1) {                                                                        # Check conversion of classification to lexical item
  Mov r10, 0x12FFFFFF; NidaLexType r10
  Mov r11, 0x13FFFFFF; NidaLexType r11
  Mov r12, 0x02FFFFFF; NidaLexType r12;
  PrintOutRegisterInHex r10, r11, r12;
  ok Assemble(debug => 1, eq => <<END);
   r10: 0000 0000 0000 0000
   r11: 0000 0000 0000 0001
   r12: 0000 0000 0000 0002
END
 }

latest:
if (1) {                                                                        # Parse some code
  my $lexDataFile = qq(unicode/lex/lex.data);                                   # As produced by unicode/lex/lex.pl
     $lexDataFile = qq(lib/Nasm/$lexDataFile) unless $develop;

  my $lex = eval readFile $lexDataFile;                                         # Load lexical definitions

  my @p = my (  $out,    $size,   $opens,      $fail) =                         # Variables
             (Vq(out), Vq(size), Vq(opens), Vq('fail'));

  my $source = Rutf8 $$lex{sampleText};                                         # String to be parsed in utf8
  my $sourceLength = StringLength Vq(string, $source);
     $sourceLength->outNL("Input  Length: ");

  ConvertUtf8ToUtf32 Vq(u8,$source), size8 => $sourceLength,                    # Convert to utf32
    (my $source32       = Vq(u32)),
    (my $sourceSize32   = Vq(size32)),
    (my $sourceLength32 = Vq(count));

  $sourceSize32   ->outNL("Output Length: ");                                   # Write output length

  PrintOutStringNL "After conversion from utf8 to utf32";
  PrintUtf32($sourceLength32, $source32);                                       # Print utf32

  Vmovdqu8 zmm0, "[".Rd(join ', ', $lex->{lexicalLow} ->@*)."]";                # Each double is [31::24] Classification, [21::0] Utf32 start character
  Vmovdqu8 zmm1, "[".Rd(join ', ', $lex->{lexicalHigh}->@*)."]";                # Each double is [31::24] Range offset,   [21::0] Utf32 end character

  ClassifyWithInRangeAndSaveOffset address=>$source32, size=>$sourceLength32;   # Alphabetic classification

  PrintOutStringNL "After classification into alphabet ranges";
  PrintUtf32($sourceLength32, $source32);                                       # Print classified utf32

  Vmovdqu8 zmm0, "[".Rd(join ', ', $lex->{bracketsLow} ->@*)."]";               # Each double is [31::24] Classification, [21::0] Utf32 start character
  Vmovdqu8 zmm1, "[".Rd(join ', ', $lex->{bracketsHigh}->@*)."]";               # Each double is [31::24] Range offset,   [21::0] Utf32 end character

  ClassifyWithInRange address=>$source32, size=>$sourceLength32;                # Bracket matching

  PrintOutStringNL "After classification into brackets";
  PrintUtf32($sourceLength32, $source32);                                       # Print classified brackets

  MatchBrackets address=>$source32, size=>$sourceLength32, $opens, $fail;       # Match brackets

  PrintOutStringNL "After bracket matching";
  PrintUtf32($sourceLength32, $source32);                                       # Print matched brackets

  ok Assemble(debug => 1, eq => <<END);
Input  Length: 0000 0000 0000 00C0
Output Length: 0000 0000 0000 0300
After conversion from utf8 to utf32
0001 D5EE 0000 0020  0001 D44E 0001 D460  0001 D460 0001 D456  0001 D454 0001 D45B  0000 0020 0000 230A  0000 0020 0000 2329  0000 0020 0000 2768  0000 0020 0001 D5EF
0001 D5FD 0000 0020  0000 2769 0000 0020  0000 232A 0000 0020  0000 0020 0001 D429  0001 D425 0001 D42E  0001 D42C 0000 0020  0000 276A 0000 0020  0001 D600 0001 D5F0
0000 0020 0000 276B  0000 0020 0000 230B  0000 0020 0000 27E2  0000 000A 0001 D5EE  0001 D5EE 0000 000A  0000 0020 0000 0020  0001 D44E 0001 D460  0001 D460 0001 D456
0001 D454 0001 D45B  0000 000A 0000 0020  0000 0020 0000 0073  0000 006F 0000 006D  0000 0065 0000 000A  0000 000A 0000 0061  0000 0073 0000 0063  0000 0069 0000 0069
0000 000A 0000 000A  0000 0074 0000 0065  0000 0078 0000 0074  0000 000A 0000 0020  0000 0020 0001 D429  0001 D425 0001 D42E  0001 D42C 0000 000A  0000 0020 0000 0020
0001 D5F0 0001 D5F0  0000 0020 0000 27E2
After classification into alphabet ranges
0700 001A 0200 0020  0600 001A 0600 002C  0600 002C 0600 0022  0600 0020 0600 0027  0200 0020 0000 230A  0200 0020 0000 2329  0200 0020 0000 2768  0200 0020 0700 001B
0700 0029 0200 0020  0000 2769 0200 0020  0000 232A 0200 0020  0200 0020 0400 0029  0400 0025 0400 002E  0400 002C 0200 0020  0000 276A 0200 0020  0700 002C 0700 001C
0200 0020 0000 276B  0200 0020 0000 230B  0200 0020 0900 0000  0300 0000 0700 001A  0700 001A 0300 0000  0200 0020 0200 0020  0600 001A 0600 002C  0600 002C 0600 0022
0600 0020 0600 0027  0300 0000 0200 0020  0200 0020 0200 0073  0200 006F 0200 006D  0200 0065 0300 0000  0300 0000 0200 0061  0200 0073 0200 0063  0200 0069 0200 0069
0300 0000 0300 0000  0200 0074 0200 0065  0200 0078 0200 0074  0300 0000 0200 0020  0200 0020 0400 0029  0400 0025 0400 002E  0400 002C 0300 0000  0200 0020 0200 0020
0700 001C 0700 001C  0200 0020 0900 0000
After classification into brackets
0700 001A 0200 0020  0600 001A 0600 002C  0600 002C 0600 0022  0600 0020 0600 0027  0200 0020 1200 230A  0200 0020 1400 2329  0200 0020 1600 2768  0200 0020 0700 001B
0700 0029 0200 0020  1700 2769 0200 0020  1500 232A 0200 0020  0200 0020 0400 0029  0400 0025 0400 002E  0400 002C 0200 0020  1800 276A 0200 0020  0700 002C 0700 001C
0200 0020 1900 276B  0200 0020 1300 230B  0200 0020 0900 0000  0300 0000 0700 001A  0700 001A 0300 0000  0200 0020 0200 0020  0600 001A 0600 002C  0600 002C 0600 0022
0600 0020 0600 0027  0300 0000 0200 0020  0200 0020 0200 0073  0200 006F 0200 006D  0200 0065 0300 0000  0300 0000 0200 0061  0200 0073 0200 0063  0200 0069 0200 0069
0300 0000 0300 0000  0200 0074 0200 0065  0200 0078 0200 0074  0300 0000 0200 0020  0200 0020 0400 0029  0400 0025 0400 002E  0400 002C 0300 0000  0200 0020 0200 0020
0700 001C 0700 001C  0200 0020 0900 0000
After bracket matching
0700 001A 0200 0020  0600 001A 0600 002C  0600 002C 0600 0022  0600 0020 0600 0027  0200 0020 1200 0023  0200 0020 1400 0014  0200 0020 1600 0012  0200 0020 0700 001B
0700 0029 0200 0020  1700 000D 0200 0020  1500 000B 0200 0020  0200 0020 0400 0029  0400 0025 0400 002E  0400 002C 0200 0020  1800 0021 0200 0020  0700 002C 0700 001C
0200 0020 1900 001C  0200 0020 1300 0009  0200 0020 0900 0000  0300 0000 0700 001A  0700 001A 0300 0000  0200 0020 0200 0020  0600 001A 0600 002C  0600 002C 0600 0022
0600 0020 0600 0027  0300 0000 0200 0020  0200 0020 0200 0073  0200 006F 0200 006D  0200 0065 0300 0000  0300 0000 0200 0061  0200 0073 0200 0063  0200 0069 0200 0069
0300 0000 0300 0000  0200 0074 0200 0065  0200 0078 0200 0074  0300 0000 0200 0020  0200 0020 0400 0029  0400 0025 0400 002E  0400 002C 0300 0000  0200 0020 0200 0020
0700 001C 0700 001C  0200 0020 0900 0000
END
 }

#latest:
if (0) {
  is_deeply Assemble(debug=>1), <<END;
END
 }

ok 1;

unlink $_ for qw(hash print2 sde-log.txt sde-ptr-check.out.txt z.txt);          # Remove incidental files

lll "Finished:", time - $start,  "bytes assembled:",   totalBytesAssembled;
