#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I. -I/home/phil/perl/cpan/AsmC/lib/
#-------------------------------------------------------------------------------
# Generate X86 assembler code using Perl as a macro pre-processor.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation
# Finished in 17.46s, bytes assembled: 3669616
package Nasm::X86;
our $VERSION = "20210813";
use warnings FATAL => qw(all);
use strict;
use Carp qw(confess cluck);
use Data::Dump qw(dump);
use Data::Table::Text qw(dumpFile confirmHasCommandLineCommand convertUtf32ToUtf8 currentDirectory evalFile fff fileMd5Sum fileSize findFiles firstNChars formatTable fpe fpf genHash lll owf pad readFile stringsAreNotEqual stringMd5Sum temporaryFile);
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
my $develop     = -e q(/home/phil/);                                            # Developing

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
  my @i0 = qw(lahf popfq pushfq rdtsc ret syscall);                             # Zero operand instructions

  my @i1 = split /\s+/, <<END;                                                  # Single operand instructions
bswap call dec idiv  inc jmp ja jae jb jbe jc jcxz je jecxz jg jge jl jle
jna jnae jnb jnbe jnc jne jng jnge jnl jnle jno jnp jns jnz jo jp jpe jpo jrcxz
js jz loop neg not seta setae setb setbe setc sete setg setge setl setle setna setnae
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
andn
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
#TEST         Keep(\$target)    if "$i" =~ m(\\Amov\\Z) and \$Registers{\$target};
#TEST         KeepSet(\$source) if "$i" =~ m(\\Amov\\Z) and \$Registers{\$source};
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

sub SetLabel(;$)                                                                # Create (if necessary) and set a label in the code section returning the label so set.
 {my ($l) = @_;                                                                 # Label
  $l //= Label;
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

my $Pi = "3.141592653589793238462";

sub Pi32 {Rd("__float32__($Pi)")}                                               #P Pi as a 32 bit float
sub Pi64 {Rq("__float32__($Pi)")}                                               #P Pi as a 64 bit float

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

sub ChooseRegisters($@)                                                         # Choose the specified numbers of registers excluding those on the specified list
 {my ($number, @registers) = @_;                                                # Number of registers needed, Registers not to choose
  my %r = (map {"r$_"} 8..15);
  delete $r{$_} for @registers;
  $number <= keys %r or confess "Not enough registers available";
  sort keys %r
 }

sub InsertZeroIntoRegisterAtPoint($$)                                           # Insert a zero into the specified register at the point indicated by another register
 {my ($point, $in) = @_;                                                        # Register with a single 1 at the insertion point, register to be inserted into.

  PushR my @s = my ($mask, $low, $high) = ChooseRegisters(3, $in, $point);      # Choose three work registers and push them
  Mov  $mask, $point;
  Sub  $mask, 1;
  Andn $high, $mask, $in;
  Shl  $high, 1;
  Mov  $low,  $in;
  And  $low,  $mask;
  Or   $low,  $high;
  Mov  $in,   $low;
  PopR @s;                                                                      # Restore stack
 }

sub InsertOneIntoRegisterAtPoint($$)                                            # Insert a one into the specified register at the point indicated by another register
 {my ($point, $in) = @_;                                                        # Register with a single 1 at the insertion point, register to be inserted into.
  InsertZeroIntoRegisterAtPoint($point, $in);                                   # Insert a zero
  Or $in, $point;                                                               # Make the zero a one
 }

sub LoadZmm($@)                                                                 # Load a numbered zmm with the specified bytes
 {my ($zmm, @bytes) = @_;                                                       # Numbered zmm, bytes
  my $b = Rb(@bytes);
  Vmovdqu8 "zmm$zmm", "[$b]";
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
   {#Keep $r;                                                                   # Register must not already be in use
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

sub Keep(@)                                                                     # Mark registers as in use so that they cannot be updated  until we explicitly free them.  Complain if the register is already in use.
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

sub LoadConstantIntoMaskRegister($$)                                            # Set a mask register equal to a constant.
 {my ($mask, $value) = @_;                                                      # Mask register to load, constant to load
  $mask =~ m(\Ak[0-7])i or confess "Not a mask register $mask";
  PushR rax;
  Mov rax, $value;                                                              # Load a general register
  Kmovq $mask, rax;                                                             # Load mask register
  PopR rax;
 }

sub LoadBitsIntoMaskRegister($$@)                                               # Load a bit string specification into a mask register
 {my ($mask, $prefix, @values) = @_;                                            # Mask register to load, prefix bits, +n 1 bits -n 0 bits
  $mask =~ m(\Ak[0-7])i or confess "Not a mask register $mask";
  my $b = "0b$prefix";
  for my $v(@values)                                                            # String representation of bit string
   {$b .= '1' x +$v if $v > 0;
    $b .= '0' x -$v if $v < 0;
    $v or confess "Count must be positive or negative bit not zero";
   }
  LoadConstantIntoMaskRegister($mask, eval $b)
 }

my $Vpcmp = genHash("NasmX86::CompareCodes",                                    # Compare codes for "Vpcmp"
  eq=>0,                                                                        # Equal
  lt=>1,                                                                        # Less than
  le=>2,                                                                        # Less than or equals
  ne=>4,                                                                        # Not equals
  ge=>5,                                                                        # Greater than or equal
  gt=>6,                                                                        # Greater than
 );

#D1 Structured Programming                                                      # Structured programming constructs

sub If($$;$)                                                                    # If
 {my ($jump, $then, $else) = @_;                                                # Jump op code of variable, then - required , else - optional
  @_ >= 2 && @_ <= 3 or confess;

  ref($jump) or $jump =~ m(\AJ(c|e|g|ge|gt|h|l|le|nc|ne|nz|z)\Z)
             or confess "Invalid jump: $jump";

  if (ref($jump))                                                               # Variable reference - non zero then then else else
   {PushR r15;
    Mov r15, $jump->address;
    Cmp r15,0;
    PopR r15;
    __SUB__->(q(Jz), $then, $else);
   }
  elsif (!$else)                                                                # No else
   {my $end = Label;
    push @text, <<END;
    $jump $end;
END
    Trace;
    &$then;
    SetLabel $end;
   }
  else                                                                          # With else
   {my $endIf     = Label;
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

sub IfEq($;$)                                                                   # If equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jne), $then, $else);                                                     # Opposite code
 }

sub IfNe($;$)                                                                   # If not equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Je), $then, $else);                                                      # Opposite code
 }

sub IfNz($;$)                                                                   # If the zero flag is not set then execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jz), $then, $else);                                                      # Opposite code
 }

sub IfZ($;$)                                                                    # If the zero flag is set then execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jnz), $then, $else);                                                     # Opposite code
 }

sub IfC($;$)                                                                    # If the carry flag is set then execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jnc), $then, $else);                                                     # Opposite code
 }

sub IfNc($;$)                                                                   # If the carry flag is not set then execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jc), $then, $else);                                                      # Opposite code
 }

sub IfLt($;$)                                                                   # If less than execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jge), $then, $else);                                                     # Opposite code
 }

sub IfLe($;$)                                                                   # If less than or equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jg), $then, $else);                                                      # Opposite code
 }

sub IfGt($;$)                                                                   # If greater than execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jle), $then, $else);                                                     # Opposite code
 }

sub IfGe($;$)                                                                   # If greater than or equal execute the then body else the else body
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jl), $then, $else);                                                      # Opposite code
 }

sub Block(&)                                                                    # Execute a block of code one with the option of jumping out of the block or restarting the block via the supplied labels.
 {my ($body) = @_;                                                              # Body
  @_ == 1 or confess;
  SetLabel(my $start = Label);
  my $end = Label;
  &$body($start, $end);                                                         # Start and end labels
  SetLabel $end;                                                                # Exit loop
 }

sub For(&$$;$)                                                                  # For - iterate the body as long as register is less than limit incrementing by increment each time
 {my ($body, $register, $limit, $increment) = @_;                               # Body, register, limit on loop, increment on each iteration
  @_ == 3 or @_ == 4 or confess;
  $increment //= 1;                                                             # Default increment
  my $next = Label;                                                             # Next iteration
  Comment "For $register $limit";
  my $start = Label;
  my $end   = Label;
  SetLabel $start;
  Cmp $register, $limit;
  Jge $end;

  &$body($start, $end, $next);                                                  # Start, end and next labels

  SetLabel $next;                                                               # Next iteration starting with after incrementing
  if ($increment == 1)
   {Inc $register;
   }
  else
   {Add $register, $increment;
   }
  Jmp $start;                                                                   # Restart loop
  SetLabel $end;                                                                # Exit loop
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
  Then
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
  my @in      = ($options{in}  // [])->@*;                                      # Input parameters
  my @out     = ($options{out} // [])->@*;                                      # Output parameters
  my @io      = ($options{io}  // [])->@*;                                      # Update u=in place parameters
  my $comment = $options{comment};                                              # Optional comment describing sub
  Comment "Subroutine " .($comment) if $comment;                                # Assemble comment

  if ($name and my $n = $subroutines{$name}) {return $n}                        # Return the label of a pre-existing copy of the code

  my %p;
  my sub check($)                                                               # Check a parameter
   {my ($name) = @_;
    $p{$name} = Variable(3, $name);                                             # Make a value parameter variable
   }

  my sub checkIo($)                                                             # Check an io parameter
   {my ($name) = @_;
    $p{$name} = R($name, 3);                                                    # Make a reference parameter variable
   }

  check  ($_) for @in;
  check  ($_) for @out;
  checkIo($_) for @io;

  my $start = Label;                                                            # Jump over code - would be better to put it in a different section
  my $end   = Label;
  Jmp $end;

  SetLabel $start;
  &$body({%p});                                                                 # Code with parameters
  Ret;
  SetLabel $end;

  defined($name) or confess "Name missing";
  $subroutines{$name} = genHash(__PACKAGE__."::Sub",                            # Subroutine definition
    start     => $start,
    name      => $name,
    comment   => $comment,
    in        => {map {$_=>3} @in},
    out       => {map {$_=>3} @out},
    io        => {map {$_=>3} @io},
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
    unless ($sub->in->{$n} or $sub->out->{$n} or $sub->io->{$n})                # Describe valid parameters using a table
     {my @t;
      push @t, map {[q(in),  $_]} keys $sub->in ->%*;
      push @t, map {[q(io),  $_]} keys $sub->io ->%*;
      push @t, map {[q(out), $_]} keys $sub->out->%*;
      my $t = formatTable([@t], [qw(Type Name)]);
      confess "Invalid parameter: '$n'\n$t";
     }
    $p{$n} = $v;
   }

  if (1)                                                                        # Check for duplicate parameters
   {my %dup; $dup{$_}++ for map {keys $sub->{$_}->%*} qw(in out io);
    for my $d(keys %dup) {delete $dup{$d} if $dup{$d} <= 1}                       # Remove singletons
    keys %dup and confess "Duplicate keys ".dump([keys %dup]);
   }

  if ((keys $sub->in->%*) or (keys $sub->io->%*))                               # Transfer input parameters
   {PushR my $transfer = r15;

    for my $p(keys $sub->in->%*)                                                # Load input parameters
     {confess "Missing in parameter: $p" unless my $v = $p{$p};
      $sub->variables->{$p}->copy($v, $transfer);
     }

    for my $p(keys $sub->io->%*)                                                # Load io parameters
     {confess "Missing io parameter: $p" unless my $v = $p{$p};
      $sub->variables->{$p}->copyAddress($v, $transfer);
     }

    PopR $transfer;
   }

  my $n = $$sub{name};
  Trace;
  Call $$sub{start};                                                            # Call the sub routine
  Trace;

  if ((keys $sub->out->%*))                                                     # Transfer output parameters
   {PushR my $transfer = r15;
    for my $p(keys $sub->out->%*)                                               # Load output parameters
     {confess qq(Missing output parameter: "$p") unless my $v = $p{$p};
      $v->copy($sub->variables->{$p}, $transfer);
     }
    PopR $transfer;
   }
 }

sub cr(&@)                                                                      # Call a subroutine with a reordering of the registers.
 {my ($body, @registers) = @_;                                                  # Code to execute with reordered registers, registers to reorder
  ReorderSyscallRegisters   @registers;
  &$body;
  UnReorderSyscallRegisters @registers;
 }

sub CommentWithTraceBack(@)                                                     # Insert a comment into the assembly code with a traceback showing how it was generated
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  eval {confess};
  my $p = dump($@);
  push @text, <<END;
; $c  $p
END
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
  @_ >= 2 or confess;

  my $c = join ' ', @string;
  my $l = length($c);
  my $a = Rs($c);

  my $s = Subroutine
   {Comment "Write start to channel  $channel, the string: ".dump($c);
    SaveFirstFour;
    Mov rax, 1;
    Mov rdi, $channel;
    Mov rsi, $a;
    Mov rdx, $l;
    Syscall;
    RestoreFirstFour();
    Comment "Write end to channel  $channel, the string: ".dump($c);
   } name => "PrintString_${channel}_${c}";

  $s->call;
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
  my $hexTranslateTable = hexTranslateTable;
  $end //= 7;                                                                   # Default end byte

  my $sub = Macro
   {Comment "Print Rax In Hex on channel: $channel start";
    SaveFirstFour rax;                                                          # Rax is a parameter
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
    Comment "Print Rax In Hex on channel: $channel start";
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
   {Call Macro
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
  IfNz Then {PrintErrStringNL "ZF=0"}, Else {PrintErrStringNL "ZF=1"};
  Popfq;
 }

sub PrintOutZF                                                                  # Print the zero flag without disturbing it on stdout
 {@_ == 0 or confess;

  Pushfq;
  IfNz Then {PrintOutStringNL "ZF=0"}, Else {PrintOutStringNL "ZF=1"};
  Popfq;
 }

#D1 Variables                                                                   # Variable definitions and operations

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
   {#DComment qq(Variable name: "$name", size: $size);
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
#   laneSize  => undef,                                                         # Size of the lanes in this variable
    name      => $name,                                                         # Name of the variable
    purpose   => undef,                                                         # Purpose of this variable
    reference => undef,                                                         # Reference to another variable
    size      => $nSize,                                                        # Size of variable
   );
 }

sub V(*;$%)                                                                     # Define a quad variable
 {my ($name, $expr, %options) = @_;                                             # Name of variable, initializing expression, options
  &Variable(3, @_)
 }

sub K(*;$%)                                                                     # Define a quad constant
 {my ($name, $expr, %options) = @_;                                             # Name of variable, initializing expression, options
  &Variable(3, @_, constant=>1)
 }

sub R(*;$)                                                                      # Define a reference variable
 {my ($name, $size) = @_;                                                       # Name of variable, variable being referenced
  my $r = &Variable(3, $name);                                                  # The referring variable is 64 bits wide
  $r->reference = $size;                                                        # Mark variable as a reference
  $r                                                                            # Size of the referenced variable
 }

#D2 Print variables                                                             # Print the values of variables or the memory addressed by them

sub Nasm::X86::Variable::dump($$$;$$)                                           #P Dump the value of a variable to the specified channel adding an optional title and new line if requested
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

sub Nasm::X86::Variable::copy($$;$)                                             # Copy one variable into another
 {my ($left, $right, $Transfer) = @_;                                           # Left variable, right variable, optional transfer register
  @_ == 2 or @_ == 3 or confess;

  my $transfer = $Transfer // r15;                                              # Transfer register

  ref($right) =~ m(Variable) or confess "Variable required";
  my $l = $left ->address;
  my $r = $right->address;

  if ($left->size == 3 and $right->size == 3)
   {my $lr = $left ->reference;
    my $rr = $right->reference;

    PushR $transfer unless $Transfer;
    Mov $transfer, $r;
    if ($rr)
     {Mov $transfer, "[$transfer]";
     }
    if (!$lr)
     {Mov $l, $transfer;
     }
    else
     {Comment "Copy ".$right->name.' to '.$left->name;
      my ($ref) = ChooseRegisters(1, $transfer);
      PushR $ref;
      Mov $ref, $l;
      Mov "[$ref]", $transfer;
      PopR $ref;
     }
    PopR $transfer unless $Transfer;
    return;
   }

  confess "Need more code";
 }

sub Nasm::X86::Variable::copyAddress($$;$)                                      # Copy a reference to a variable
 {my ($left, $right, $Transfer) = @_;                                           # Left variable, right variable, optional transfer register
  my $transfer = $Transfer // r15;

  $left->reference  or confess "Left hand side must be a reference";
  $left->size == 3  or confess "Left hand side must be size 3";

  my $l = $left ->address;
  my $r = $right->address;

  if ($right->size == 3)
   {PushR $transfer unless $Transfer;
    if ($right->reference)                                                      # Right is a reference so we copy its value
     {Mov $transfer, $r;
     }
    else                                                                        # Right is not a reference so we copy its address
     {Lea $transfer, $r;
     }
    Mov $l, $transfer;                                                          # Save value of address in left
    PopR $transfer unless $Transfer;
    return;
   }

  confess "Need more code";
 }


sub Nasm::X86::Variable::copyZF($)                                              # Copy the current state of the zero flag into a variable
 {my ($var) = @_;                                                               # Variable
  @_ == 1 or confess;

  my $a = $var->address;                                                        # Address of the variable

  if ($var->size == 3)
   {PushR my @save = (rax);
    Lahf;                                                                       # Save flags to ah: (SF:ZF:0:AF:0:PF:1:CF)
    Shr ah, 6;                                                                  # Put zero flag in bit zero
    And ah, 1;                                                                  # Isolate zero flag
    Mov $a, ah;                                                                 # Save zero flag
    PopR @save;
    return;
   }

  confess "Need more code";
 }

sub Nasm::X86::Variable::copyZFInverted($)                                      # Copy the opposite of the current state of the zero flag into a variable
 {my ($var) = @_;                                                               # Variable
  @_ == 1 or confess;

  my $a = $var->address;                                                        # Address of the variable

  if ($var->size == 3)
   {PushR my @save = (rax);
    Lahf;                                                                       # Save flags to ah: (SF:ZF:0:AF:0:PF:1:CF)
    Shr ah, 6;                                                                  # Put zero flag in bit zero
    Not ah;                                                                     # Invert zero flag
    And ah, 1;                                                                  # Isolate zero flag
    Mov $a, ah;                                                                 # Save zero flag
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
    my $new = V('Clone of '.$var->name);
    PushR my @save = (r15);
    Mov r15, $var->address;
    Mov $new->address, r15;
    PopR @save;
    $new->reference = $var->reference;
    return $new;
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
    my $v = V(join(' ', '('.$left->name, $name, (ref($right) ? $right->name : $right).')'), r15);
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
    my $v = V(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), $op eq "%" ? rdx : rax);
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
    my $v = V(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), r15);
    PopR r15;
    return $v;
   }
  confess "Need more code";
 }

sub Nasm::X86::Variable::booleanC($$$$)                                         # Combine the left hand variable with the right hand variable via a boolean operator using a conditional move instruction.
 {my ($cmov, $op, $left, $right) = @_;                                          # conditional move instruction name, operator name, Left variable,  right variable

  !ref($right) or ref($right) =~ m(Variable) or confess "Variable expected";
  my $r = ref($right) ? $right->address : $right;                               # Right can be either a variable reference or a constant

  if ($left->size == 3)
   {PushR r15;
    Mov r15, $left ->address;
    if ($left->reference)                                                       # Dereference left if necessary
     {Mov r15, "[r15]";
     }
    if (ref($right) and $right->reference)                                      # Dereference on right if necessary
     {PushR r14;
      Mov r14, $right ->address;
      Mov r14, "[r14]";
      Cmp r15, r14;
     }
    elsif (ref($right))                                                         # Variable but not a reference on the right
     {Cmp r15, $right->address;
     }
    else                                                                        # Constant on the right
     {Cmp r15, $right;
     }

    Mov r15, 1;                                                                 # Place a one below the stack
    my $w = RegisterSize r15;
    Mov "[rsp-$w]", r15;
    Mov r15, 0;                                                                 # Assume the result was false
    &$cmov(r15, "[rsp-$w]");                                                    # Indicate true result
    my $v = V(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), r15);
    PopR r15;
    return $v;
   }
  confess "Need more code";
 }

sub Nasm::X86::Variable::eq($$)                                                 # Check whether the left hand variable is equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanC(\&Cmove, q(eq), $left, $right);
 }

sub Nasm::X86::Variable::ne($$)                                                 # Check whether the left hand variable is not equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::boolean(\&IfNe, q(ne), $left, $right);
 }

sub Nasm::X86::Variable::ge($$)                                                 # Check whether the left hand variable is greater than or equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanC(\&Cmovge, q(ge), $left, $right);
 }

sub Nasm::X86::Variable::gt($$)                                                 # Check whether the left hand variable is greater than the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanC(\&Cmovg, q(gt), $left, $right);
 }

sub Nasm::X86::Variable::le($$)                                                 # Check whether the left hand variable is less than or equal to the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanC(\&Cmovle, q(le), $left, $right);
 }

sub Nasm::X86::Variable::lt($$)                                                 # Check whether the left hand variable is less than the right hand variable
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanC(\&Cmovl, q(lt), $left, $right);
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
  my $r = V("Minimum(".$left->name.", ".$right->name.")", r12);
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
  my $r = V("Maximum(".$left->name.", ".$right->name.")", r12);
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
  my $r = V("And(".$left->name.", ".$right->name.")", r14);
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
  my $r = V("Or(".$left->name.", ".$right->name.")", r14);
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

  PushR my @save = my ($l, $b) = ChooseRegisters(2, $mask);                     # Choose two registers not the mask register
  Mov $b, -1;
  $length->setReg($l);
  Bzhi $b, $b, $l;
  Kmovq $mask, $b if $mask =~ m(\Ak)i;                                          # Set mask register if provided
  Mov   $mask, $b if $mask =~ m(\Ar)i;                                          # Set general purpose register if provided
  PopR @save;
 }

sub Nasm::X86::Variable::setMaskBit($$)                                         # Set a bit in the specified mask register retaining the other bits
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to set, mask register
  @_ == 2 or confess;
  $mask =~ m(\Ak)i or confess "Mask register required";
  PushR my @save = my ($l, $b) = (r14, r15);
  Kmovq $b, $mask;
  $index->setReg($l);
  Bts $b, $l;
  Kmovq $mask, $b;                                                              # Set mask register if provided
  PopR @save;
 }

sub Nasm::X86::Variable::clearMaskBit($$)                                       # Clear a bit in the specified mask register retaining the other bits
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to clear, mask register
  @_ == 2 or confess;
  $mask =~ m(\Ak)i or confess "Mask register required";

  PushR my @save = my ($l, $b) = (r14, r15);
  Kmovq $b, $mask;
  $index->setReg($l);
  Btc $b, $l;
  Kmovq $mask, $b;                                                              # Set mask register if provided
  PopR @save;
 }

sub Nasm::X86::Variable::setBit($$)                                             # Set a bit in the specified register retaining the other bits
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to set, mask register
  @_ == 2 or confess;

  PushR my @save = my ($l) = ChooseRegisters(1, $mask);                         # Choose a register
  $index->setReg($l);
  Bts $mask, $l;
  PopR @save;
 }

sub Nasm::X86::Variable::clearBit($$)                                           # Clear a bit in the specified mask register retaining the other bits
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to clear, mask register
  @_ == 2 or confess;

  PushR my @save = my ($l) = ChooseRegisters(1, $mask);                         # Choose a register
  $index->setReg($l);
  Btc $mask, $l;
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

sub loadFromZmm($*$$)                                                           # Load the specified register from the offset located in the numbered zmm.
 {my ($register, $size, $zmm, $offset) = @_;                                    # Register to load, "b|w|d|q" for size, numbered zmm register to load from, constant offset in bytes
  @_ == 4 or confess;
  $offset >= 0 && $offset <= RegisterSize zmm0 or confess "Out of range";

  $register =~ m(\Ar\d+) or confess "Choose r8..r15 not $register";

  PushRR "zmm$zmm";                                                             # Push source register

  ClearRegisters $register;

  Mov $register."b", "[rsp+$offset]" if $size =~ m(b);                          # Load byte register from offset
  Mov $register."w", "[rsp+$offset]" if $size =~ m(w);                          # Load word register from offset
  Mov $register."d", "[rsp+$offset]" if $size =~ m(d);                          # Load double word register from offset
  Mov $register,     "[rsp+$offset]" if $size =~ m(q);                          # Load register from offset
  Add rsp, RegisterSize "zmm$zmm";                                              # Pop source register
 }

sub putIntoZmm($*$$)                                                            # Put the specified register into the numbered zmm at the from the offset located in the numbered zmm.
 {my ($register, $size, $zmm, $offset) = @_;                                    # Register to load, bwdq for size, numbered zmm register to load from, constant offset in bytes
  @_ == 4 or confess;
  $offset >= 0 && $offset <= RegisterSize zmm0 or confess "Out of range";

  PushR "zmm$zmm";                                                              # Push source register

  Mov "[rsp+$offset]", $register."b" if $size =~ m(b);                          # Load byte register from offset
  Mov "[rsp+$offset]", $register."w" if $size =~ m(w);                          # Load word register from offset
  Mov "[rsp+$offset]", $register."d" if $size =~ m(d);                          # Load double word register from offset
  Mov "[rsp+$offset]", $register,    if $size =~ m(q);                          # Load register from offset
  PopR "zmm$zmm";                                                               # Reload zmm
 }

sub getBwdqFromMm($$$;$)                                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 {my ($size, $mm, $offset, $Transfer) = @_;                                     # Size of get, mm register, offset in bytes either as a constant or as a variable, optional transfer register
  @_ == 3 or @_ == 4 or confess;
  my $w = RegisterSize $mm;                                                     # Size of mm register
  !$Transfer or $Transfer =~ m(\Ar\d+\Z) or confess "Need a numbered register"; # Check that we have a numbered register
  my $transfer = $Transfer // r15;                                              # Register to use to transfer value to variable

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
    $offset >= 0 && $offset <= RegisterSize $mm or
      confess "Out of range" if $offset =~ m(\A\d+\Z);                          # Check the offset if it is a number
    $offset =~ m(r15)
      and confess "Cannot pass offset: '$offset', in r15, choose another register";
   }

  PushR $transfer unless $Transfer;
  Vmovdqu32 "[rsp-$w]", $mm;                                                    # Write below the stack

  if ($size !~ m(q|d))                                                          # Clear the register if necessary
   {ClearRegisters r15; KeepFree r15;
   }

  Mov $transfer."b", "[rsp+$o-$w]" if $size =~ m(b);                            # Load byte register from offset
  Mov $transfer."w", "[rsp+$o-$w]" if $size =~ m(w);                            # Load word register from offset
  Mov $transfer."d", "[rsp+$o-$w]" if $size =~ m(d);                            # Load double word register from offset
  Mov $transfer,     "[rsp+$o-$w]" if $size =~ m(q);                            # Load register from offset

  my $v = V("$size at offset $offset in $mm", $transfer);                       # Create variable
  PopR $transfer unless $Transfer;
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

sub getDFromZmm($$;$)                                                           # Get the double word from the numbered zmm register and return it in a variable
 {my ($zmm, $offset, $transfer) = @_;                                           # Numbered zmm, offset in bytes, optional transfer register
  getBwdqFromMm('d', "zmm$zmm", $offset, $transfer)                             # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
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
  my $w = RegisterSize $mm;                                                     # Size of mm register

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
    $offset >= 0 && $offset <= RegisterSize $mm or
      confess "Out of range" if $offset =~ m(\A\d+\Z);                          # Check the offset if it is a number
    $offset =~ m(r15) and
      confess "Cannot pass offset: '$offset', in r15, choose another register";
   }

  PushR my @save = (r15);                                                        # Push target register
  $content->setReg(r15);
  Vmovdqu32 "[rsp-$w]", $mm;                                                    # Write below the stack
  Mov   "[rsp+$o-$w]", r15b if $size =~ m(b);                                   # Write byte register
  Mov   "[rsp+$o-$w]", r15w if $size =~ m(w);                                   # Write word register
  Mov   "[rsp+$o-$w]", r15d if $size =~ m(d);                                   # Write double word register
  Mov   "[rsp+$o-$w]", r15  if $size =~ m(q);                                   # Write register
  Vmovdqu32 $mm, "[rsp-$w]";                                                    # Read below the stack
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
  &AllocateMemory(size => $size, my $a = V(address));
  $a
 }

#D2 Structured Programming with variables                                       # Structured programming operations driven off variables.

sub Nasm::X86::Variable::for($&)                                                # Iterate the body limit times.
 {my ($limit, $body) = @_;                                                      # Limit, Body
  @_ == 2 or confess;
  Comment "Variable::For $limit";
  my $index = V(q(index), 0);                                                   # The index that will be incremented
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
   } in => [qw(size)], out => [qw(address)];

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
   } in => [qw(size address)];

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
     {V(align, rsi)->setMaskFirst(k7);                                          # Set mask bits
      Vmovdqu8 "[rax]{k7}", zmm0;                                               # Masked move to memory
      Add rax, rsi;                                                             # Update point to clear from
      Sub rdi, rsi;                                                             # Reduce clear length
     };

    For                                                                         # Clear remaining memory in full zmm blocks
     {Vmovdqu64 "[rax]", zmm0;
     } rax, rdx, RegisterSize zmm0;

    PopR @save;
   } in => [qw(size address)];

  $s->call(@variables);
 }

sub MaskMemory22(@)                                                               # Write the specified byte into locations in the target mask that correspond to the locations in the source that contain the specified byte.
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
     {V(align, r10)->setMaskFirst(k7);                                          # Set mask bits
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
   } in => [qw(size source mask match set)];                                    # Match is the character to match on in the source, set is the character to write into the mask at the corresponding position.

  $s->call(@variables);
 }

sub MaskMemoryInRange4_22(@)                                                    # Write the specified byte into locations in the target mask that correspond to the locations in the source that contain 4 bytes in the specified range.
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

    my sub check($$)                                                            # Check a character
     {my ($z, $f) = @_;                                                         # First zmm, finished label
      my $Z = $z + 4;
      Vpcmpub  "k6{k7}", zmm0, "zmm$z", 5;                                      # Greater than or equal
      Vpcmpub  "k7{k6}", zmm0, "zmm$Z", 2;                                      # Less than or equal
      Ktestq k7, k7;
      Jz $f;                                                                    # No match
      Kshiftlq k7, k7, 1;                                                       # Match - move up to next character
     };

    my sub last4()                                                              # Expand each set bit four times
     {Kshiftlq k6, k7, 1;  Kandq k7, k6, k7;                                    # We have found a character in the specified range
      Kshiftlq k6, k7, 2;  Kandq k7, k6, k7;                                    # Last four
     };

    For                                                                         # Mask remaining memory in full zmm blocks
     {my $finished = Label;                                                     # Point where we have finished the initial comparisons
      Vmovdqu8 zmm0, "[rax]";                                                   # Load complete block of source
      Kxnorq k7, k7, k7;                                                        # Complete block - sets register to all ones
      check($_, $finished) for 2..5;  last4;                                    # Check a range

      Vmovdqu8 "[rdx]{k7}", zmm1;                                               # Write set byte into mask at match points
      Add rdx, $size;                                                           # Update point to mask to
      SetLabel $finished;
     } rax, r8, $size;


    Mov r10, rsi; And r10, 0x3f;                                                # Modulus the size of zmm
    Test r10, r10;
    IfNz sub                                                                    # Need to align so that the rest of the mask can be done in full zmm blocks
     {my $finished = Label;                                                     # Point where we have finished the initial comparisons
      V(align, r10)->setMaskFirst(k7);                                          # Set mask bits
      Vmovdqu8 "zmm0\{k7}", "[rax]";                                            # Load first incomplete block of source
      check($_, $finished) for 2..5;  last4;                                    # Check a range
      Vmovdqu8 "[rdx]{k7}", zmm1;                                               # Write set byte into mask at match points
      Add rax, r10;                                                             # Update point to mask from
      Add rdx, r10;                                                             # Update point to mask to
      Sub  r8, r10;                                                             # Reduce mask length
      SetLabel $finished;
     };

    PopR @save;
   } in => [qw(size source mask set low high)];

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
   } in => [qw(source target size)];

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
   } in => [qw(file)], out => [qw(address size)];

  $s->call(@variables);
 }

sub executeFileViaBash(@)                                                       # Execute the file named in the arena addressed by rax with bash
 {my (@variables) = @_;                                                         # Variables
  @_ >= 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Execute a file via bash";
    SaveFirstFour;
    Fork;                                                                       # Fork

    Test rax, rax;

    IfNz                                                                        # Parent
    Then
     {WaitPid;
     },
    Else                                                                        # Child
     {KeepFree rax;
      $$p{file}->setReg(rdi);
      Mov rsi, 0;
      Mov rdx, 0;
      Mov rax, 59;
      Syscall;
     };
    RestoreFirstFour;
   } in => [qw(file)];

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
   } in => [qw(file)];

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
    Then
     {$$p{out}->getReg(r14);
      $$p{size}->copy(K(one, 1));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    Cmp r14, 0xdf;                                                              # 2 bytes
    IfLe
    Then
     {Mov r13b, "[r15+1]";
      And r13, 0x3f;
      And r14, 0x1f;
      Shl r14, 6;
      Or  r14,  r13;
      $$p{out}->getReg(r14);
      $$p{size}->copy(K(two, 2));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    Cmp r14, 0xef;                                                              # 3 bytes
    IfLe
    Then
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
      $$p{size}->copy(K(three, 3));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    Cmp r14, 0xf7;                                                              # 4 bytes
    IfLe
    Then
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
      $$p{size}->copy(K(four, 4));
      Jmp $success;
      KeepFree rax, r11, r12, r13, r14, r15;
     };

    $$p{fail}->getConst(1);                                                     # Conversion failed

    SetLabel $success;

    PopR @save;
   } in => [qw(in)], out => [qw(out  size  fail)];

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
    AllocateMemory size => $size, my $address = V(address);

     $$p{u8}            ->setReg(r14);                                          # Current position in input string
    ($$p{u8}+$$p{size8})->setReg(r15);                                          # Upper limit of input string
    $address->setReg(r13);                                                      # Current position in output string
    ClearRegisters r12;                                                         # Number of characters in output string

    ForEver sub                                                                 # Loop through input string  converting each utf8 sequence to utf32
     {my ($start, $end) = @_;
      my @p = my ($out, $size, $fail) = (V(out), V(size), V('fail'));
      GetNextUtf8CharAsUtf32 V(in, r14), @p;                                    # Get next utf 8 character and convert it to utf32
      If ($fail,
      Then
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
      Jge $end;                                                                 # Exhausted input string
    };

    $$p{u32}   ->copy($address);                                                # Address of allocation
    $$p{size32}->copy($size);                                                   # Size of allocation
    $$p{count} ->getReg(r12);                                                   # Number of unicode points converted from utf8 to utf32
    PopR @save;
   } in => [qw(u8  size8)], out => [qw(u32 size32 count)];

  $s->call(@parameters);
 } # ConvertUtf8ToUtf32

sub ClassifyRange($@)                                                           #P Implementation of ClassifyInRange and ClassifyWithinRange
 {my ($recordOffsetInRange, @parameters) = @_;                                  # Record offset in classification in high byte if 1 else in classification if 2, parameters
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
      Jz $next;                                                                 # No character was matched
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
     in   => [qw(address size)];

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

sub ClassifyWithInRangeAndSaveOffset(@)                                         # Alphabetic classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification code in the high byte of zmm1 and the offset of the first element in the range in the high byte of zmm0.  The lowest 21 bits of each double word in zmm0 and zmm1  contain the utf32 characters marking the start and end of each range. The classification bits from zmm1 for the first matching range are copied into the high byte of each utf32 character in the block of memory.  The offset in the range is copied into the lowest byte of each utf32 character in the block of memory.  The middle two bytes are cleared.  The net effect is to reduce 21 bits of utf32 to 16 bits.
 {my (@parameters) = @_;                                                        # Parameters
  ClassifyRange(2, @_);
 }

sub PrintUtf32($$)                                                              #P Print the specified number of utf32 characters at the specified address
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
    If ($index % 8 == 7,
    Then
     {PrintOutNL;                                                               #
     },
    Else
     {If($index != $count1, sub
       {PrintOutString "  ";
       });
     });
   });
  PrintOutNL;
  PopR @save;
 }

#D1 Short Strings                                                               # Operations on Short Strings

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

#D1 Arenas                                                                      # An arena is single extensible block of memory which contains other data structures such as strings, arrays, trees within it.

sub Cstrlen()                                                                   #P Length of the C style string addressed by rax returning the length in r15
 {@_ == 0 or confess;

  my $sub  = Macro                                                              # Create arena
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
   } in => [qw(string)], out => [qw(size)];

  $s->call(@parameters, my $z = V(size));                                       # Variable that holds the length of the string
  $z
 }

sub CreateArena(%)                                                              # Create an relocatable arena and returns its address in rax. Optionally add a chain header so that 64 byte blocks of memory can be freed and reused within the arena.
 {my (%options) = @_;                                                           # free=>1 adds a free chain.
  Comment "Create arena";
  my $N = V(size, 4096);                                                        # Initial size of string

  my ($string, $size, $used, $free) = All8Structure 3;                          # String base
  my $data = $string->field(0, "start of data");                                # Start of data

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;

    AllocateMemory($N, address=>$$p{bs});                                       # Allocate memory and save its location in a variable

    $$p{bs}->setReg(rax);
    $N     ->setReg(rdx);
    Mov rdi, $string->size;                                                     # Size of arena base structure which is constant
    Mov $used->addr, rdi;                                                       # Used space
    Mov $size->addr, rdx;                                                       # Size

    RestoreFirstFour;
   } out => [qw(bs)];

  $s->call(my $bs = V(bs));                                                     # Variable that holds the reference to the arena

  genHash(__PACKAGE__."::Arena",                                                # Definition of arena
    structure => $string,                                                       # Structure details
    size      => $size,                                                         # Size field details
    used      => $used,                                                         # Used field details
    free      => $free,                                                         # Free chain offset
    data      => $data,                                                         # The start of the data
    bs        => $bs,                                                           # Variable that addresses the arena
   );
 }

sub Nasm::X86::Arena::chain($$$@)                                               #P Return a variable with the end point of a chain of double words in the arena starting at the specified variable.
 {my ($arena, $bs, $variable, @offsets) = @_;                                   # Arena descriptor, arena locator, start variable,  offsets chain
  @_ >= 3 or confess;

  PushR my @save = (r14, r15);                                                  # 14 is the arena address, 15 the current offset in the arena
  $bs->setReg(r14);
  $variable->setReg(r15);
  for my $o(@offsets)                                                           # Each offset
   {KeepFree r15;
    Mov r15d, "dword[r14+r15+$o]";                                              # Step through each offset
   }
  my $r = V(join (' ', @offsets), r15);                                         # Create a variable with the result
  PopR @save;
  $r
 }

sub Nasm::X86::Arena::putChain($$$$@)                                           #P Write the double word in the specified variable to the double word location at the the specified offset in the specified arena.
 {my ($arena, $bs,  $start, $value, @offsets) = @_;                             # Arena descriptor, arena locator variable, start variable, value to put as a variable,  offsets chain
  @_ >= 5 or confess;

  PushR my @save = (r14, r15);                                                  # 14 is the arena address, 15 the current offset in the arena
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

sub Nasm::X86::Arena::length($@)                                                # Get the length of an arena
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables
  @_ >= 2 or confess;
  my $size = $arena->size->addr;
  my $used = $arena->used->addr;

  my $s = Subroutine                                                            # Allocate more space if required
   {my ($p) = @_;                                                               # Parameters
    Comment "Arena length";
    SaveFirstFour;
    $$p{bs}->setReg(rax);                                                       # Address arena
    Mov rdx, $arena->used->addr;                                                # Used
    Sub rdx, $arena->structure->size;
    $$p{size}->getReg(rdx);
    RestoreFirstFour;
   } in => [qw(bs)], out => [qw(size)];

  $s->call($arena->bs, @variables);
 }

sub Nasm::X86::Arena::updateSpace($@)                                           #P Make sure that the arena addressed by rax has enough space to accommodate content of length rdi
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables

  @_ >= 3 or confess;
  my $size = $arena->size->addr;
  my $used = $arena->used->addr;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Allocate more space for an arena";
    SaveFirstFour;
    $$p{bs}->setReg(rax);                                                       # Address arena
    my $oldSize = V(oldSize, $size);                                            # Size
    my $oldUsed = V(oldUsed, $used);                                            # Used
    my $minSize = $oldUsed + $$p{size};                                         # Minimum size of new string
    KeepFree rax;
    If ($minSize > $oldSize,
    Then                                                                        # More space needed
     {Mov rax, 4096;                                                            # Minimum arena size
      $minSize->setReg(rdx);
      ForEver
       {my ($start, $end) = @_;
        Shl rax, 1;                                                             # New arena size - double the size of the old arena
        Cmp rax, rdx;                                                           # Big enough?
        Jge $end;                                                               # Big enough!
       };
      my $newSize = V(size, rax);                                               # Save new arena size
      AllocateMemory(size => $newSize, my $address = V(address));               # Create new arena
      CopyMemory(target  => $address, source => $$p{bs}, size => $oldUsed);     # Copy old arena into new arena
      FreeMemory(address => $$p{bs},  size   => $oldSize);                      # Free previous memory previously occupied arena
      $$p{bs}->copy($address);                                                  # Save new arena address
     });

    RestoreFirstFour;
   } io => [qw(bs)], in => [qw(size)];

  $s->call(@variables);
 } # updateSpace

sub Nasm::X86::Arena::makeReadOnly($)                                           # Make an arena read only
 {my ($arena) = @_;                                                             # Arena descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Make an arena readable";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    Mov rdi, rax;                                                               # Address of arena
    Mov rsi, $arena->size->addr;                                                # Size of arena
    KeepFree rax;

    Mov rdx, 1;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded arena
   } in => [qw(bs)];

  $s->call(bs => $arena->bs);
 }

sub Nasm::X86::Arena::makeWriteable($)                                          # Make an arena writable
 {my ($arena) = @_;                                                             # Arena descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Make an arena writable";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    Mov rdi, rax;                                                               # Address of arena
    Mov rsi, $arena->size->addr;                                                # Size of arena
    KeepFree rax;
    Mov rdx, 3;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded arena
   } in => [qw(bs)];

  $s->call(bs => $arena->bs);
 }

sub Nasm::X86::Arena::allocate($@)                                              # Allocate the amount of space indicated in rdi in the arena addressed by rax and return the offset of the allocation in the arena in rdi
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Allocate space in an arena";
    SaveFirstFour;

    $arena->updateSpace($$p{bs}, $$p{size});                                    # Update space if needed
    $$p{bs}  ->setReg(rax);
    Mov rsi, $arena->used->addr;                                                # Currently used
    $$p{offset}->getReg(rsi);
    $$p{size}  ->setReg(rdi);
    Add rsi, rdi;
    Mov $arena->used->addr, rsi;                                                # Currently used
    KeepFree rax, rdi, rsi;

    RestoreFirstFour;
   } in => [qw(size)], io => [qw(bs)], out => [qw(offset)];

  $s->call($arena->bs, @variables);
 }

sub Nasm::X86::Arena::blockSize($)                                              #P Size of a block
 {my ($arena) = @_;                                                             # Arena
  RegisterSize(zmm0)
 }

sub Nasm::X86::Arena::allocZmmBlock($@)                                         # Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable
 {my ($arena, @variables) = @_;                                                 # Arena, variables
  @_ >= 2 or confess;
  my $ffb = $arena->firstFreeBlock;                                             # Check for a free block
  If ($ffb > 0,
  Then                                                                          # Free block available
   {PushR zmm31;
    $arena->getBlock($arena->bs, $ffb, 31);                                     # Load the first block on the free chain
    my $second = getDFromZmm(31, 60);                                           # The location of the next pointer is forced upon us by string which got there first.
    $arena->setFirstFreeBlock($second);                                         # Set the first free block field to point to the second block
    for my $v(@variables)
     {if (ref($v) and $v->name eq "offset")
       {$v->copy($ffb);
        last;
       }
     }
    PopR zmm31;
   },
  Else                                                                          # Cannot reuse a free block so use unassigned memory
   {$arena->allocate(V(size, RegisterSize(zmm0)), @variables);
   });
 }

sub Nasm::X86::Arena::allocBlock($)                                             # Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable
 {my ($arena) = @_;                                                             # Arena
  @_ == 1 or confess;
  $arena->allocZmmBlock                                                         # Allocate a zmm block
   ($arena->bs, V(size, RegisterSize(zmm0)), my $o = V(offset));
  $o                                                                            # Offset as a variable
 }

sub Nasm::X86::Arena::firstFreeBlock($)                                         #P Create and load a variable with the first free block on the free block chain or zero if no such block in the given arena
 {my ($arena) = @_;                                                             # Arena address as a variable
  @_ == 1 or confess;

  Comment "Get first free block in an arena";
  PushR rax;
  $arena->bs->setReg(rax);                                                      #P Address underlying arena
  KeepFree rax;
  Mov rax, $arena->free->addr;                                                  # Content of free chain pointer
  my $v = V('free', rax);                                                       # Remainder of the free chain
  PopR rax;
  $v
 }

sub Nasm::X86::Arena::setFirstFreeBlock($$)                                     #P Set the first free block field from a variable
 {my ($arena, $offset) = @_;                                                    # Arena descriptor, first free block offset as a variable
  @_ == 2 or confess;

  Comment "Set first free block start";
  PushR my @save = (rax, rsi, rdx);
  $arena->bs->setReg(rax);                                                      # Address underlying arena
  Lea rdx, $arena->free->addr;                                                  # Address of address of free chain
  $offset->setReg(rsi);                                                         # Offset of block being freed
  Mov "[rdx]", rsi;                                                             # Set head of free chain to point to block just freed
  PopR @save;
  Comment "Set first free block end";
 }

sub Nasm::X86::Arena::freeBlock($@)                                             #P Free a block in an arena by placing it on the free chain
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Free a block in an arena";
    PushR zmm31;
    my $rfc = $arena->firstFreeBlock;                                           # Get first free block
    ClearRegisters zmm31;                                                       # Second block
    $rfc->putDIntoZmm(31, 60);                                                  # The position of the next pointer was dictated by strings.
    $arena->putBlock($$p{bs}, $$p{offset}, 31);                                 # Link the freed block to the rest of the free chain
    $arena->setFirstFreeBlock($$p{offset});                                     # Set free chain field to point to latest free chain element
    PopR zmm31;
   } in => [qw(offset)], io => [qw(bs)];

  $s->call($arena->bs, @variables);
 }

sub Nasm::X86::Arena::getBlock($$$$)                                            #P Get the block with the specified offset in the specified string and return it in the numbered zmm
 {my ($arena, $bsa, $block, $zmm) = @_;                                         # Arena descriptor, arena variable, offset of the block as a variable, number of zmm register to contain block
  @_ == 4 or confess;
  defined($bsa)   or confess;
  defined($block) or confess;

  Comment "Get block start";
  PushR my @save = (r14, r15);                                                  # Result register
  If ($block < $arena->data->loc,
  Then                                                                          #DEBUG
   {PrintErrStringNL "Attempt to get block below start of arena";
    Exit(1);
   });

  $bsa  ->setReg(r15);                                                          # Arena address
  $block->setReg(r14);                                                          # Offset of block in arena
  Vmovdqu64 "zmm$zmm", "[r15+r14]";                                             # Read from memory
  PopR @save;                                                                   # Restore registers
  Comment "Get block end";
 }

sub Nasm::X86::Arena::putBlock($$$$)                                            #P Write the numbered zmm to the block at the specified offset in the specified arena
 {my ($arena, $bsa, $block, $zmm) = @_;                                         # Arena descriptor, arena variable, block in arena, content variable
  @_ >= 4 or confess;
  PushR my @save = (r14, r15);                                                  # Work registers
  defined($bsa) or confess "Arena not set";
  $bsa->setReg(r15);                                                            # Arena address
  defined($block) or confess;
  If ($block < $arena->data->loc,
  Then                                                                          #DEBUG
   {PrintErrStringNL "Attempt to put block below start of arena";
    Exit(1);
   });
  $block->setReg(r14);                                                          # Offset of block in arena
  Vmovdqu64 "[r15+r14]", "zmm$zmm";                                             # Write to memory
  PopR @save;                                                                   # Restore registers
 }

sub Nasm::X86::Arena::m($@)                                                     # Append the content with length rdi addressed by rsi to the arena addressed by rax
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables
  @_ >= 4 or confess;
  my $used = $arena->used->addr;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Append memory to an arena";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    my $oldUsed = V("used", $used);
    $arena->updateSpace($$p{bs}, $$p{size});                                    # Update space if needed

    my $target  = $oldUsed + $$p{bs};
    KeepFree rax;
    CopyMemory(source => $$p{address}, $$p{size}, target => $target);           # Move data in

    KeepFree rdx;
    my $newUsed = $oldUsed + $$p{size};

    $$p{bs} ->setReg(rax);                                                      # Update used field
    $newUsed->setReg(rdi);
    Mov $used, rdi;

    RestoreFirstFour;
   } io => [qw(bs)], in => [qw(address size)];

  $s->call(@variables);
 }

sub Nasm::X86::Arena::q($$)                                                     # Append a constant string to the arena
 {my ($arena, $string) = @_;                                                    # Arena descriptor, string
  @_ == 2 or confess;

  my $s = Rs($string);

  my $bs = $arena->bs;                                                          # Move data
  my $ad = V(address, $s);
  my $sz = V(size, length($string));
  $arena->m($bs, $ad, $sz);
 }

sub Nasm::X86::Arena::ql($$)                                                    # Append a quoted string containing new line characters to the arena addressed by rax
 {my ($arena, $const) = @_;                                                     # Arena, constant
  @_ == 2 or confess;
  for my $l(split /\s*\n/, $const)
   {$arena->q($l);
    $arena->nl;
   }
 }

sub Nasm::X86::Arena::char($$)                                                  # Append a character expressed as a decimal number to the arena addressed by rax
 {my ($arena, $char) = @_;                                                      # Arena descriptor, number of character to be appended
  @_ == 2 or confess;
  my $s = Rb(ord($char));
  $arena->m($arena->bs, V(address, $s), V(size, 1));                            # Move data
 }

sub Nasm::X86::Arena::nl($)                                                     # Append a new line to the arena addressed by rax
 {my ($arena) = @_;                                                             # Arena descriptor
  @_ == 1 or confess;
  $arena->char("\n");
 }

sub Nasm::X86::Arena::z($)                                                      # Append a trailing zero to the arena addressed by rax
 {my ($arena) = @_;                                                             # Arena descriptor
  @_ == 1 or confess;
  $arena->char("\0");
 }

sub Nasm::X86::Arena::append($@)                                                # Append one arena to another
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Concatenate arenas";
    SaveFirstFour;
    $$p{source}->setReg(rax);
    Mov rdi, $arena->used->addr;
    Sub rdi, $arena->structure->size;
    Lea rsi, $arena->data->addr;
    $arena->m(bs=>$$p{target}, V(address, rsi), V(size, rdi));
    RestoreFirstFour;
   } in => [qw(target source)];

  $s->call(target=>$arena->bs, @variables);
 }

sub Nasm::X86::Arena::clear($)                                                  # Clear the arena addressed by rax
 {my ($arena) = @_;                                                             # Arena descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Clear arena";
    PushR my @save = (rax, rdi);
    $$p{bs}->setReg(rax);
    Mov rdi, $arena->structure->size;
    Mov $arena->used->addr, rdi;
    PopR     @save;
   } in => [qw(bs)];

  $s->call(bs => $arena->bs);
 }

sub Nasm::X86::Arena::write($@)                                                 # Write the content in an arena addressed by rax to a temporary file and replace the arena content with the name of the  temporary file
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Write an arena to a file";
    SaveFirstFour;

    $$p{file}->setReg(rax);
    OpenWrite;                                                                  # Open file
    my $file = V('fd', rax);                                                    # File descriptor
    KeepFree rax;

    $$p{bs}->setReg(rax);                                                       # Write file
    Lea rsi, $arena->data->addr;
    Mov rdx, $arena->used->addr;
    Sub rdx, $arena->structure->size;
    KeepFree rax;

    Mov rax, 1;                                                                 # Write content to file
    $file->setReg(rdi);
    Syscall;
    KeepFree rax, rdi, rsi, rdx;

    $file->setReg(rax);
    CloseFile;
    RestoreFirstFour;
   }  in => [qw(file)], io => [qw(bs)];

  $s->call(bs => $arena->bs, @variables);
 }

sub Nasm::X86::Arena::read($@)                                                  # Read the named file (terminated with a zero byte) and place it into the named arena.
 {my ($arena, @variables) = @_;                                                 # Arena descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Read an arena";
    ReadFile($$p{file}, (my $size = V(size)), my $address = V(address));
    $arena->m($$p{bs}, $size, $address);                                        # Move data into arena
    FreeMemory($size, $address);                                                # Free memory allocated by read
   } io => [qw(bs)], in => [qw(file)];

  $s->call(bs => $arena->bs, @variables);
 }

sub Nasm::X86::Arena::out($)                                                    # Print the specified arena addressed by rax on sysout
 {my ($arena) = @_;                                                             # Arena descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Write an arena";
    SaveFirstFour;
    $$p{bs}->setReg(rax);
    Mov rdi, $arena->used->addr;                                                # Length to print
    Sub rdi, $arena->structure->size;                                           # Length to print
    Lea rax, $arena->data->addr;                                                # Address of data field
    PrintOutMemory;
    RestoreFirstFour;
   } in => [qw(bs)];

  $s->call($arena->bs);
 }

sub Nasm::X86::Arena::dump($;$)                                                 # Dump details of an arena
 {my ($arena, $depth) = @_;                                                     # Arena descriptor, optional amount of memory to dump  as the number of 64 byte blocks
  @_ == 1 or @_ == 2  or confess;
  $depth //= 4;                                                                 # Default depth

  PushR my @save = (rax, r15);                                                  # Get address of arena
  $arena->bs->setReg(rax);

  Call Macro                                                                    # Bash string
   {Comment "Print details of an arena";
    SaveFirstFour;
    PrintOutStringNL("Arena");

    PushR rax;                                                                  # Print size
    Mov rax, $arena->size->addr;
    PrintOutString("  Size: ");
    PrintOutRaxInHex;
    PrintOutNL;
    PopR rax;

    PushR rax;                                                                  # Print used
    Mov rax, $arena->used->addr;
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
   } name => "Nasm::X86::Arena::dump$depth";

  PopR @save;
 }

#D1 String                                                                      # Strings made from zmm sized blocks of text

sub Nasm::X86::Arena::CreateString($)                                           # Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the arena addressed by rax and return its descriptor
 {my ($arena) = @_;                                                             # Arena description
  @_ == 1 or confess;
  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  Comment "Allocate a new string in an arena";

  my $s = genHash(__PACKAGE__."::String",                                       # String definition
    bs      => $arena,                                                          # Bytes string definition
    links   => $b - 2 * $o,                                                     # Location of links in bytes in zmm
    next    => $b - 1 * $o,                                                     # Location of next offset in block in bytes
    prev    => $b - 2 * $o,                                                     # Location of prev offset in block in bytes
    length  => $b - 2 * $o - 1,                                                 # Maximum length in a block
    first   => V('first'),                                                      # Variable addressing first block in string
   );

  my $first = $s->allocBlock;                                                   # Allocate first block
  $s->first->copy($first);                                                      # Record offset of first block

  if (1)                                                                        # Initialize circular list
   {my $nn = $s->next;
    my $pp = $s->prev;
    PushR my @save = (r14, r15);
    $arena->bs->setReg(r15);
    $first         ->setReg(r14);
    Mov "[r15+r14+$nn]", r14d;
    Mov "[r15+r14+$pp]", r14d;
    PopR @save;
   }
  $s                                                                            # Description of string
 }

sub Nasm::X86::String::address($)                                               #P Address of a string
 {my ($String) = @_;                                                            # String descriptor
  @_ == 1 or confess;
  $String->bs->bs;
 }

sub Nasm::X86::String::allocBlock($)                                            #P Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable
 {my ($String) = @_;                                                            # String descriptor
  @_ == 1 or confess;

  $String->bs->allocBlock;                                                      # Allocate block and return its offset as a variable
 }

sub Nasm::X86::String::getBlockLength($$)                                       #P Get the block length of the numbered zmm and return it in a variable
 {my ($String, $zmm) = @_;                                                      # String descriptor, number of zmm register
  @_ == 2 or confess;
  getBFromZmm $zmm, 0;                                                          # Block length
 }

sub Nasm::X86::String::setBlockLengthInZmm($$$)                                 #P Set the block length of the numbered zmm to the specified length
 {my ($String, $length, $zmm) = @_;                                             # String descriptor, length as a variable, number of zmm register
  @_ == 3 or confess;
  PushR my @save = (r15);                                                       # Save work register
  $length->setReg(r15);                                                         # New length
  $length->putBIntoZmm($zmm, 0);                                                # Insert block length
  PopR @save;                                                                   # Length of block is a byte
 }

sub Nasm::X86::String::getBlock($$$$)                                           #P Get the block with the specified offset in the specified string and return it in the numbered zmm
 {my ($String, $bsa, $block, $zmm) = @_;                                        # String descriptor, arena variable, offset of the block as a variable, number of zmm register to contain block
  @_ >= 4 or confess;
  $String->bs->getBlock($bsa, $block, $zmm);
 }

sub Nasm::X86::String::putBlock($$$$)                                           #P Write the numbered zmm to the block at the specified offset in the specified arena
 {my ($String, $bsa, $block, $zmm) = @_;                                        # String descriptor, arena variable, block in arena, content variable
  @_ >= 4 or confess;
  $String->bs->putBlock($bsa, $block, $zmm);
 }

sub Nasm::X86::String::getNextAndPrevBlockOffsetFromZmm($$)                     #P Get the offsets of the next and previous blocks as variables from the specified zmm
 {my ($String, $zmm) = @_;                                                      # String descriptor, zmm containing block
  @_ == 2 or confess;
  my $l = $String->links;                                                       # Location of links
  PushR my @regs = (r14, r15);                                                  # Work registers
  my $L = getQFromZmm($zmm, $String->links);                                    # Links in one register
  $L->setReg(r15);                                                              # Links
  Mov r14d, r15d;                                                               # Next
  Shr r15, RegisterSize(r14d) * 8;                                              # Prev
  my @r = (V("Next block offset", r15), V("Prev block offset", r14));           # Result
  PopR @regs;                                                                   # Free work registers
  @r;                                                                           # Return (next, prev)
 }

sub Nasm::X86::String::putNextandPrevBlockOffsetIntoZmm($$$$)                   #P Save next and prev offsets into a zmm representing a block
 {my ($String, $zmm, $next, $prev) = @_;                                        # String descriptor, zmm containing block, next offset as a variable, prev offset as a variable
  @_ == 4 or confess;
  if ($next and $prev)                                                          # Set both previous and next
   {PushR my @regs = (r14, r15);                                                # Work registers
    $next->setReg(r14);                                                         # Next offset
    $prev->setReg(r15);                                                         # Prev offset
    Shl r14, RegisterSize(r14d) * 8;                                            # Prev high
    Or r15, r14;                                                                # Links in one register
    my $l = V("Links", r15);                                                    # Links as variable
    $l->putQIntoZmm($zmm, $String->links);                                      # Load links into zmm
    PopR @regs;                                                                 # Free work registers
   }
  elsif ($next)                                                                 # Set just next
   {PushR my @regs = (r15);                                                     # Work registers
    $next->setReg(r15);                                                         # Next offset
    my $l = V("Links", r15);                                                    # Links as variable
    $l->putDIntoZmm($zmm, $String->next);                                       # Load links into zmm
    PopR @regs;                                                                 # Free work registers
   }
  elsif ($prev)                                                                 # Set just prev
   {PushR my @regs = (r15);                                                     # Work registers
    $prev->setReg(r15);                                                         # Next offset
    my $l = V("Links", r15);                                                    # Links as variable
    $l->putDIntoZmm($zmm, $String->prev);                                       # Load links into zmm
    PopR @regs;                                                                 # Free work registers
   }
 }

sub Nasm::X86::String::dump($)                                                  # Dump a string to sysout
 {my ($String) = @_;                                                            # String descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Dump a block in a string";
    PushR my @save = (zmm31);
    my $block  = $$p{first};                                                    # The first block
                 $String->getBlock($$p{bs}, $block, 31);                        # The first block in zmm31
    my $length = $String->getBlockLength(31);                                   # Length of block
    PrintOutStringNL "string Dump";
    $block ->out("Offset: ");
    PrintOutString "   ";
    $length->outNL("Length: "); PrintOutRegisterInHex zmm31;                    # Print block

    ForEver                                                                     # Each block in string
     {my ($start, $end) = @_;                                                   #
      my ($next, $prev) = $String->getNextAndPrevBlockOffsetFromZmm(31);        # Get links from current block
      If ($next == $block, sub{Jmp $end});                                      # Next block is the first block so we have printed the string
      $String->getBlock($$p{bs}, $next, 31);                                    # Next block in zmm
      my $length = $String->getBlockLength(31);                                 # Length of block
      $next  ->out("Offset: ");                                                 # Print block
      PrintOutString "   ";
      $length->outNL("Length: "); PrintOutRegisterInHex zmm31;
     };
    PrintOutNL;

    PopR @save;
   } in => [qw(first)], io => [qw(bs)];

  $s->call($String->address, $String->first);
 }

sub Nasm::X86::String::len($$)                                                  # Find the length of a string
 {my ($String, $size) = @_;                                                     # String descriptor, size variable
  @_ == 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Length of a string";
    PushR my @save = (zmm31);
    my $block  = $$p{first};                                                    # The first block
                 $String->getBlock($$p{bs}, $block, 31);                        # The first block in zmm31
    my $length = $String->getBlockLength(31);                                   # Length of block

    ForEver                                                                     # Each block in string
     {my ($start, $end) = @_;                                                   #
      my ($next, $prev) = $String->getNextAndPrevBlockOffsetFromZmm(31);        # Get links from current block
      If ($next == $block, sub{Jmp $end});                                      # Next block is the first block so we have printed the string
      $String->getBlock($$p{bs}, $next, 31);                                    # Next block in zmm
      $length += $String->getBlockLength(31);                                   # Add length of block
     };
    $$p{size}->copy($length);
    PopR @save;
   } in => [qw(first)], io => [qw(bs)], out => [qw(size)];

  $s->call($String->address, $String->first, $size);
 }

sub Nasm::X86::String::concatenate($$)                                          # Concatenate two strings by appending a copy of the source to the target string.
 {my ($target, $source) = @_;                                                   # Target string, source string
  @_ == 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Concatenate strings";
    PushR my @save = (zmm29, zmm30, zmm31);
    my $sb = $$p{sBs};                                                          # The arena underlying the source
    my $sf = $$p{sFirst};                                                       # The first block in the source
    my $tb = $$p{tBs};                                                          # The arena underlying the target
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
      If ($sn == $sf,
      Then                                                                      # Last source block
       {$source->getBlock($tb, $tf, 30);                                        # The first target block
        $source->putNextandPrevBlockOffsetIntoZmm(30, undef, $new);             # Update end of block chain
        $source->putBlock($tb, $tf, 30);                                        # Save modified first target block

        Jmp $end
       });

      $source->getBlock($sb, $sn, 31);                                          # Next source block
     };

    PopR @save;
   } in => [qw(sBs sFirst tBs tFirst)];

  $s->call(sBs => $source->address, sFirst => $source->first,
           tBs => $target->address, tFirst => $target->first);
 }

sub Nasm::X86::String::insertChar($@)                                           # Insert a character into a string
 {my ($String, @variables) = @_;                                                # String, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Insert character into a string";
    PushR my @save = (k7, r14, r15, zmm30, zmm31);
    my $B = $$p{bs};                                                            # The arena underlying the string
    my $F = $$p{first};                                                         # The first block in string
    my $c = $$p{character};                                                     # The character to insert
    my $P = $$p{position};                                                      # The position in the string at which we want to insert the character
    $String->getBlock($B, $F, 31);                                              # The first source block
    my $C = V('Current character position', 0);                                 # Current character position
    my $L = $String->getBlockLength(31);                                        # Length of last block
    my $M   = V('Block length', $String->length);                               # Maximum length of a block
    my $One = V('One', 1);                                                      # Literal one
    my $current = $F;                                                           # Current position in scan of block chain

    ForEver                                                                     # Each block in source string
     {my ($start, $end) = @_;                                                   # Start and end labels

      If ((($P >= $C) & ($P <= $C + $L)),
      Then                                                                      # Position is in current block
       {my $O = $P - $C;                                                        # Offset in current block
        PushRR zmm31;                                                           # Stack block
        $O->setReg(r14);                                                        # Offset of character in block
        $c->setReg(r15);                                                        # Character to insert
        Mov "[rsp+r14]", r15b;                                                  # Place character after skipping length field

        If ($L < $M,
        Then                                                                    # Current block has space
         {($P+1)->setMask($C + $L - $P + 1, k7);                                # Set mask for reload
          Vmovdqu8 "zmm31{k7}", "[rsp-1]";                                      # Reload
          $String->setBlockLengthInZmm($L + 1, 31);                             # Length of block
         },
        Else                                                                    # In the current block but no space so split the block
         {$One->setMask($C + $L - $P + 2, k7);                                  # Set mask for reload
          Vmovdqu8 "zmm30{k7}", "[rsp+r14-1]";                                  # Reload
          $String->setBlockLengthInZmm($O,          31);                        # New shorter length of original block
          $String->setBlockLengthInZmm($L - $O + 1, 30);                        # Set length of  remainder plus inserted char in the new block

          my $new = $String->allocBlock;                                        # Allocate new block
          my ($next, $prev)=$String->getNextAndPrevBlockOffsetFromZmm(31);      # Linkage from last block

          If ($next == $prev,
          Then                                                                  # The existing string has one block, add new as the second block
           {$String->putNextandPrevBlockOffsetIntoZmm(31, $new,  $new);
            $String->putNextandPrevBlockOffsetIntoZmm(30, $next, $prev);
           },
          Else                                                                  # The existing string has two or more blocks
           {$String->putNextandPrevBlockOffsetIntoZmm(31, $new,  $prev);        # From last block
            $String->putNextandPrevBlockOffsetIntoZmm(30, $next, $current);     # From new block
           });

          $String->putBlock($B, $new, 30);                                      # Save the modified block
         });

        $String->putBlock($B, $current, 31);                                    # Save the modified block
        PopRR zmm31;                                                            # Restore stack
        KeepFree r14, r15;
        Jmp $end;                                                               # Character successfully inserted
       });

      my ($next, $prev) = $String->getNextAndPrevBlockOffsetFromZmm(31);        # Get links from current source block
      If ($next == $F,
      Then                                                                      # Last source block
       {$c->setReg(r15);                                                        # Character to insert
        Push r15;
        $String->append($B, $F, V(size, 1), V(source, rsp));                    # Append character if we go beyond limit
        Pop  r15;
        Jmp $end;
       });

      $current->copy($next);
      $String->getBlock($B, $current, 31);                                      # Next block
      $L = $String->getBlockLength(31);                                         # Length of block
      $C += $L;                                                                 # Current character position at the start of this block
     };

    PopR @save;
   } in => [qw(first character position)], io => [qw(bs)];

  $s->call($String->address, first => $String->first, @variables)
 }

sub Nasm::X86::String::deleteChar($@)                                           # Delete a character in a string
 {my ($String, @variables) = @_;                                                # String, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Delete a character in a string";
    PushR my @save = (k7, zmm31);
    my $B = $$p{bs};                                                            # The arena underlying the string
    my $F = $$p{first};                                                         # The first block in string
    my $P = $$p{position};                                                      # The position in the string at which we want to insert the character
    $String->getBlock($B, $F, 31);                                              # The first source block
    my $C = V('Current character position', 0);                                 # Current character position
    my $L = $String->getBlockLength(31);                                        # Length of last block
    my $current = $F;                                                           # Current position in scan of block chain

    ForEver                                                                     # Each block in source string
     {my ($start, $end) = @_;                                                   # Start and end labels

      If ((($P >= $C) & ($P <= $C + $L)),
      Then                                                                      # Position is in current block
       {my $O = $P - $C;                                                        # Offset in current block
        PushRR zmm31;                                                           # Stack block
        ($O+1)->setMask($L - $O, k7);                                           # Set mask for reload
        Vmovdqu8 "zmm31{k7}", "[rsp+1]";                                        # Reload
        $String->setBlockLengthInZmm($L-1, 31);                                 # Length of block
        $String->putBlock($B, $current, 31);                                    # Save the modified block
        PopRR zmm31;                                                            # Stack block
        Jmp $end;                                                               # Character successfully inserted
       });

      my ($next, $prev) = $String->getNextAndPrevBlockOffsetFromZmm(31);        # Get links from current source block
      $String->getBlock($B, $next, 31);                                         # Next block
      $current->copy($next);
      $L = $String->getBlockLength(31);                                         # Length of block
      $C += $L;                                                                 # Current character position at the start of this block
     };

    PopR @save;
   } in => [qw(first  position )], io => [qw(bs)];

  $s->call($String->address, first => $String->first, @variables)
 }

sub Nasm::X86::String::getCharacter($@)                                         # Get a character from a string
 {my ($String, @variables) = @_;                                                # String, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Get a character from a string";
    PushR my @save = (r15, zmm31);
    my $B = $$p{bs};                                                            # The arena underlying the string
    my $F = $$p{first};                                                         # The first block in string
    my $P = $$p{position};                                                      # The position in the string at which we want to insert the character
    $String->getBlock($B, $F, 31);                                              # The first source block
    my $C = V('Current character position', 0);                                 # Current character position
    my $L = $String->getBlockLength(31);                                        # Length of last block

    ForEver                                                                     # Each block in source string
     {my ($start, $end) = @_;                                                   # Start and end labels

      If ((($P >= $C) & ($P <= $C + $L)),
      Then                                                                      # Position is in current block
       {my $O = $P - $C;                                                        # Offset in current block
        PushRR zmm31;                                                           # Stack block
        ($O+1)  ->setReg(r15);                                                  # Character to get
        KeepFree r15;
        Mov r15b, "[rsp+r15]";                                                  # Reload
        $$p{out}->getReg(r15);                                                  # Save character
        PopRR zmm31;                                                            # Stack block
        Jmp $end;                                                               # Character successfully inserted
       });

      my ($next, $prev) = $String->getNextAndPrevBlockOffsetFromZmm(31);        # Get links from current source block
      $String->getBlock($B, $next, 31);                                         # Next block
      $L = $String->getBlockLength(31);                                         # Length of block
      $C += $L;                                                                 # Current character position at the start of this block
     };

    PopR @save;
   } in => [qw(first  position )], io => [qw(bs)], out => [qw(out)];

  $s->call($String->address, first => $String->first, @variables)
 }

sub Nasm::X86::String::append($@)                                               # Append the specified content in memory to the specified string
 {my ($String, @variables) = @_;                                                # String descriptor, variables
  @_ >= 3 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Append completed successfully
    my $Z       = V(zero, 0);                                                   # Zero
    my $O       = V(one,  1);                                                   # One
    my $L       = V(size, $String->length);                                     # Length of a full block
    my $B       = $$p{bs};                                                      # Underlying string
    my $source  = $$p{source};                                                  # Address of content to be appended
    my $size    = $$p{size};                                                    # Size of content
    my $first   = $$p{first};                                                   # First (preallocated) block in string

    PushR my @save = (zmm29, zmm30, zmm31);
    ForEver                                                                     # Append content until source exhausted
     {my ($start, $end) = @_;                                                   # Parameters
      $String->getBlock($B, $first, 29);                                        # Get the first block
      my ($second, $last) = $String->getNextAndPrevBlockOffsetFromZmm(29);      # Get the offsets of the second and last blocks
      $String->getBlock($B, $last,  31);                                        # Get the last block
      my $lengthLast      = $String->getBlockLength(31);                        # Length of last block
      my $spaceLast       = $L - $lengthLast;                                   # Space in last block
      my $toCopy          = $spaceLast->min($size);                             # Amount of data required to fill first block
      my $startPos        = $O + $lengthLast;                                   # Start position in zmm
      $source->setZmm(31, $startPos, $toCopy);                                  # Append bytes
      $String->setBlockLengthInZmm($lengthLast + $toCopy, 31);                  # Set the length
      $String->putBlock($B, $last, 31);                                         # Put the block
      If ($size <= $spaceLast, sub {Jmp $end});                                 # We are finished because the last block had enough space

      $source += $toCopy;                                                       # Remaining source
      $size   -= $toCopy;                                                       # Remaining source length

      my $new = $String->allocBlock;                                            # Allocate new block
      $String->getBlock  ($B, $new, 30);                                        # Load the new block
      my ($next, $prev) = $String->getNextAndPrevBlockOffsetFromZmm(31);        # Linkage from last block

      If ($first == $last,
      Then                                                                      # The existing string has one block, add new as the second block
        {$String->putNextandPrevBlockOffsetIntoZmm(31, $new,  $new);
         $String->putNextandPrevBlockOffsetIntoZmm(30, $last, $last);
        },
      Else                                                                      # The existing string has two or more blocks
       {$String->putNextandPrevBlockOffsetIntoZmm(31, $new,    $prev);          # From last block
        $String->putNextandPrevBlockOffsetIntoZmm(30, $next,   $last);          # From new block
        $String->putNextandPrevBlockOffsetIntoZmm(29, undef,   $new);           # From first block
        $String->putBlock($B, $first, 29);                                      # Put the modified last block
        });

      $String->putBlock($B, $last, 31);                                         # Put the modified last block
      $String->putBlock($B, $new,  30);                                         # Put the modified new block
     };
    PopR @save;
   }  in => [qw(first source size)], io => [qw(bs)];

  $s->call($String->address, $String->first, @variables);
 }

sub Nasm::X86::String::clear($)                                                 # Clear the block by freeing all but the first block
 {my ($String) = @_;                                                            # String descriptor
  @_ == 1 or confess;

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    PushR my @save = (rax, r14, r15, zmm29, zmm30, zmm31);

    my $first = $$p{first};                                                     # First block
    $String->getBlock($$p{bs}, $$p{first}, 29);                                 # Get the first block
    my ($second, $last) = $String->getNextAndPrevBlockOffsetFromZmm(29);        # Get the offsets of the second and last blocks
    ClearRegisters zmm29;                                                       # Clear first block
    $String->putNextandPrevBlockOffsetIntoZmm(29, $first, $first);              # Initialize block chain
    $String->putBlock($$p{bs}, $first, 29);                                     # Put the first block

    If ($last != $first,
    Then                                                                        # Two or more blocks on the chain
     {$$p{bs}->setReg(rax);                                                     # Address underlying arena
      Lea r14, $String->bs->free->addr;                                         # Address of address of free chain
      Mov r15, "[r14]";                                                         # Address of free chain
      my $rfc = V('next', r15);                                                 # Remainder of the free chain

      If ($second == $last,
      Then                                                                      # Two blocks on the chain
       {ClearRegisters zmm30;                                                   # Second block
        $String->putNextandPrevBlockOffsetIntoZmm(30, $rfc, undef);             # Put second block on head of the list
        $String->putBlock($$p{bs}, $second, 30);                                # Put the second block
       },
      Else                                                                      # Three or more blocks on the chain
       {my $z = V(zero, 0);                                                     # A variable with zero in it
        $String->getBlock($$p{bs}, $second, 30);                                # Get the second block
        $String->getBlock($$p{bs}, $last,   31);                                # Get the last block
        $String->putNextandPrevBlockOffsetIntoZmm(30, undef, $z);               # Reset prev pointer in second block
        $String->putNextandPrevBlockOffsetIntoZmm(31, $rfc, undef);             # Reset next pointer in last block to remainder of free chain
        $String->putBlock($$p{bs}, $second, 30);                                # Put the second block
        $String->putBlock($$p{bs}, $last, 31);                                  # Put the last block
       }),

      KeepFree        r15;                                                      # Put the second block at the top of the free chain
      $second->setReg(r15);
      Mov  "[r14]",   r15;
     });

    PopR @save;
   }  in => [qw(first )], io => [qw(bs)];

  $s->call($String->address, $String->first);
 }

#D1 Array                                                                       # Array constructed as a set of blocks in an arena

sub Nasm::X86::Arena::CreateArray($)                                            # Create a array in an arena
 {my ($arena) = @_;                                                             # Arena description
  @_ == 1 or confess;
  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  Comment "Allocate a new array in an arena";

  my $p = 0;                                                                    # Position in block
  my $s = genHash(__PACKAGE__."::Array",                                        # String definition
    bs     => $arena,                                                           # Bytes string definition
    width  => $o,                                                               # Width of each element
    first  => V('first'),                                                       # Variable addressing first block in string
    slots1 => $b / $o - 1,                                                      # Number of slots in first block
    slots2 => $b / $o,                                                          # Number of slots in second and subsequent blocks
   );
  $s->slots2 == 16 or confess "Number of slots per block not 16";               # Slots per block

  my $first = $s->allocBlock;                                                   # Allocate first block
  $s->first->copy($first);                                                      # Save first block
  $s                                                                            # Description of array
 }

sub Nasm::X86::Array::address($)                                                #P Address of a string
 {my ($Array) = @_;                                                             # Array descriptor
  @_ == 1 or confess;
  $Array->bs->bs;
 }

sub Nasm::X86::Array::allocBlock($)                                             #P Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable
 {my ($Array) = @_;                                                             # Array descriptor
  @_ == 1 or confess;

  $Array->bs->allocBlock;
 }

sub Nasm::X86::Array::dump($@)                                                  # Dump a array
 {my ($Array, @variables) = @_;                                                 # Array descriptor, variables
  @_ >= 1 or confess;
  my $b = $Array->bs;                                                           # Underlying arena
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $Array->width;                                                        # The size of an entry in a block
  my $n = $Array->slots1;                                                       # The number of slots per block
  my $N = $Array->slots2;                                                       # The number of slots per block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    my $B = $$p{bs};                                                            # Arena
    my $F = $$p{first};                                                         # First block

    PushR my @save = (zmm30, zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmm(31, 0);                                              # Size of array
    PrintOutStringNL("array");
    $size->out("Size: ", "  ");
    PrintOutRegisterInHex zmm31;

    If ($size > $n,
    Then                                                                        # Array has secondary blocks
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
   }  in => [qw(first)], io => [qw(bs)];

  $s->call($Array->address, $Array->first, @variables);
 }

sub Nasm::X86::Array::push($@)                                                  # Push an element onto the array
 {my ($Array, @variables) = @_;                                                 # Array descriptor, variables
  @_ >= 2 or confess;
  my $b = $Array->bs;                                                           # Underlying arena
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $Array->width;                                                        # The size of an entry in a block
  my $n = $Array->slots1;                                                       # The number of slots per block
  my $N = $Array->slots2;                                                       # The number of slots per block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Arena
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element to be inserted

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmm(31, 0);                                              # Size of array

    If ($size < $n,
    Then                                                                        # Room in the first block
     {$E       ->putDIntoZmm(31, ($size + 1) * $w);                             # Place element
      ($size+1)->putDIntoZmm(31, 0);                                            # Update size
      $b       ->putBlock($B, $F, 31);                                          # Put the first block back into memory
      Jmp $success;                                                             # Element successfully inserted in first block
     });

    If ($size == $n,
    Then                                                                        # Migrate the first block to the second block and fill in the last slot
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

    If ($size <= $N * ($N - 1),
    Then                                                                        # Still within two levels
     {If ($size % $N == 0,
      Then                                                                      # New secondary block needed
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
   }  in => [qw(first  element)], io => [qw(bs)];

  $s->call($Array->address, $Array->first, @variables);
 }

sub Nasm::X86::Array::pop($@)                                                   # Pop an element from an array
 {my ($Array, @variables) = @_;                                                 # Array descriptor, variables
  @_ >= 2 or confess;
  my $b = $Array->bs;                                                           # Underlying arena
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $Array->width;                                                        # The size of an entry in a block
  my $n = $Array->slots1;                                                       # The number of slots per block
  my $N = $Array->slots2;                                                       # The number of slots per block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Arena
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element being popped

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmm(31, 0);                                              # Size of array

    If ($size > 0,
    Then                                                                        # Array has elements
     {If ($size <= $n,
      Then                                                                      # In the first block
       {$E       ->getDFromZmm(31, $size * $w);                                 # Get element
        ($size-1)->putDIntoZmm(31, 0);                                          # Update size
        $b       ->putBlock($B, $F, 31);                                        # Put the first block back into memory
        Jmp $success;                                                           # Element successfully retrieved from secondary block
       });

      If ($size == $N,
      Then                                                                      # Migrate the second block to the first block now that the last slot is empty
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

      If ($size <= $N * ($N - 1),
      Then                                                                      # Still within two levels
       {If ($size % $N == 1,
        Then                                                                    # Secondary block can be freed
         {PushR my @save = (rax, zmm30);
          my $S = getDFromZmm(31, ($size / $N + 1) * $w);                       # Address secondary block from first block
          $b       ->getBlock($B, $S, 30);                                      # Load secondary block
          $E->getDFromZmm(30, 0);                                               # Get first element from secondary block
          V(zero, 0)->putDIntoZmm(31, ($size / $N + 1) * $w);                   # Zero at offset of secondary block in first block
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
   }  in => [qw(first)], io => [qw(bs)], out => [qw(element )];

  $s->call($Array->address, $Array->first, @variables);
 }

sub Nasm::X86::Array::get($@)                                                   # Get an element from the array
 {my ($Array, @variables) = @_;                                                 # Array descriptor, variables
  @_ >= 3 or confess;
  my $b = $Array->bs;                                                           # Underlying arena
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $Array->width;                                                        # The size of an entry in a block
  my $n = $Array->slots1;                                                       # The number of slots in the first block
  my $N = $Array->slots2;                                                       # The number of slots in the secondary blocks

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Arena
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element to be returned
    my $I = $$p{index};                                                         # Index of the element to be returned

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmm(31, 0);                                              # Size of array

    If ($I < $size,
    Then                                                                        # Index is in array
     {If ($size <= $n,
      Then                                                                      # Element is in the first block
       {$E->getDFromZmm(31, ($I + 1) * $w);                                     # Get element
        Jmp $success;                                                           # Element successfully inserted in first block
       });

      If ($size <= $N * ($N - 1),
      Then                                                                      # Still within two levels
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
   }  in => [qw(first index)], io => [qw(bs)], out => [qw(element )];

  $s->call($Array->address, $Array->first, @variables);
 }

sub Nasm::X86::Array::put($@)                                                   # Put an element into an array as long as it is with in its limits established by pushing.
 {my ($Array, @variables) = @_;                                                 # Array descriptor, variables
  @_ >= 3 or confess;
  my $b = $Array->bs;                                                           # Underlying arena
  my $W = RegisterSize zmm0;                                                    # The size of a block
  my $w = $Array->width;                                                        # The size of an entry in a block
  my $n = $Array->slots1;                                                       # The number of slots in the first block
  my $N = $Array->slots2;                                                       # The number of slots in the secondary blocks

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Arena
    my $F = $$p{first};                                                         # First block
    my $E = $$p{element};                                                       # The element to be added
    my $I = $$p{index};                                                         # Index of the element to be inserted

    PushR my @save = (zmm31);
    $b->getBlock($B, $F, 31);                                                   # Get the first block
    my $size = getDFromZmm(31, 0          );                                    # Size of array
    If ($I < $size,
    Then                                                                        # Index is in array
     {If ($size <= $n,
       Then                                                                     # Element is in the first block
       {$E->putDIntoZmm(31, ($I + 1) * $w);                                     # Put element
        $b->putBlock($B, $F, 31);                                               # Get the first block
        Jmp $success;                                                           # Element successfully inserted in first block
       });

      If ($size <= $N * ($N - 1),
      Then                                                                      # Still within two levels
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
   }  in => [qw(first index element )], io => [qw(bs)];

  $s->call($Array->address, $Array->first, @variables);
 }

#D1 Tree                                                                        # Tree constructed as sets of blocks in an arena.

sub Nasm::X86::Arena::DescribeTree($)                                           # Return a descriptor for a tree in the specified arena
 {my ($arena) = @_;                                                             # Arena descriptor
  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  my $length = $b / $o - 2;                                                     # Length of block to split
  my $split  = $length / 2  * $o;                                               # Offset of splitting key

  confess "Maximum keys must be 14" unless $b / $o - 2 == 14;                   # Maximum number of keys is expected to be 14
  confess "Splitting key offset must be 28" unless $split == 28;                # Splitting key offset

  genHash(__PACKAGE__."::Tree",                                                 # tree.
    bs           => $arena,                                                     # Arena definition.
    data         => V(data),                                                    # Variable containing the last data found
    first        => V(first),                                                   # Variable addressing offset to first block of keys.
    found        => V(found),                                                   # Variable indicating whether the last find was successful or not
    leftLength   => $length / 2,                                                # Left split length
    lengthOffset => $b - $o * 2,                                                # Offset of length in keys block.  The length field is a word - see: "MultiWayTree.svg"
    loop         => $b - $o,                                                    # Offset of keys, data, node loop.
    maxKeys      => $length,                                                    # Maximum number of keys.
    splittingKey => $split,                                                     # POint at which to split a full block
    rightLength  => $length - 1 - $length / 2,                                  # Right split length
    subTree      => V(subTree),                                                 # Variable indicating whether the last find found a sub tree
    treeBits     => $b - $o * 2 + 2,                                            # Offset of tree bits in keys block.  The tree bits field is a word, each bit of which tells us whether the corresponding data element is the offset (or not) to a sub tree of this tree .
    treeBitsMask => 0x3fff,                                                     # 14 tree bits
    up           => $b - $o * 2,                                                # Offset of up in data block.
    width        => $o,                                                         # Width of a key or data slot.
   );
 }

sub Nasm::X86::Arena::CreateTree($)                                             # Create a tree in an arena.
 {my ($arena) = @_;                                                             # Arena description
  @_ == 1 or confess;

  my $t = $arena->DescribeTree;                                                 # Return a descriptor for a tree at the specified offset in the specified arena

  my $s = Subroutine
   {my ($p) = @_;
    Comment "Create a block multiway Tree start";
    my $keys = $t->allocBlock;                                                  # Allocate first keys block
    $$p{first}->copy($keys);
    PushR my @save = (zmm31);
    ClearRegisters zmm31;
    $t->putLoop($t->allocBlock, 31);                                            # Keys loops to data - for the first 7 keys we should store the corresponding data further up in the block rather than creating a new block.
    $arena->putBlock($t->address, $keys, 31);                                   # Write first keys
    PopR @save;
    Comment "Create a block multiway Tree end";
   } io => [qw(bs)], out => [qw(first)];

  $s->call(bs => $t->address, first => $t->first);

  $t                                                                            # Description of array
 }

sub Nasm::X86::Tree::Clone($)                                                   # Clone the specified tree descriptions
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess;

  Comment "Nasm::X86::Tree::Clone";
  my $t = $tree->bs->DescribeTree;                                              # Return a descriptor for a tree
  $t->first->copy($tree->first);
  $t
 }

sub Nasm::X86::Tree::allocKeysDataNode($$$$@)                                   #P Allocate a keys/data/node block and place it in the numbered zmm registers
 {my ($t, $K, $D, $N, @variables) = @_;                                         # Tree descriptor, numbered zmm for keys, numbered zmm for data, numbered zmm for children, variables
  @_ >= 4 or confess;

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters

    my $B = $$parameters{bs};                                                   # Arena
    $t->bs->allocZmmBlock($B, my $k = V(offset));                               # Keys
    $t->bs->allocZmmBlock($B, my $d = V(offset));                               # Data
    $t->bs->allocZmmBlock($B, my $n = V(offset));                               # Children

    $t->putLoop($d, $K);                                                        # Set the link from key to data
    $t->putLoop($n, $D);                                                        # Set the link from data to node
    $t->putLoop($k, $N);                                                        # Set the link from node  to key
   }
  name=>qq(Nasm::X86::Tree::allocKeysDataNode::${K}::${D}::${N}),               # Create a subroutine for each combination of registers encountered
  io => [qw(bs)];

  $s->call($t->address, @variables);
 } # allocKeysDataNode

sub Nasm::X86::Tree::splitNode($$$$@)                                           #P Split a node given its offset in an arena retaining the key being inserted in the node split while putting the remainder to the left or right.
 {my ($t, $bs, $node, $key, @variables) = @_;                                   # Tree descriptor, backing arena, offset of node, key, variables
  @_ >= 4 or confess;

  my $K = 31; my $D = 30; my $N = 29;                                           # Key, data, node blocks

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $b = $$parameters{bs};                                                   # Arena
    my $k = $$parameters{key};                                                  # Key we are looking for
    my $n = $$parameters{node};                                                 # Node to split

    PushR my @save = (r8, zmm 22..31);
    my $transfer = r8;                                                          # Use this register to transfer data between zmm blocks and variables
    $t->getKeysDataNode($n, $K, $D, $N);                                        # Load root node

    If ($t->getLengthInKeys($K) != $t->maxKeys,
    Then                                                                        # Only split full blocks
     {Jmp $success;
     });

    my $p = $t->getUpFromData($D);                                              # Parent
    If ($p,
    Then                                                                        # Not the root
     {my $s = getDFromZmm $K, $t->splittingKey, $transfer;                      # Splitting key
      If ($k < $s,
      Then                                                                      # Split left node pushing remainder right so that we keep the key we are looking for in the left node
       {Vmovdqu64 zmm28, zmm31;                                                 # Load left node
        Vmovdqu64 zmm27, zmm30;
        Vmovdqu64 zmm26, zmm29;
        $t->allocKeysDataNode(25, 24, 23);                                      # Create new right node

        KeepFree zmm $N;                                                        # Reloading root
        $t->getKeysDataNode($p, $K, $D, $N);                                    # Load parent
        $t->splitFullLeftNode;
        $t->putKeysDataNode($p, $K, $D, $N);                                    # Save parent
        $t->putKeysDataNode($n, 28, 27, 26);                                    # Save left
        my $r = $t->getLoop    (23, $transfer);                                 # Offset of right keys
        $t->putUpIntoData  ($p, 24);                                            # Reparent new block
        $t->putKeysDataNode($r, 25, 24, 23);                                    # Save right back into node we just split
       },
      Else                                                                      # Split right node pushing remainder left  so that we keep the key we are looking for in the right node
       {Vmovdqu64 zmm25, zmm31;                                                 # Load right node
        Vmovdqu64 zmm24, zmm30;
        Vmovdqu64 zmm23, zmm29;
        $t->allocKeysDataNode(28, 27, 26);                                      # Create new left node

        KeepFree zmm $N;                                                        # Reloading root
        $t->getKeysDataNode($p, $K, $D, $N);                                    # Load parent
        $t->splitFullRightNode;
        $t->putKeysDataNode($p, $K, $D, $N);                                    # Save parent
        my $l = $t->getLoop    (26, $transfer);                                 # Offset of left keys
        $t->putUpIntoData  ($p, 27);                                            # Reparent new block
        $t->putKeysDataNode($l, 28, 27, 26);                                    # Save left
        $t->putKeysDataNode($n, 25, 24, 23);                                    # Save right back into node we just split
       });
     },
    Then
     {$t->splitFullRoot;                                                        # Root
      my $l = getDFromZmm $N, 0,         $transfer;
      my $r = getDFromZmm $N, $t->width, $transfer;
      $t->putKeysDataNode($n, $K, $D, $N);                                      # Save root
      $t->putKeysDataNode($l, 28, 27, 26);                                      # Save left
      $t->putKeysDataNode($r, 25, 24, 23);                                      # Save right
     });

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in => [qw(node key)], io => [qw(bs)];

  $s->call(bs=>$bs, node=>$node, key=>$key, @variables);
 } # splitNode

sub Nasm::X86::Tree::reParent($$$$$@)                                           #P Reparent the children of a node held in registers. The children are in the backing arena not registers.
 {my ($t, $bs, $PK, $PD, $PN, @variables) = @_;                                 # Tree descriptor, backing arena, numbered zmm key node, numbered zmm data node, numbered zmm child node, variables
  @_ >= 5 or confess;
  my $b = $t->bs;                                                               # Underlying arena

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters

    my $B = $$parameters{bs};                                                   # Arena
    my $L = $t->getLengthInKeys($PK) + 1;                                       # Number of children
    my $p = $t->getUpFromData ($PD);                                            # Parent node offset as a variable

    If ($t->getLoop($PD), sub                                                   # Not a leaf
     {PushR my @save = (rax, rdi);
      Mov rdi, rsp;                                                             # Save stack base
      PushRR "zmm$PN";                                                          # Child nodes on stack
      my $w = $t->width; my $l = $t->loop; my $u = $t->up;                      # Steps we will make along the chain
      my $s = V(start);
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
   } io => [qw(bs)];

  $s->call($t->address, @variables);
 } # reParent

sub Nasm::X86::Tree::transferTreeBitsFromParent($$$$)                           #P Transfer tree bits when splitting a full node.
 {my ($b, $parent, $left, $right) = @_;                                         # Tree descriptor, numbered parent zmm, numbered left zmm, numbered right zmm

  PushR my @save = my ($whole, $half)  = (r15, r14);
  $b->getTreeBits($parent, $whole);                                             # Transfer Tree bits
  Cmp $whole, 0;
  IfNz                                                                          # Action required iff there are some tree bits
  Then
   {Mov $half, $whole;                                                          # Left tree bits
    And $half, ((1 << $b->leftLength) - 1);                                     # Isolate left bits
    $b->putTreeBits($left, $half);                                              # Save left tree bits

    Mov $half, $whole;                                                          # Right tree bits
    Shr $half, $b->leftLength + 1;                                              # Isolate right bits
    And  $half, ((1 << $b->rightLength) - 1);                                   # Remove any bits above
    $b->putTreeBits($right, $half);                                             # Save right tree bits

    Mov $half, $whole;                                                          # Right tree bits
    Shr $half, $b->leftLength;                                                  # Parent bit
    And $half, 1;                                                               # Only one bit
    $b->putTreeBits($parent, $half);                                            # Save parent tree bits
   };
  PopR @save;
 }

sub Nasm::X86::Tree::transferTreeBitsFromLeftOrRight($$$$$$)                    #P Transfer tree bits when splitting a full left or right node.
 {my ($b, $rnl, $point, $parent, $left, $right) = @_;                           # Tree descriptor, 0 - left 1 - right, register indicating point of left in parent, numbered parent zmm, numbered left zmm, numbered right zmm

  PushR my @save = my ($whole, $half, $bits) = ChooseRegisters(3, $point);
  $b->getTreeBits($rnl ? $right : $left, $whole);                               # Tree bits

  Mov $half, $whole;                                                            # Right bits
  Shr $half, $b->leftLength + 1;                                                # Isolate right bits
  $b->putTreeBits($right, $half);                                               # Save right bits

  $b->getTreeBits($parent, $bits);                                              # Parent bits
  InsertZeroIntoRegisterAtPoint($point, $bits);
  Mov $half, $whole;                                                            # Tree bit of key being moved into parent from left
  Shr $half, $b->leftLength+1;                                                  # Tree bit to move into parent is now in carry flag
  IfC Then {Or $bits, $point};                                                  # One parent bit
  $b->putTreeBits($parent, $bits);                                              # Put parent tree bits

  Mov $half, $whole;                                                            # Left bits
  And $half, ((1 << $b->leftLength) - 1);                                       # Remove any bits above
  $b->putTreeBits($left, $half);                                                # Save left bits
  PopR @save;
 }

sub Nasm::X86::Tree::transferTreeBitsFromLeft($$$$$)                            #P Transfer tree bits when splitting a full left node
 {my ($b, $point, $parent, $left, $right) = @_;                                 # Tree descriptor, register indicating point of left in parent, numbered parent zmm, numbered left zmm, numbered right zmm
  $b->transferTreeBitsFromLeftOrRight(0, $point, $parent, $left, $right);
 }

sub Nasm::X86::Tree::transferTreeBitsFromRight($$$$$)                           #P Transfer tree bits when splitting a full right node
 {my ($b, $point, $parent, $left, $right) = @_;                                 # Tree descriptor, register indicating point of right in parent, numbered parent zmm, numbered left zmm, numbered right zmm
  $b->transferTreeBitsFromLeftOrRight(1, $point, $parent, $left, $right);
 }

sub Nasm::X86::Tree::splitFullRoot($)                                           #P Split a full root block held in 31..29 and place the left block in 28..26 and the right block in 25..23. The left and right blocks should have their loop offsets set so they can be inserted into the root.
 {my ($t) = @_;                                                                 # Tree descriptor
  @_ == 1 or confess;

  my $length = $t->maxKeys;                                                     # Length of block to split
  my $ll = $t->leftLength;                                                      # Left split point
  my $rl = $t->rightLength;                                                     # Right split point

  my $TK = 31; my $TD = 30; my $TN = 29;                                        # Root key, data, node
  my $LK = 28; my $LD = 27; my $LN = 26;                                        # Key, data, node blocks in left child
  my $RK = 25; my $RD = 24; my $RN = 23;                                        # Key, data, node blocks in right child
  my $Test = 22;                                                                # Zmm used to hold test values via broadcast

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push
    my $B = $$parameters{bs};

    PushR my @save = (k6, k7, r8, zmm22);
    my $transfer = r8;                                                          # Use this register to transfer data between zmm blocks and variables

    If ($t->getLengthInKeys($TK) != $t->maxKeys, sub {Jmp $success});           # Only split full blocks

    $t->allocKeysDataNode(  28, 27, 26);                                        # Allocate immediate children of the root
    my $l = $t->getLoop(            26, $transfer);
    $t->putKeysDataNode($l, 28, 27, 26);
    $t->allocKeysDataNode  (25, 24, 23);
    my $r = $t->getLoop            (23, $transfer);
    $t->putKeysDataNode($l, 25, 24, 23);
    $t->reParent       ($B, 28, 27, 26);                                        # Reparent grandchildren
    $t->reParent       ($B, 25, 24, 23);

    my $n  = $t->getLoop($TD, $transfer);                                       # Offset of node block or zero if there is no node block
    my $to = $t->getLoop($TN, $transfer);                                       # Offset of root block
    my $lo = $t->getLoop($LN, $transfer);                                       # Offset of left block
    my $ro = $t->getLoop($RN, $transfer);                                       # Offset of right block

    LoadBitsIntoMaskRegister(k7, "11",-$length);                                # Area to clear preserving loop and up/length
    &Vmovdqu32   (zmm $LK."{k7}{z}",   $LK);                                    # Clear left
    &Vmovdqu32   (zmm $LD."{k7}{z}",   $LD);
    &Vmovdqu32   (zmm $RK."{k7}{z}",   $RK);                                    # Clear right
    &Vmovdqu32   (zmm $RD."{k7}{z}",   $RD);

    LoadBitsIntoMaskRegister(k7, "10" -$length);                                # Area to clear preserving loop
    &Vmovdqu32   (zmm $LN."{k7}{z}",   $LN);                                    # Clear left
    &Vmovdqu32   (zmm $RK."{k7}{z}",   $RK);                                    # Clear right

    LoadBitsIntoMaskRegister(k7, "",  +$ll);                                    # Constant mask up to the split point
    &Vmovdqu32   (zmm $LK."{k7}",      $TK);                                    # Split keys left
    &Vmovdqu32   (zmm $LD."{k7}",      $TD);                                    # Split data left
    If ($n, sub  {&Vmovdqu32 (zmm $LN."{k7}", $TN)});                           # Split nodes left

    LoadBitsIntoMaskRegister(k6, '',  +$rl, -($ll+1));                          # Constant mask from one beyond split point to end of keys
    Kshiftrq k7, k6, $ll+1;                                                     # Constant mask for compressed right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $TK);                                    # Split right keys
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right keys
    &Vmovdqu32   (zmm $RK.  "{k7}",    $Test);                                  # Save right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $TD);                                    # Split right data
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right data
    &Vmovdqu32   (zmm $RD.  "{k7}",    $Test);                                  # Save right data

    If ($n,
    Then                                                                        # Split nodes right
     {&Vmovdqu32   (zmm $Test."{k6}{z}", $TN);                                  # Split right nodes
      &Vpcompressd (zmm $Test."{k6}",    $Test);                                # Compress right node
      &Vmovdqu32   (zmm $RN.  "{k7}",    $Test);                                # Save right node
     });

    my $k = getDFromZmm $TK, $ll * (my $w = $t->width), $transfer;              # Splitting key
    my $d = getDFromZmm $TD, $ll * $w,                  $transfer;              # Splitting data

    LoadConstantIntoMaskRegister(k7, 1);                                        # Position of key, data in root node
    $k->zBroadCastD($Test);                                                     # Broadcast keys
    &Vmovdqu32 (zmm $TK."{k7}",  $Test);                                        # Insert key in root
    $d->zBroadCastD($Test);                                                     # Broadcast keys
    &Vmovdqu32 (zmm $TD."{k7}",  $Test);                                        # Insert data in root
    LoadBitsIntoMaskRegister(k7, "11", -($length-1), 1);                        # Unused fields
    &Vmovdqu32 (zmm $TK."{k7}{z}",  $TK);                                       # Clear unused keys in root
    &Vmovdqu32 (zmm $TD."{k7}{z}",  $TD);                                       # Clear unused data in root

    If ($n,
    Then
     {LoadBitsIntoMaskRegister(k7, "1", -$length, 1);                           # Unused fields
      &Vmovdqu32 (zmm $TN."{k7}{z}",  $TN);                                     # Clear unused node in root
     });

    $t->putLengthInKeys($TK, K(one,  1));                                       # Set length of root keys
    $t->putLengthInKeys($LK, K(leftLength,  $ll));                              # Length of left node
    $t->putLengthInKeys($RK, K(rightLength, $rl));                              # Length of right node

    $t->putUpIntoData($to, $LD);                                                # Set parent of left node
    $t->putUpIntoData($to, $RD);                                                # Set parent of right node

    $lo->putDIntoZmm($TN, 0);                                                   # Insert offset of left node in root nodes
    $ro->putDIntoZmm($TN, $w);                                                  # Insert offset of right node in root nodes

    $t->transferTreeBitsFromParent($TK, $LK, $RK);                              # Transfer any tree bits present

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   } io =>[qw(bs)];

  $s->call (bs => $t->address);
 } # splitFullRoot

sub Nasm::X86::Tree::splitFullLeftOrRightNode($$)                               #P Split a full a full left node (held in 28..26) or a full right node (held in 25..23) whose parent is in 31..29.
 {my ($t, $right) = @_;                                                         # Tree descriptor,  0 left or 1 right
  @_ == 2 or confess;

  my $length = $t->maxKeys;                                                     # Length of block to split
  my $ll = $t->leftLength;                                                      # Left split point
  my $rl = $t->rightLength;                                                     # Right split point

  my $PK = 31; my $PD = 30; my $PN = 29;                                        # Root key, data, node. These registers are saved in L<splitNode>
  my $LK = 28; my $LD = 27; my $LN = 26;                                        # Key, data, node blocks in left child
  my $RK = 25; my $RD = 24; my $RN = 23;                                        # Key, data, node blocks in right child
  my $Test = 22;                                                                # Zmm used to hold test values via broadcast

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    PushR my @save = (r8);
    my $transfer = r8;                                                          # Use this register to transfer data between zmm blocks and variables

    If ($t->getLengthInKeys($right ? $RK : $LK) != $t->maxKeys,                 # Only split full blocks
    Then {Jmp $success});

    my $n  = $t->getLoop($right ? $RD : $LD, $transfer);                        # Offset of node block or zero if there is no node block for the right node
    my $lo = $t->getLoop($LN, $transfer);                                       # Offset of left block
    my $ro = $t->getLoop($RN, $transfer);                                       # Offset of right block

    if ($right)
     {LoadBitsIntoMaskRegister(k7, "00", +$length);                             # Left mask for keys and data
      &Vmovdqu32(zmm $LK."{k7}", $RK);                                          # Copy right keys  to left node
      &Vmovdqu32(zmm $LD."{k7}", $RD);                                          # Copy right data  to left node
      LoadBitsIntoMaskRegister(k7, "01", +$length);                             # Left mask for child nodes
      &Vmovdqu32(zmm $LN."{k7}", $RN);                                          # Copy right nodes to left node
     }

    my $k = getDFromZmm $LK, $ll * (my $w = $t->width), $transfer;              # Splitting key
    my $d = getDFromZmm $LD, $ll * $w,                  $transfer;              # Splitting data

    LoadBitsIntoMaskRegister(k6, '', +$rl, -($ll+1));                           # Constant mask from one beyond split point to end of keys
    Kshiftrq k7, k6, $ll+1;                                                     # Constant mask for compressed right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $LK);                                    # Split out right keys
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right keys
    &Vmovdqu32   (zmm $RK.  "{k7}",    $Test);                                  # Save right keys

    &Vmovdqu32   (zmm $Test."{k6}{z}", $LD);                                    # Split out right data
    &Vpcompressd (zmm $Test."{k6}",    $Test);                                  # Compress right data
    &Vmovdqu32   (zmm $RD.  "{k7}",    $Test);                                  # Save right data

    If ($n,
    Then                                                                        # Split nodes right
     {&Vmovdqu32   (zmm $Test."{k6}{z}", $LN);                                  # Split right nodes
      &Vpcompressd (zmm $Test."{k6}",    $Test);                                # Compress right node
      &Vmovdqu32   (zmm $RN.  "{k7}",    $Test);                                # Save right node
     });

    if ($right)
     {LoadBitsIntoMaskRegister(k7, '11', -($rl+2), +($ll-1));                   # Areas to retain
      LoadBitsIntoMaskRegister(k6, '11', -($rl+1),  +$ll);

      &Vmovdqu32   (zmm $RK."{k7}{z}",   $RK);                                  # Remove unused keys on right
      &Vmovdqu32   (zmm $RD."{k7}{z}",   $RD);                                  # Remove unused data on right

      If ($n,
      Then                                                                      # Split nodes left
       {LoadBitsIntoMaskRegister(k7, '10', -($rl+2), +($ll-1));
        &Vmovdqu32 (zmm $RN."{k7}{z}",   $RN);
       });

      &Vmovdqu32   (zmm $LK."{k6}{z}",   $LK);                                  # Remove unused keys on left
      &Vmovdqu32   (zmm $LD."{k6}{z}",   $LD);                                  # Remove unused data on left

      If ($n,
      Then                                                                      # Split nodes left
       {LoadBitsIntoMaskRegister(k6, '10', -($rl+1), +$ll);
        &Vmovdqu32 (zmm $LN."{k6}{z}",   $LN);
       });
     }
    else
     {LoadBitsIntoMaskRegister(k7, "11", -($rl+1), +$ll);                       # Mask to reset moved keys

      &Vmovdqu32   (zmm $LK."{k7}{z}",   $LK);                                  # Remove unused keys
      &Vmovdqu32   (zmm $LD."{k7}{z}",   $LD);                                  # Split data left
      If ($n,
      Then                                                                      # Split nodes left
       {LoadBitsIntoMaskRegister(k7, '10', -($rl+1), +$ll);
        &Vmovdqu32 (zmm $LN."{k7}{z}",   $LN);
       });
     }
    ($right ? $ro : $lo)->zBroadCastD($Test);                                   # Find index in parent of left node - broadcast offset of left node so we can locate it in the parent
    LoadBitsIntoMaskRegister(k7, '', +$length);                                 # Nodes
    &Vpcmpud("k6{k7}", zmm($PN, $Test), 0);                                     # Check for equal offset - one of them will match to create the single insertion point in k6

    Kandnq k5, k6, k7;                                                          # Expansion mask
    &Vpexpandd (zmm $PK."{k5}", $PK);                                           # Shift up keys
    &Vpexpandd (zmm $PD."{k5}", $PD);                                           # Shift up keys
    $k->zBroadCastD($Test);                                                     # Broadcast new key
    &Vmovdqu32 (zmm $PK."{k6}", $Test);                                         # Insert new key
    $d->zBroadCastD($Test);                                                     # Broadcast new data
    &Vmovdqu32 (zmm $PD."{k6}", $Test);                                         # Insert new data

    Kmovq r15, k6;                                                              # Point at which to insert in parent
    $t->transferTreeBitsFromLeftOrRight($right, r15, $PK, $LK, $RK);

    If ($n,
    Then                                                                        # Insert new left node offset into parent nodes
     {Kshiftlq k6, k6, 1 unless $right;                                         # Node insertion point
      Kandnq k5, k6, k7;                                                        # Expansion mask
      &Vpexpandd (zmm $PN."{k5}", $PN);                                         # Shift up nodes
      ($right ? $lo : $ro)->zBroadCastD($Test);                                 # Broadcast left node offset
      &Vmovdqu32 (zmm $PN."{k6}", $Test);                                       # Insert right node offset
     });

    my $l = $t->getLengthInKeys($PK);                                           # Length of parent
            $t->putLengthInKeys($PK, $l + 1);                                   # New length of parent
    $t->putLengthInKeys($LK, K(leftLength,  $ll));                              # Length of left node
    $t->putLengthInKeys($RK, K(rightLength, $rl));                              # Length of right node

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   } name => "splitFullLeftOrRightNode_$right";

  $s->call;
 } # splitFullLeftOrRightNode

sub Nasm::X86::Tree::splitFullLeftNode($)                                       #P Split a full left node block held in 28..26 whose parent is in 31..29 and place the new right block in 25..23. The parent is assumed to be not full. The loop and length fields are assumed to be authoritative and hence are preserved.
 {my ($t) = @_;                                                                 # Tree descriptor
  @_ == 1 or confess;
  $t->splitFullLeftOrRightNode(0);
 }

sub Nasm::X86::Tree::splitFullRightNode($)                                      #P Split a full right node block held in 25..23 whose parent is in 31..29 and place the new left block in 28..26.  The loop and length fields are assumed to be authoritative and hence are preserved.
 {my ($t) = @_;                                                                 # Tree descriptor
  @_ == 1 or confess;
  $t->splitFullLeftOrRightNode(1);
 }

sub Nasm::X86::Tree::findAndSplit($@)                                           #P Find a key in a tree which is known to contain at least one key splitting full nodes along the path to the key.
 {my ($t, @variables) = @_;                                                     # Tree descriptor, variables
  @_ >= 3 or confess;
  my $W = $t->width;                                                            # Width of keys and data

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Arena
    my $F = $$p{first};                                                         # First keys block
    my $K = $$p{key};                                                           # Key to find

    my $tree = $F->clone;                                                       # Start at the first key block
    PushR my @save = (k6, k7, r8, r14, r15, zmm28, zmm29, zmm30, zmm31);
    my $zmmKeys = 31; my $zmmData = 30; my $zmmNode = 29; my $zmmTest = 28;
    my $lengthMask = k6; my $testMask = k7;
    my $transfer = r8;                                                          # Use this register to transfer data between zmm blocks and variables

    $K->setReg(r15);                                                            # Load key into test register
    Vpbroadcastd "zmm$zmmTest", r15d;
    KeepFree r15;

    $t->splitNode($B, $F, $K);                                                  # Split the root

    ForEver                                                                     # Step down through tree
     {my ($start, $end) = @_;                                                   # Parameters
      $t->getKeysDataNode($tree, $zmmKeys, $zmmData, $zmmNode);                 # Get the keys/data/nodes block
      my $node = getDFromZmm $zmmNode, 0, $transfer;                            # First element of node block, which will be zero if we are on a leaf

      my $l = $t->getLengthInKeys($zmmKeys);                                    # Length of the block
      $l->setMaskFirst($lengthMask);                                            # Set the length mask
      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmKeys", "zmm$zmmTest", 0;       # Check for equal elements
      Ktestw   $testMask, $testMask;
      IfNz                                                                      # Result mask is non zero so we must have found the key
      Then
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros gives index
        $$p{compare}->copy(K(zero, 0));                                         # Key found
        $$p{index}  ->getReg(r14);                                              # Index from trailing zeros
        $$p{offset} ->copy($tree);                                              # Offset of matching block
        Jmp $success;                                                           # Return
       };

      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmTest", "zmm$zmmKeys", 1;       # Check for greater elements
      Ktestw   $testMask, $testMask;
      IfNz                                                                      # Non zero implies that the key is less than some of the keys in the block
      Then
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros
        If ($node == 0,
        Then                                                                    # We are on a leaf
         {$$p{compare}->copy(K(minusOne, -1));                                  # Key less than
          $$p{index}  ->getReg(r14);                                            # Index from trailing zeros
          $$p{offset} ->copy($tree);                                            # Offset of matching block
          Jmp $success;                                                         # Return
         });
        $tree->copy(getDFromZmm $zmmNode, "r14*$W", $transfer);                 # Corresponding node
        Jmp $start;                                                             # Loop
       };

      if (1)                                                                    # Key greater than all keys in block
       {If ($node == 0,
        Then                                                                    # We have reached a leaf
         {$$p{compare}->copy(K(plusOne, +1));                                   # Key greater than last key
          $$p{index}  ->copy($l-1);                                             # Index of last key which we are greater than
          $$p{offset} ->copy($tree);                                            # Offset of matching block
          Jmp $success
         });
       };
      $tree->copy(getDFromZmm $zmmNode, $l * $t->width, $transfer);             # Greater than all keys so step through last child node
     };

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in => [qw(first key)], io => [qw(bs)], out => [qw(compare offset index)];

  $s->call($t->address, first => $t->first, @variables);
 } # findAndSplit

sub Nasm::X86::Tree::find($$)                                                   # Find a key in a tree and test whether the found data is a sub tree.  The results are held in the variables "found", "data", "subTree" addressed by the tree descriptor.
 {my ($t, $key) = @_;                                                           # Tree descriptor, key field to search for
  @_ == 2 or confess;
  my $W = $t->width;                                                            # Width of keys and data

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $F = $$p{first};                                                         # First keys block
    my $K = $$p{key};                                                           # Key to find

    $$p{found}  ->copy(K(zero, 0));                                             # Key not found
    $$p{data}   ->copy(K(zero, 0));                                             # Data not yet found
    $$p{subTree}->copy(K(zero, 0));                                             # Not yet a sub tree

    my $tree = $F->clone;                                                       # Start at the first key block
    PushR my @save = (k6, k7, r8, r14, r15, zmm28, zmm29, zmm30, zmm31);
    my $zmmKeys = 31; my $zmmData = 30; my $zmmNode = 29; my $zmmTest = 28;
    my $lengthMask = k6; my $testMask = k7;
    my $transfer = r8;                                                          # Use this register to transfer data between zmm blocks and variables

    $K->setReg(r15);                                                            # Load key into test register
    Vpbroadcastd "zmm$zmmTest", r15d;
    KeepFree r15;

    K(loop, 99)->for(sub                                                        # Step down through tree
     {my ($index, $start, $next, $end) = @_;
      $t->getKeysDataNode($tree, $zmmKeys, $zmmData, $zmmNode);                 # Get the keys block
      my $l = $t->getLengthInKeys($zmmKeys);                                    # Length of the block
      If ($l == 0,
      Then                                                                      # Empty tree so we have not found the key
       {Jmp $success;                                                           # Return
       });

      $l->setMaskFirst($lengthMask);                                            # Set the length mask
      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmKeys", "zmm$zmmTest", 0;       # Check for equal elements
      Ktestw   $testMask, $testMask;
      IfNz                                                                      # Result mask is non zero so we must have found the key
      Then
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros
        $$p{found}->copy(K(one, 1));                                            # Key found
        $$p{data} ->copy(getDFromZmm $zmmData, "r14*$W", $transfer);            # Data associated with the key
        $t->isTree(r15, $zmmKeys);                                              # Check whether the data so found is a sub tree
        $$p{subTree}->copyZFInverted;                                           # Copy zero flag which opposes the notion that this element is a sub tree
        Jmp $success;                                                           # Return
       };

      my $n = getDFromZmm $zmmNode, 0, $transfer;                               # First child empty implies we are on a leaf
      If ($n == 0,
      Then                                                                      # Zero implies that this is a leaf node
       {Jmp $success;                                                           # Return
       });

      Vpcmpud "$testMask\{$lengthMask}", "zmm$zmmTest", "zmm$zmmKeys", 1;       # Check for greater elements
      Ktestw   $testMask, $testMask;

      IfNz                                                                      # Non zero implies that the key is less than some of the keys
      Then
       {Kmovq r15, $testMask;
        Tzcnt r14, r15;                                                         # Trailing zeros
        $tree->copy(getDFromZmm $zmmNode, "r14*$W", $transfer);                 # Corresponding node
        Jmp $next;                                                              # Loop
       };
      $tree->copy(getDFromZmm $zmmNode, $l * $W, $transfer);                    # Greater than all keys
     });
    PrintErrStringNL "Stuck in find";                                           # We seem to be looping endlessly
    Exit(1);

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in  => [qw(first key)],  out => [qw(data found data subTree)];

  $s->call(first => $t->first, key => $key, data => $t->data,
           found => $t->found, subTree => $t->subTree);
 } # find

sub Nasm::X86::Tree::findAndClone($$)                                           # Find a key in the specified tree and clone it is it is a sub tree.
 {my ($t, $key) = @_;                                                           # Tree descriptor, key as a dword
  @_ == 2 or confess;
  Comment "Nasm::X86::Tree::findAndClone";
  $t->find($key);
  If ($t->found,
  Then
   {$t->first->copy($t->data);                                                  # Copy the data variable to the first variable without checking whether it is valid
   });
 }

sub Nasm::X86::Tree::insertDataOrTree($$$$)                                     # Insert either a key, data pair into the tree or create a sub tree at the specified key (if it does not already exist) and return the offset of the first block of the sub tree in the data variable.
 {my ($t, $tnd, $key, $data) = @_;                                              # Tree descriptor, 0 - data or 1 - tree, key as a dword, data as a dword
  @_ >= 2 or confess;
  my $b = $t->bs;                                                               # Underlying arena
  my $W = RegisterSize zmm0;                                                    # The size of a block

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $B = $$p{bs};                                                            # Arena
    my $F = $$p{first};                                                         # First keys block
    my $K = $$p{key};                                                           # Key  to be inserted
    my $D = $$p{data};                                                          # Data to be inserted

    PushR my @save = (k4, k5, k6, k7, r13, r14, r15, zmm 22..31);
    my $point = r13;                                                            # Insertion indicator
    $t->getKeysDataNode($F, 31, 30, 29);                                        # Get the first block

    my $l = $t->getLengthInKeys(31);                                            # Length of the block
    If ($l == 0,                                                                # Check for  empty tree.
    Then                                                                        # Empty tree
     {$K->putDIntoZmm    (31, 0);                                               # Write key
      $t->putLengthInKeys(31, K(one, 1));                                       # Set the length of the block
      if ($tnd)                                                                 # Create and mark key as addressing a sub tree
       {$D->copy($t->bs->CreateTree->first) if $tnd == 1;                       # Create sub tree in the same arena as parent tree if requested
        Mov r15, 1;                                                             # Indicate first position
        $t->setTree(r15,  31);                                                  # Mark this key as addressing a sub tree from the existing tree
       }
      $D->putDIntoZmm    (30, 0);                                               # Write data
      $t->putKeysData($F, 31, 30);                                              # Write the data block back into the underlying arena
      Jmp $success;                                                             # Insert completed successfully
     });

    my $n = $t->getLoop(30);                                                    # Get the offset of the node block
    If (($n == 0) & ($l < $t->maxKeys),
    Then                                                                        # Node is root with no children and space for more keys
     {$l->setMaskFirst(k7);                                                     # Set the compare bits
      $K->setReg(r15);                                                          # Key to search for
      Vpbroadcastd zmm22, r15d;                                                 # Load key
      KeepFree r15;
      Vpcmpud "k6{k7}", zmm22, zmm31, 0;                                        # Check for equal key
      Ktestd k6, k6;                                                            # Check whether a matching key was found - the operation clears the zero flag if the register is not zero
      IfNz                                                                      # Found the key so we just update the data field
      Then
       {if ($tnd)                                                               # Insert sub tree if requested
         {Kmovq r15, k6;                                                        # Position of key just found
          $t->isTree(r15, 31);                                                  # Set the zero flag to indicate whether the existing data element is in fact a tree
          IfNz                                                                  # If the data element is already a tree then get its value and return it in the data variable
          Then
           {Tzcnt r14, r15;                                                     # Trailing zeros
            $D->copy(getDFromZmm(30, "r14*$$t{width}"));                        # Data associated with the key
            Jmp $success;                                                       # Return offset of sub tree
           },
          Else                                                                  # The existing element is not a tree so we mark it as such using the single bit in r15/k6
           {$t->setTree(r15, 31);
           };
          $D->copy($t->bs->CreateTree->first) if $tnd == 1;                     # Create tree and copy offset of first  block
         }
        $D->setReg(r14);                                                        # Key to search for
        Vpbroadcastd "zmm30{k6}", r14d;                                         # Load data
        $t->putKeysData($F, 31, 30);                                            # Write the data block back into the underlying arena
        KeepFree r14;
        Jmp $success;                                                           # Insert completed successfully
       };

      Vpcmpud "k6{k7}", zmm22, zmm31, 1;                                        # Check for elements that are greater than an existing element
      Ktestw   k6, k6;
      IfEq (sub                                                                 # K6 zero implies the latest key goes at the end
       {Kshiftlw k6, k7, 1;                                                     # Reach next empty field
        Kandnw   k6, k7, k6;                                                    # Remove back fill to leave a single bit at the next empty field
       },
      sub
       {Kandw    k5, k6, k7;                                                    # Tested at: # Insert key for Tree but we could simplify by using a mask for the valid area
        Kandnw   k4, k5, k7;
        Kshiftlw k5, k5, 1;
        Korw     k5, k4, k5;                                                    # Broadcast mask
        Kandnw   k6, k5, k7;                                                    # Expand mask
        Vpexpandd  "zmm31{k5}", zmm31;                                          # Shift up keys
        Vpexpandd  "zmm30{k5}", zmm30;                                          # Shift up data
       });

      Vpbroadcastd "zmm31{k6}", r15d;                                           # Load key

      if ($tnd)                                                                 # Insert new sub tree
       {$D->copy($t->bs->CreateTree->first) if $tnd == 1;                       # Create tree and copy offset of first block
       }
      if (1)                                                                    # Expand tree bits to match
       {Kmovq $point, k6;                                                       # Position of key just found
        $t->expandTreeBitsWithZeroOrOne($tnd, 31, $point);                      # Mark new entry as a sub tree
       }

      $D->setReg(r14);                                                          # Corresponding data
      Vpbroadcastd "zmm30{k6}", r14d;                                           # Load data
      KeepFree r14;
      $t->putLengthInKeys( 31, $l + 1);                                         # Set the length of the block

      If $l + 1 == $t->maxKeys,
      Then                                                                      # Root is now full: allocate the node block for it and chain it in
       {$t->bs->allocZmmBlock($B, my $n = V(offset));                           # Children
        $t->putLoop($n, 30);                                                    # Set the link from data to node
        $t->putLoop($F, 29);                                                    # Set the link from node to key
       };

      $t->putKeysDataNode($F, 31, 30, 29);                                      # Write the data block back into the underlying arena
      $t->splitNode($B, $F, $K);                                                # Split if the leaf has got too big
      Jmp $success;                                                             # Insert completed successfully
     });

    my $compare = V(compare);                                                   # Comparison result
    my $offset  = V(offset);                                                    # Offset of result
    my $index   = V('index');                                                   # Index of result
    $t->findAndSplit($K, $compare, $offset, $index);                            # Split node if full

    KeepFree zmm 29;
    $t->getKeysDataNode($offset, 31, 30, 29);

    Mov $point, 0;
    $index->setBit($point);                                                     # Set point at the index

    If $compare == 0,                                                           # Duplicate key
    Then                                                                        # Found an equal key so update the data
     {$D->putDIntoZmm(30, $index * $t->width);                                  # Update data at key
      $t->putKeysDataNode($offset, 31, 30, 29);                                 # Rewrite data and keys
      $t->setOrClearTree($tnd, $point, 31);                                     # Set or clear tree bit as necessary
     },
    Else                                                                        # We have room for the insert because each block has been split to make it non full
     {If $compare > 0,
      Then                                                                      # Position at which to insert new key if it is greater than the indexed key
       {++$index;
        Shl $point, 1;                                                          # Move point up as well
       };

      my $length = $t->getLengthInKeys(31);                                     # Number of keys
      If $index < $length,
      Then                                                                      # Need to expand as we cannot push
       {$length->setMaskFirst(k7);                                              # Length as bits
        Kshiftlw k6, k7, 1;                                                     # Length plus one as bits with a  trailing zero
        Korw     k6, k6, k7;                                                    # Length plus one as bits with no trailing zero
        $index->clearMaskBit(k6);                                               # Zero at the index
        Vpexpandd    "zmm31{k6}", zmm31;                                        # Shift up keys
        Vpexpandd    "zmm30{k6}", zmm30;                                        # Shift up data
       };

      $t->expandTreeBitsWithZeroOrOne($tnd, 31, $point);                        # Mark inserted key as referring to a tree or not

      $D->copy($t->bs->CreateTree->first) if $tnd == 1;                         # Create tree and place its offset into data field

      ClearRegisters k7;
      $index->setMaskBit(k7);                                                   # Set bit at insertion point
      $K->setReg(r15);                                                          # Corresponding data
      Vpbroadcastd "zmm31{k7}", r15d;                                           # Load key
      $D->setReg(r14);                                                          # Corresponding data
      Vpbroadcastd "zmm30{k7}", r14d;                                           # Load data
      $t->putLengthInKeys(31, $length + 1);                                     # Set the new length of the block
      $t->putKeysDataNode($offset, 31, 30, 29);                                 # Rewrite data and keys
      $t->splitNode($B, $offset, $K);                                           # Split if the leaf has got too big
     };

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }
   name => "Nasm::X86::Tree::insertDataOrTree_$tnd",
   in   => [qw(first key)], io => [qw(bs data)];                                # Data either supplies the data or returns the offset of the sub tree

  $s->call($t->address, first => $t->first, key => $key,
    data => $tnd == 1 ? $t->data : $data);
 } # insert

sub Nasm::X86::Tree::insert($$$)                                                # Insert a dword into into the specified tree at the specified key.
 {my ($t, $key, $data) = @_;                                                    # Tree descriptor, key as a dword, data as a dword
  @_ == 3 or confess;
  $t->insertDataOrTree(0, $key, $data)                                          # Insert data
 }

sub Nasm::X86::Tree::insertTree($$;$)                                           # Insert a sub tree into the specified tree tree under the specified key. If no sub tree is supplied an empty one is provided gratis.
 {my ($t, $key, $subTree) = @_;                                                 # Tree descriptor, key as a dword, sub tree to insert else an empty one will be added
  @_ == 2 or @_ == 3 or confess;
  if (my $r = ref($subTree))
   {if ($r =~ m(Tree))
     {$t->insertDataOrTree(2, $key, $subTree->first);                           # Insert a sub tree from a tree descriptor
     }
    elsif ($r =~ m(Variable))
     {$t->insertDataOrTree(2, $key, $subTree);                                  # Insert a sub tree from a variable containing an offset to the first node of the tree
     }
    else
     {confess "Reference to a variable or a tree required";
     }
   }
  else                                                                          # Create a sub tree
   {$t->insertDataOrTree(1, $key);                                              # Request a sub tree be created if one has not been supplied
   }
 }

sub Nasm::X86::Tree::insertTreeAndClone($$)                                     # Insert a new sub tree into the specified tree tree under the specified key and return a descriptor for it.  If the tree already exists, return a descriptor for it.
 {my ($t, $key) = @_;                                                           # Tree descriptor, key as a dword
  @_ == 2 or confess;
  Comment "Nasm::X86::Tree::insertTreeAndClone";
  $t->insertTree($key);
  $t->first->copy($t->data);                                                    # Copy the data variable to the first variable without checking whether it is valid
 }

sub Nasm::X86::Tree::getKeysData($$$$)                                          #P Load the keys and data blocks for a node
 {my ($t, $offset, $zmmKeys, $zmmData) = @_;                                    # Tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys
  @_ == 4 or confess;
  $t->bs->getBlock($t->address, $offset, $zmmKeys);                             # Get the keys block
  my $data = $t->getLoop($zmmKeys);                                             # Get the offset of the corresponding data block
  $t->bs->getBlock($t->address, $data, $zmmData);                               # Get the data block
 }

sub Nasm::X86::Tree::putKeysData($$$$)                                          #P Save the key and data blocks for a node
 {my ($t, $offset, $zmmKeys, $zmmData) = @_;                                    # Tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys
  @_ == 4 or confess;
  $t->bs->putBlock($t->address, $offset, $zmmKeys);                             # Put the keys block
  my $data = $t->getLoop($zmmKeys);                                             # Get the offset of the corresponding data block
  my $up   = $t->getUpFromData($zmmData);                                       #DEBUG Check up pointer
  If ($up >= $offset,
  Then
   {PrintErrStringNL "Up is not less than node";
    Exit(0);
   });
  $t->bs->putBlock($t->address, $data, $zmmData);                               # Put the data block
 }

sub Nasm::X86::Tree::getNode($$$)                                               #P Load the child nodes for a node
 {my ($t, $offset, $zmmNode) = @_;                                              # Tree descriptor, offset of nodes, numbered zmm for keys
  @_ == 3 or confess;
  $t->bs->getBlock($t->address, $offset, $zmmNode);                             # Get the node block
 }

sub Nasm::X86::Tree::getKeysDataNode($$$$$)                                     #P Load the keys, data and child nodes for a node
 {my ($t, $offset, $zmmKeys, $zmmData, $zmmNode) = @_;                          # Tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys, numbered numbered for keys
  @_ == 5 or confess;
  my $b = $t->bs;                                                               # Underlying arena
  $b->getBlock($b->bs, $offset, $zmmKeys);                                      # Get the keys block
  my $data = $t->getLoop($zmmKeys);                                             # Get the offset of the corresponding data block
  $b->getBlock($b->bs, $data, $zmmData);                                        # Get the data block
  my $node = $t->getLoop($zmmData);                                             # Get the offset of the corresponding node block
  If ($node,
  Then                                                                          # Check for optional node block
   {$b->getBlock($b->bs, $node, $zmmNode);                                      # Get the node block
   },
  sub                                                                           # No children
   {ClearRegisters zmm $zmmNode;                                                # Clear the child block to signal that there was not one - if there were it would have child nodes in it which would be none zero
   });
 }

sub Nasm::X86::Tree::putKeysDataNode($$$$$)                                     #P Save the keys, data and child nodes for a node
 {my ($t, $offset, $zmmKeys, $zmmData, $zmmNode) = @_;                          # Tree descriptor, offset as a variable, numbered zmm for keys, numbered data for keys, numbered numbered for keys
  @_ == 5 or confess;
  $t->putKeysData($offset, $zmmKeys, $zmmData);                                 # Put keys and data
  my $node = $t->getLoop($zmmData);                                             # Get the offset of the corresponding node block
  If ($node,
  Then                                                                          # Check for optional node block
   {$t->bs->putBlock($t->address, $node, $zmmNode);                             # Put the node block
   });
 }

sub Nasm::X86::Tree::getLengthInKeys($$)                                        #P Get the length of the keys block in the numbered zmm and return it as a variable
 {my ($t, $zmm) = @_;                                                           # Tree descriptor, zmm number
  @_ == 2 or confess;

  getBFromZmm($zmm, $t->lengthOffset);                                          # The length field as a variable
 }

sub Nasm::X86::Tree::putLengthInKeys($$$)                                       #P Get the length of the block in the numbered zmm from the specified variable
 {my ($t, $zmm, $length) = @_;                                                  # tree, zmm number, length variable
  @_ == 3 or confess;
  ref($length) or confess dump($length);
  $length->putBIntoZmm($zmm, $t->lengthOffset)                                  # Set the length field
 }

sub Nasm::X86::Tree::getUpFromData($$)                                          #P Get the up offset from the data block in the numbered zmm and return it as a variable
 {my ($t, $zmm) = @_;                                                           # Tree descriptor, zmm number
  @_ == 2 or confess;
  getDFromZmm($zmm, $t->lengthOffset);                                          # The length field as a variable
 }

sub Nasm::X86::Tree::putUpIntoData($$$)                                         #P Put the offset of the parent keys block expressed as a variable into the numbered zmm
 {my ($t, $offset, $zmm) = @_;                                                  # Tree descriptor, variable containing up offset, zmm number
  @_ == 3 or confess;
  defined($offset) or confess;
  $offset->putDIntoZmm($zmm, $t->lengthOffset);                                 # Save the up offset into the data block
 }

sub Nasm::X86::Tree::getLoop($$;$)                                              #P Return the value of the loop field as a variable
 {my ($t, $zmm, $transfer) = @_;                                                # Tree descriptor, numbered zmm, optional transfer register
  @_ >= 1 or confess;
  getDFromZmm($zmm, $t->loop, $transfer);                                       # Get loop field as a variable
 }

sub Nasm::X86::Tree::putLoop($$$)                                               #P Set the value of the loop field from a variable
 {my ($t, $value, $zmm) = @_;                                                   # Tree descriptor, variable containing offset of next loop entry, numbered zmm
  @_ >= 1 or confess;
  $value->putDIntoZmm($zmm, $t->loop);                                          # Put loop field as a variable
 }

sub Nasm::X86::Tree::leftOrRightMost($$@)                                       # Return the left most or right most node
 {my ($t, $dir, @variables) = @_;                                               # Tree descriptor, direction: left = 0 or right = 1, variables
  @_ >= 1 or confess;
  my $success = Label;                                                          # Short circuit if ladders by jumping directly to the end after a successful push
  my $b = $t->bs;                                                               # Underlying arena

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    my $F = $$p{node};                                                          # First block
    PushR my @save = (rax, zmm29, zmm30, zmm31);

    K(loopLimit, 9)->for(sub                                                    # Loop a reasonable number of times
     {my ($index, $start, $next, $end) = @_;
      $t->getKeysDataNode($F, 31, 30, 29);                                      # Get the first keys block
      my $n = getDFromZmm(29, 0);                                               # Get the node block offset from the data block loop
      If ($n == 0,
      Then                                                                      # Reached the end so return the containing block
       {$$p{offset}->copy($F);
        Jmp $success;
       });
      if ($dir == 0)                                                            # Left most
       {my $l = getDFromZmm(29, 0);                                             # Get the left most node
        $F->copy($l);                                                           # Continue with the next level
       }
      else                                                                      # Right most
       {my $l = $t->getLengthInKeys(31);                                        # Length of the node
        my $r = getDFromZmm(31, $l);                                            # Get the right most child
        $F->copy($r);                                                           # Continue with the next level
       }
     });
    PrintErrStringNL "Stuck in LeftOrRightMost";
    Exit(1);

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   } name => $dir == 0 ? "Nasm::X86::Tree::leftMost"
                       : "Nasm::X86::Tree::rightMost",
     in => [qw(node )], out => [qw(offset )];

  $s->call(@variables);
 }

sub Nasm::X86::Tree::leftMost($@)                                               # Return the left most node
 {my ($t, @variables) = @_;                                                     # Tree descriptor, variables
  $t->leftOrRightMost(0, @variables)                                            # Return the left most node
 }

sub Nasm::X86::Tree::rightMost($@)                                              # Return the right most node
 {my ($t,  @variables) = @_;                                                    # Tree descriptor, variables
  $t->leftOrRightMost(1, @variables)                                            # Return the right most node
 }

sub Nasm::X86::Tree::nodeFromData($$$)                                          #P Load the the node block into the numbered zmm corresponding to the data block held in the numbered zmm.
 {my ($t, $data, $node) = @_;                                                   # Tree descriptor, numbered zmm containing data, numbered zmm to hold node block
  @_ == 3 or confess;
  my $loop = $t->getLoop($data);                                                # Get loop offset from data
  $t->getBlock($t->address, $loop, $node);                                      # Node
 }

sub Nasm::X86::Tree::address($)                                                 #P Address of the arena containing a tree
 {my ($t) = @_;                                                                 # Tree descriptor
  @_ == 1 or confess;
  $t->bs->bs;
 }

sub Nasm::X86::Tree::allocBlock($@)                                             #P Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable
 {my ($t, @variables) = @_;                                                     # Tree descriptor, variables
  @_ == 1 or confess;
  $t->bs->allocBlock                                                            # Allocate a block and return its offset as a variable
 }

sub Nasm::X86::Tree::depth($@)                                                  # Return the depth of a node within a tree.
 {my ($t, @variables) = @_;                                                     # Tree descriptor, variables
  @_ >= 2 or confess;

  my $s = Subroutine
   {my ($parameters) = @_;                                                      # Parameters
    my $success = Label;                                                        # Short circuit if ladders by jumping directly to the end after a successful push

    my $N = $$parameters{node};                                                 # Starting node

    PushR my @save = (r14, r15, zmm30, zmm31);
    my $tree = $N->clone;                                                       # Start at the specified node

    K(loop, 9)->for(sub                                                         # Step up through tree
     {my ($index, $start, $next, $end) = @_;
      $t->getKeysData($tree, 31, 30);                                           # Get the keys block
      my $p = $t->getUpFromData(30);                                            # Parent
      If ($p == 0,
      Then                                                                      # Empty tree so we have not found the key
       {$$parameters{depth}->copy($index+1);                                    # Key not found
        Jmp $success;                                                           # Return
       });
      $tree->copy($p);                                                          # Up to next level
     });
    PrintErrStringNL "Stuck in depth";                                          # We seem to be looping endlessly
    Exit(1);

    SetLabel $success;                                                          # Insert completed successfully
    PopR @save;
   }  in => [qw(node )], out => [qw(depth )];

  $s->call(@variables);
 } # depth

#D2 Sub trees                                                                   # Construct trees of trees.

sub Nasm::X86::Tree::isTree($$$)                                                #P Set the Zero Flag to oppose the tree bit in the numbered zmm register holding the keys of a node to indicate whether the data element indicated by the specified register is an offset to a sub tree in the containing arena or not.
{my ($t, $register, $zmm) = @_;                                                 # Tree descriptor, word register holding a bit shifted into the position to test, numbered zmm register holding the keys for a node in the tree
  @_ == 3 or confess;

  my $b = RegisterSize zmm0;                                                    # Size of a block == size of a zmm register
  my $o = $b - $$t{treeBits};                                                   # Bytes from tree bits to end of zmm
  PushR $register;
  And $register, $t->treeBitsMask;                                              # Mask tree bits to prevent tests outside the permitted area
  PushRR "zmm$zmm";                                                             # Put the keys on the stack
  Add rsp, RegisterSize zmm0;                                                   # Restore stack
  And $register, "[rsp-$o]";                                                    # Test the tree bits - done here to avoid the effect on the zero flag of add
  PopR $register;
 } # isTree

sub Nasm::X86::Tree::setOrClearTree($$$$)                                       #P Set or clear the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indicated by the specified register is an offset to a sub tree in the containing arena.
 {my ($t, $set, $register, $zmm) = @_;                                          # Tree descriptor, set if true else clear, register holding a single one in the lowest 14 bits at the insertion point, numbered zmm register holding the keys for a node in the tree
  @_ == 4 or confess;
  $register =~ m(\Ar) or                                                        # Check register type
    confess "General purpose register required, not $register";

  my $z = "zmm$zmm";                                                            # Full name of zmm register
  my $o = $$t{treeBits};                                                        # Tree bits to end of zmm
  PushR my @save = ($register, $z);
  if ($set)                                                                     # Set the indexed bit
   {And $register, $t->treeBitsMask;                                            # Mask tree bits to prevent operations outside the permitted area
    Or "[rsp+$o]", $register;
   }
  else                                                                          # Clear the indexed bit
   {And $register, $t->treeBitsMask;                                            # Mask tree bits to prevent operations outside the permitted area
    Not $register;
    And "[rsp+$o]", $register;
   }
  PopR @save;
 } # setOrClearTree

sub Nasm::X86::Tree::setTree($$$)                                               #P Set the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing arena.
{my ($t, $register, $zmm) = @_;                                                 # Tree descriptor, register holding data element index 0..13, numbered zmm register holding the keys for a node in the tree
  @_ == 3 or confess;
  $t->setOrClearTree(1, $register, $zmm);
 } # setTree

sub Nasm::X86::Tree::clearTree($$$)                                             #P Clear the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing arena.
{my ($t, $register, $zmm) = @_;                                                 # Tree descriptor, register holding data element index 0..13, numbered zmm register holding the keys for a node in the tree
  @_ == 3 or confess;
  $t->setOrClearTree(0, $register, $zmm);
 } # clearTree

sub Nasm::X86::Tree::getTreeBits($$$)                                           #P Load the tree bits from the numbered zmm into the specified register.
 {my ($t, $zmm, $register) = @_;                                                # Tree descriptor, numbered zmm, target register
  loadFromZmm $register, w, $zmm, $t->treeBits;
  And $register, $t->treeBitsMask;
 }

sub Nasm::X86::Tree::putTreeBits($$$)                                           #P Put the tree bits in the specified register into the numbered zmm.
 {my ($t, $zmm, $register) = @_;                                                # Tree descriptor, numbered zmm, target register
  putIntoZmm $register, w, $zmm, $t->treeBits;
  And $register, $t->treeBitsMask;
 }

sub Nasm::X86::Tree::expandTreeBitsWithZeroOrOne($$$$)                          #P Insert a zero or one into the tree bits field in the numbered zmm at the specified point
 {my ($t, $onz, $zmm, $point) = @_;                                             # Tree descriptor, 0 - zero or 1 - one, numbered zmm, register indicating point
  PushR my @save = my ($bits) = ChooseRegisters(1, $point);                     # Tree bits register
  $t->getTreeBits($zmm, $bits);                                                 # Get tree bits
  if ($onz)
   {InsertOneIntoRegisterAtPoint($point, $bits);                                # Insert a one into the tree bits at the indicated location
   }
  else
   {InsertZeroIntoRegisterAtPoint($point, $bits);                               # Insert a zero into the tree bits at the indicated location
   }
  $t->putTreeBits($zmm, $bits);                                                 # Put tree bits
  PopR @save;
 }

sub Nasm::X86::Tree::expandTreeBitsWithZero($$$)                                #P Insert a zero into the tree bits field in the numbered zmm at the specified point
 {my ($t, $zmm, $point) = @_;                                                   # Tree descriptor, numbered zmm, register indicating point
  $t->expandTreeBitsWithZeroOrOne(0, $zmm, $point);                             # Insert a zero into the tree bits field in the numbered zmm at the specified point
 }

sub Nasm::X86::Tree::expandTreeBitsWithOne($$$)                                 #P Insert a one into the tree bits field in the numbered zmm at the specified point
 {my ($t, $zmm, $point) = @_;                                                   # Tree descriptor, numbered zmm, register indicating point
  $t->expandTreeBitsWithZeroOrOne(1, $zmm, $point);                             # Insert a one into the tree bits field in the numbered zmm at the specified point
 }

#D2 Print                                                                       # Print a tree

sub Nasm::X86::Tree::print($)                                                   # Print a tree
 {my ($t) = @_;                                                                 # tree
  @_ == 1 or confess;
  Comment "Nasm::X86::Tree::print";

  PushR my @save = my ($current, $base) = (r15, rbp);
  Mov  rbp, rsp;                                                                # Stack holds the trees still to be printed
  $t->first->setReg($current);
  Push $current;

  K(loop,99)->for(sub                                                           # Print each sub tree found
   {my ($index, $start, $next, $end) = @_;

    Cmp rsp, rbp;                                                               # Check for more stacked entries
    Jge $end;                                                                   # Stack grows down
    Pop $current;

    $t->first->getReg($current);                                                # Load Latest tree to iterate from stack
    PrintOutString "Tree at: ";
    PrintOutRegisterInHex $current;

    $t->by(sub                                                                  # Iterate through the tree
     {my ($iter, $end) = @_;
      $iter->tree->depth($iter->node, my $D = V(depth));
      $iter->key ->out('key: ');
      $iter->data->out(' data: ');
      $D   ->outNL    (' depth: ');
      $t->find($iter->key);                                                     # Slow way to find out if this is a subtree
      If ($t->subTree,
      Then
       {$t->data->setReg($current);
        Push $current;
       });
     });
   });

  PopR @save;
 }

#D2 Iteration                                                                   # Iterate through a tree non recursively

sub Nasm::X86::Tree::iterator($)                                                # Iterate through a multi way tree
 {my ($b) = @_;                                                                 # tree
  @_ == 1 or confess;
  Comment "Nasm::X86::Tree::iterator";

  my $node = V(node);                                                           # The current node
  $node->copy($b->first);                                                       # Start at the first node in the tree

  my $i = genHash(__PACKAGE__.'::Tree::Iterator',                               # Iterator
    tree  => $b,                                                                # Tree we are iterating over
    node  => $node,                                                             # Current node within tree
    pos   => V('pos'),                                                          # Current position within node
    key   => V(key),                                                            # Key at this position
    data  => V(data),                                                           # Data at this position
    count => V(count),                                                          # Counter - number of node
    more  => V(more),                                                           # Iteration not yet finished
   );

  $i->pos  ->copy(V('pos', -1));                                                # Initialize iterator
  $i->count->copy(V(count,  0));
  $i->more ->copy(V(more,   1));
  $i->next;                                                                     # First element if any
 }

sub Nasm::X86::Tree::Iterator::next($)                                          # Next element in the tree
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

    If ($$p{pos} == -1,
    Then                                                                        # Initial descent
     {my $t = $iter->tree;

      PushR my @save = (zmm31, zmm30,  zmm29);
      $t->getKeysDataNode($C, 31, 30, 29);                                      # Load keys and data
      my $nodes = $t->getLoop(30);                                              # Nodes

      If ($nodes,
      Then                                                                      # Go left if there are child nodes
       {$t->leftMost($C, my $l = V(offset));
        &$new($l, K(zero, 0));
       },
      Else
       {my $l = $t->getLengthInKeys(31);                                        # Number of keys
        If ($l,
        Then                                                                    # Start with the current node as it is a leaf
         {&$new($C, K(zero, 0));
         },
        Else
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
        my $i = V(indexInParent, r14);                                          # Index in parent
        my $l = $t->getLengthInKeys($zmmPK);                                    # Length of parent

        If ($i < $l,
        Then                                                                    # Continue with this node if all the keys have yet to be finished
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
    my $n = getDFromZmm(29, 0);                                                 # First node will ne zero if on a leaf
    If ($n == 0,
    Then                                                                        # Leaf
     {If ($i < $l,
      Then
       {&$new($C, $i);
       },
      Else
       {&$up;
       });
     },
    Then                                                                        # Node
     {my $offsetAtI = getDFromZmm(29, $i * $iter->tree->width);
      $iter->tree->leftMost(node=>$offsetAtI, my $l = V(offset));
      &$new($l, K(zero, 0));
     });

    PopR @save;
    SetLabel $success;
   }  io => [qw(node  pos  key  data  count  more )];

  $s->call($iter->node, $iter->pos,   $iter->key,                               # Call with iterator variables
           $iter->data, $iter->count, $iter->more);
  $iter                                                                         # Return the iterator
 }

sub Nasm::X86::Tree::by($&)                                                     # Call the specified body with each (key, data) from the specified tree in order
 {my ($b, $body) = @_;                                                          # Tree descriptor, body
  @_ == 2 or confess;
  Comment "Nasm::X86::Tree::by";

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
  Then
   {Mov rax, 2; Push rax; Push rax; KeepFree rax;
   },
  Else                                                                          # If we are not 16 byte aligned push one one.
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
  IfEq Then {Pop r15};                                                          # Double push
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
 }

sub Exit(;$)                                                                    # Exit with the specified return code or zero if no return code supplied.  Assemble() automatically adds a call to Exit(0) if the last operation in the program is not a call to Exit.
 {my ($c) = @_;                                                                 # Return code
  $c //= 0;
  my $s = Subroutine
   {Comment "Exit code: $c";
    PushR my @save = (rax, rdi);
    KeepFree  rdi;
    Mov rdi, $c;
    Mov rax, 60;
    Syscall;
    PopR @save;
   } name => "Exit_$c";

  $s->call;
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

our $assembliesPerformed = 0;                                                   # Number of assemblies performed
our $totalBytesAssembled = 0;                                                   # Estimate the size of the output programs

sub Assemble(%)                                                                 # Assemble the generated code.
 {my (%options) = @_;                                                           # Options
  Exit 0 unless @text > 4 and $text[-4] =~ m(Exit code:);                       # Exit with code 0 if no other exit has been taken
  my $debug = $options{debug}//0;                                               # 0 - none (minimal output), 1 - normal (debug output and confess of failure), 2 - failures (debug output and no confess on failure) .

  my $k = $options{keep};                                                       # Keep the executable
  my $r = join "\n", map {s/\s+\Z//sr}   @rodata;
  my $d = join "\n", map {s/\s+\Z//sr}   @data;
  my $B = join "\n", map {s/\s+\Z//sr}   @bss;
  my $t = join "\n", map {s/\s+\Z//sr}   @text;
  my $x = join "\n", map {qq(extern $_)} @extern;
  my $L = join " ",  map {qq(-l$_)}      @link;
  my $A = <<END;
section .rodata
  $r
section .data
  $d
section .bss
  $B
section .text
$x
global _start, main
  _start:
  main:
  push rbp     ; function prologue
  mov  rbp,rsp
  $t
END

  my $c    = owf(q(z.asm), $A);                                                 # Source file
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
  lll qq($assembliesPerformed: $cmd);
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

  $totalBytesAssembled += fileSize $e;                                          # Estimate the size of the output program

  unlink $o;                                                                    # Delete files
  unlink $e unless $k;                                                          # Delete executable unless asked to keep it

  if (my $N = $options{countComments})                                          # Count the comments so we can see what code to put into sub routines
   {my %c;

    for my $c(grep {m/\A\;/} split /\n/, $A)
     {if ($c =~ m(line (\d+)))
       {$c{$1}++;
       }
     }

    my @c;
    for my $c(keys %c)                                                          # Remove comments that do not appear often
     {push @c, [$c{$c}, $c] if $c{$c} >= $N;
     }
    my @d = sort {$$b[0] <=> $$a[0]} @c;
    say STDERR formatTable(\@d, [qw(Count Line)]);                              # Print frequently appearing comments
   }

  Start;                                                                        # Clear work areas for next assembly
  return $exec if $k;                                                           # Executable wanted

  if (defined(my $e = $options{eq}))                                            # Diff against expected
   {my $g = readFile($debug < 2 ? $o1 : $o2);
       $e =~ s(\s+#.*?\n) (\n)gs;                                               # Remove comments so we can annotate listings
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
@EXPORT_OK    = qw(Add All8Structure AllocateAll8OnStack AllocateMemory And Andn Assemble Block Bswap Bt Btc Btr Bts Bzhi Call CallC ChooseRegisters ClassifyInRange ClassifyRange ClassifyWithInRange ClassifyWithInRangeAndSaveOffset ClearMemory ClearRegisters ClearZF CloseFile Cmova Cmovae Cmovb Cmovbe Cmovc Cmove Cmovg Cmovge Cmovl Cmovle Cmovna Cmovnae Cmovnb Cmp Comment CommentWithTraceBack ConcatenateShortStrings ConvertUtf8ToUtf32 CopyMemory CreateArena Cstrlen DComment Db Dbwdq Dd Dec Dq Ds Dw Else Exit Extern For ForEver ForIn Fork FreeMemory GetLengthOfShortString GetNextUtf8CharAsUtf32 GetPPid GetPid GetPidInHex GetUid Hash ISA Idiv If IfC IfEq IfGe IfGt IfLe IfLt IfNc IfNe IfNz IfZ Imul Inc InsertOneIntoRegisterAtPoint InsertZeroIntoRegisterAtPoint Isa Ja Jae Jb Jbe Jc Jcxz Je Jecxz Jg Jge Jl Jle Jmp Jna Jnae Jnb Jnbe Jnc Jne Jng Jnge Jnl Jnle Jno Jnp Jns Jnz Jo Jp Jpe Jpo Jrcxz Js Jz K Kaddb Kaddd Kaddq Kaddw Kandb Kandd Kandnb Kandnd Kandnq Kandnw Kandq Kandw Keep KeepFree KeepPop KeepPush KeepReturn KeepSet Kmovb Kmovd Kmovq Kmovw Knotb Knotd Knotq Knotw Korb Kord Korq Kortestb Kortestd Kortestq Kortestw Korw Kshiftlb Kshiftld Kshiftlq Kshiftlw Kshiftrb Kshiftrd Kshiftrq Kshiftrw Ktestb Ktestd Ktestq Ktestw Kunpckb Kunpckd Kunpckq Kunpckw Kxnorb Kxnord Kxnorq Kxnorw Kxorb Kxord Kxorq Kxorw Label Lahf Lea Link LoadBitsIntoMaskRegister LoadConstantIntoMaskRegister LoadShortStringFromMemoryToZmm LoadZmm LocalData LocateIntelEmulator Loop Lzcnt Macro MaskMemory22 MaskMemoryInRange4_22 Mov Movdqa Mulpd Neg Not OpenRead OpenWrite Or PeekR Pextrb Pextrd Pextrq Pextrw Pi32 Pi64 Pinsrb Pinsrd Pinsrq Pinsrw Pop PopEax PopR PopRR Popcnt Popfq PrintErrMemory PrintErrMemoryInHex PrintErrMemoryInHexNL PrintErrMemoryNL PrintErrNL PrintErrRaxInHex PrintErrRegisterInHex PrintErrString PrintErrStringNL PrintErrZF PrintMemory PrintMemoryInHex PrintNL PrintOutMemory PrintOutMemoryInHex PrintOutMemoryInHexNL PrintOutMemoryNL PrintOutNL PrintOutRaxInHex PrintOutRaxInReverseInHex PrintOutRegisterInHex PrintOutRegistersInHex PrintOutRflagsInHex PrintOutRipInHex PrintOutString PrintOutStringNL PrintOutZF PrintRaxInHex PrintRegisterInHex PrintString PrintUtf32 Pslldq Psrldq Push PushR PushRR Pushfq R RComment Rb Rbwdq Rd Rdtsc ReadFile ReadTimeStampCounter RegisterSize ReorderSyscallRegisters RestoreFirstFour RestoreFirstFourExceptRax RestoreFirstFourExceptRaxAndRdi RestoreFirstSeven RestoreFirstSevenExceptRax RestoreFirstSevenExceptRaxAndRdi Ret Rq Rs Rutf8 Rw SaveFirstFour SaveFirstSeven SetLabel SetLengthOfShortString SetMaskRegister SetZF Seta Setae Setb Setbe Setc Sete Setg Setge Setl Setle Setna Setnae Setnb Setnbe Setnc Setne Setng Setnge Setnl Setno Setnp Setns Setnz Seto Setp Setpe Setpo Sets Setz Shl Shr Start StatSize StringLength Structure Sub Subroutine Syscall TODO Test Then Trace Tzcnt UnReorderSyscallRegisters V VERSION Vaddd Vaddpd Variable Vcvtudq2pd Vcvtudq2ps Vcvtuqq2pd Vdpps Vgetmantps Vmovd Vmovdqa32 Vmovdqa64 Vmovdqu Vmovdqu32 Vmovdqu64 Vmovdqu8 Vmovq Vmulpd Vpbroadcastb Vpbroadcastd Vpbroadcastq Vpbroadcastw Vpcmpeqb Vpcmpeqd Vpcmpeqq Vpcmpeqw Vpcmpub Vpcmpud Vpcmpuq Vpcmpuw Vpcompressd Vpcompressq Vpexpandd Vpexpandq Vpextrb Vpextrd Vpextrq Vpextrw Vpinsrb Vpinsrd Vpinsrq Vpinsrw Vpmullb Vpmulld Vpmullq Vpmullw Vprolq Vpsubb Vpsubd Vpsubq Vpsubw Vpxorq Vsqrtpd Vz WaitPid Xchg Xor ah al ax bh bl bp bpl bx ch cl cs cx dh di dil dl ds dx eax ebp ebx ecx edi edx es esi esp fs gs k0 k1 k2 k3 k4 k5 k6 k7 mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7 r10 r10b r10d r10l r10w r11 r11b r11d r11l r11w r12 r12b r12d r12l r12w r13 r13b r13d r13l r13w r14 r14b r14d r14l r14w r15 r15b r15d r15l r15w r8 r8b r8d r8l r8w r9 r9b r9d r9l r9w rax rbp rbx rcx rdi rdx rflags rip rsi rsp si sil sp spl ss st0 st1 st2 st3 st4 st5 st6 st7 xmm0 xmm1 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm2 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm3 xmm30 xmm31 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 ymm0 ymm1 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm2 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm3 ymm30 ymm31 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 zmm0 zmm1 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm2 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm3 zmm30 zmm31 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9);
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

Use B<Avx512> instructions to perform B<64> comparisons in parallel:

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

Create a dynamic arena, add some content to it, write the arena to
stdout:

  my $a = CreateArena;                                                     # Create a string
  my $b = CreateArena;                                                     # Create a string
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

   Fork;                                     # Fork

   Test rax,rax;
   IfNz                                      # Parent
   Then
    {Mov rbx, rax;
     WaitPid;
     GetPid;                                 # Pid of parent as seen in parent
     Mov rcx,rax;
     PrintOutRegisterInHex rax, rbx, rcx;
    },
   Else                                      # Child
    {Mov r8,rax;
     GetPid;                                 # Child pid as seen in child
     Mov r9,rax;
     GetPPid;                                # Parent pid as seen in child
     Mov r10,rax;
     PrintOutRegisterInHex r8, r9, r10;
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

  ReadFile(V(file, Rs($0)), (my $s = V(size)), my $a = V(address));          # Read file
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

=head3 Create a multi way tree using SIMD instructions

Create a multiway tree as in L<Tree::Multi> using B<Avx512> instructions and
iterate through it:

  my $N = 12;
  my $b = CreateArena;                   # Resizable memory block
  my $t = $b->CreateTree;        # Multi way tree in memory block

  K(count, $N)->for(sub                      # Add some entries to the tree
   {my ($index, $start, $next, $end) = @_;
    my $k = $index + 1;
    $t->insert($k,      $k + 0x100);
    $t->insert($k + $N, $k + 0x200);
   });

  $t->by(sub                                  # Iterate through the tree
   {my ($iter, $end) = @_;
    $iter->key ->out('key: ');
    $iter->data->out(' data: ');
    $iter->tree->depth($iter->node, my $D = V(depth));

    $t->find($iter->key);
    $t->found->out(' found: '); $t->data->out(' data: '); $D->outNL(' depth: ');
   });

  $t->find(K(key, 0xffff));  $t->found->outNL('Found: ');  # Find some entries
  $t->find(K(key, 0xd));     $t->found->outNL('Found: ');

  If ($t->found,
  Then
   {$t->data->outNL("Data : ");
   });

  ok Assemble(debug => 0, eq => <<END);
key: 0000 0000 0000 0001 data: 0000 0000 0000 0101 found: 0000 0000 0000 0001 data: 0000 0000 0000 0101 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0002 data: 0000 0000 0000 0102 found: 0000 0000 0000 0001 data: 0000 0000 0000 0102 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0003 data: 0000 0000 0000 0103 found: 0000 0000 0000 0001 data: 0000 0000 0000 0103 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0004 data: 0000 0000 0000 0104 found: 0000 0000 0000 0001 data: 0000 0000 0000 0104 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0005 data: 0000 0000 0000 0105 found: 0000 0000 0000 0001 data: 0000 0000 0000 0105 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0006 data: 0000 0000 0000 0106 found: 0000 0000 0000 0001 data: 0000 0000 0000 0106 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0007 data: 0000 0000 0000 0107 found: 0000 0000 0000 0001 data: 0000 0000 0000 0107 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0008 data: 0000 0000 0000 0108 found: 0000 0000 0000 0001 data: 0000 0000 0000 0108 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0009 data: 0000 0000 0000 0109 found: 0000 0000 0000 0001 data: 0000 0000 0000 0109 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000A data: 0000 0000 0000 010A found: 0000 0000 0000 0001 data: 0000 0000 0000 010A depth: 0000 0000 0000 0002
key: 0000 0000 0000 000B data: 0000 0000 0000 010B found: 0000 0000 0000 0001 data: 0000 0000 0000 010B depth: 0000 0000 0000 0002
key: 0000 0000 0000 000C data: 0000 0000 0000 010C found: 0000 0000 0000 0001 data: 0000 0000 0000 010C depth: 0000 0000 0000 0002
key: 0000 0000 0000 000D data: 0000 0000 0000 0201 found: 0000 0000 0000 0001 data: 0000 0000 0000 0201 depth: 0000 0000 0000 0001
key: 0000 0000 0000 000E data: 0000 0000 0000 0202 found: 0000 0000 0000 0001 data: 0000 0000 0000 0202 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000F data: 0000 0000 0000 0203 found: 0000 0000 0000 0001 data: 0000 0000 0000 0203 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0010 data: 0000 0000 0000 0204 found: 0000 0000 0000 0001 data: 0000 0000 0000 0204 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0011 data: 0000 0000 0000 0205 found: 0000 0000 0000 0001 data: 0000 0000 0000 0205 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0012 data: 0000 0000 0000 0206 found: 0000 0000 0000 0001 data: 0000 0000 0000 0206 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0013 data: 0000 0000 0000 0207 found: 0000 0000 0000 0001 data: 0000 0000 0000 0207 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0014 data: 0000 0000 0000 0208 found: 0000 0000 0000 0001 data: 0000 0000 0000 0208 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0015 data: 0000 0000 0000 0209 found: 0000 0000 0000 0001 data: 0000 0000 0000 0209 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0016 data: 0000 0000 0000 020A found: 0000 0000 0000 0001 data: 0000 0000 0000 020A depth: 0000 0000 0000 0002
key: 0000 0000 0000 0017 data: 0000 0000 0000 020B found: 0000 0000 0000 0001 data: 0000 0000 0000 020B depth: 0000 0000 0000 0002
key: 0000 0000 0000 0018 data: 0000 0000 0000 020C found: 0000 0000 0000 0001 data: 0000 0000 0000 020C depth: 0000 0000 0000 0002
Found: 0000 0000 0000 0000
Found: 0000 0000 0000 0001
Data : 0000 0000 0000 0201
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


Version "20210813".


The following sections describe the methods in each functional area of this
module.  For an alphabetic listing of all methods by name see L<Index|/Index>.



=head1 Data

Layout data

=head2 SetLabel($l)

Create (if necessary) and set a label in the code section returning the label so set.

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
    Exit(0);

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


=head2 Rutf8(@d)

Layout a utf8 encoded string as bytes in read only memory and return their label

     Parameter  Description
  1  @d         Data to be laid out

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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);


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

B<Example:>


    LoadZmm 0, 0..63;

    PrintOutRegisterInHex zmm 0;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    is_deeply Assemble, <<END;
    zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  END


=head2 ChooseRegisters($number, @registers)

Choose the specified numbers of registers excluding those on the specified list

     Parameter   Description
  1  $number     Number of registers needed
  2  @registers  Registers not to choose

=head2 InsertZeroIntoRegisterAtPoint($point, $in)

Insert a zero into the specified register at the point indicated by another register

     Parameter  Description
  1  $point     Register with a single 1 at the insertion point
  2  $in        Register to be inserted into.

B<Example:>


    Mov r15, 0x100;                                                               # Given a register with a single one in it indicating the desired position,
    Mov r14, 0xFFDC;                                                              # Insert a zero into the register at that position shifting the bits above that position up left one to make space for the new zero.
    Mov r13, 0xF03F;
    PrintOutRegisterInHex         r14, r15;

    InsertZeroIntoRegisterAtPoint r15, r14;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex r14;
    Or r14, r15;                                                                  # Replace the inserted zero with a one
    PrintOutRegisterInHex r14;
    InsertOneIntoRegisterAtPoint r15, r13;
    PrintOutRegisterInHex r13;
    ok Assemble(debug => 0, eq => <<END);
     r14: 0000 0000 0000 FFDC
     r15: 0000 0000 0000 0100
     r14: 0000 0000 0001 FEDC
     r14: 0000 0000 0001 FFDC
     r13: 0000 0000 0001 E13F
  END


=head2 InsertOneIntoRegisterAtPoint($point, $in)

Insert a one into the specified register at the point indicated by another register

     Parameter  Description
  1  $point     Register with a single 1 at the insertion point
  2  $in        Register to be inserted into.

B<Example:>


    Mov r15, 0x100;                                                               # Given a register with a single one in it indicating the desired position,
    Mov r14, 0xFFDC;                                                              # Insert a zero into the register at that position shifting the bits above that position up left one to make space for the new zero.
    Mov r13, 0xF03F;
    PrintOutRegisterInHex         r14, r15;
    InsertZeroIntoRegisterAtPoint r15, r14;
    PrintOutRegisterInHex r14;
    Or r14, r15;                                                                  # Replace the inserted zero with a one
    PrintOutRegisterInHex r14;

    InsertOneIntoRegisterAtPoint r15, r13;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex r13;
    ok Assemble(debug => 0, eq => <<END);
     r14: 0000 0000 0000 FFDC
     r15: 0000 0000 0000 0100
     r14: 0000 0000 0001 FEDC
     r14: 0000 0000 0001 FFDC
     r13: 0000 0000 0001 E13F
  END


=head2 LoadZmm($zmm, @bytes)

Load a numbered zmm with the specified bytes

     Parameter  Description
  1  $zmm       Numbered zmm
  2  @bytes     Bytes

B<Example:>



    LoadZmm 0, 0..63;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex zmm 0;

    is_deeply Assemble, <<END;
    zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  END


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


    SetZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};
    ClearZF;
    IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

    Mov r15, 5;
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};

    ok Assemble(debug=>0, eq => <<END);
  ZF=1
  ZF=0
  ZF=1
  ZF=1
  ZF=0
  Zero
  NOT zero
  Carry
  NO carry
  Carry
  NO carry
  END


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

    SetZF;
    IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};

    ClearZF;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

    Mov r15, 5;
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};

    ok Assemble(debug=>0, eq => <<END);
  ZF=1
  ZF=0
  ZF=1
  ZF=1
  ZF=0
  Zero
  NOT zero
  Carry
  NO carry
  Carry
  NO carry
  END


=head2 Tracing

Trace the execution of a program

=head3 Trace()

Add tracing code


=head2 Tracking

Track the use of registers so that we do not accidently use unset registers or write into registers that are already in use.

=head3 Keep(@target)

Mark registers as in use so that they cannot be updated  until we explicitly free them.  Complain if the register is already in use.

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

=head3 LoadConstantIntoMaskRegister($mask, $value)

Set a mask register equal to a constant.

     Parameter  Description
  1  $mask      Mask register to load
  2  $value     Constant to load

B<Example:>


    Mov r14, 0;
    Kmovq k0, r14;
    KeepFree r14;
    Ktestq k0, k0;
    IfZ Then {PrintOutStringNL "0 & 0 == 0"};
    PrintOutZF;


    LoadConstantIntoMaskRegister k1, 1;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Ktestq k1, k1;
    IfNz Then {PrintOutStringNL "1 & 1 != 0"};
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

    my $a = V('aaaa');
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


=head3 LoadBitsIntoMaskRegister($mask, $prefix, @values)

Load a bit string specification into a mask register

     Parameter  Description
  1  $mask      Mask register to load
  2  $prefix    Prefix bits
  3  @values    +n 1 bits -n 0 bits

B<Example:>


    for (0..7)
     {ClearRegisters "k$_";
      K($_,$_)->setMaskBit("k$_");
      PrintOutRegisterInHex "k$_";
     }

    ClearRegisters k7;

    LoadBitsIntoMaskRegister(k7, '1010', -4, +4, -2, +2, -1, +1, -1, +1);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex "k7";

    ok Assemble(debug => 0, eq => <<END);
      k0: 0000 0000 0000 0001
      k1: 0000 0000 0000 0002
      k2: 0000 0000 0000 0004
      k3: 0000 0000 0000 0008
      k4: 0000 0000 0000 0010
      k5: 0000 0000 0000 0020
      k6: 0000 0000 0000 0040
      k7: 0000 0000 0000 0080
      k7: 0000 0000 000A 0F35
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


    my $cmp = sub
     {my ($a, $b) = @_;

      for my $op(qw(eq ne lt le gt ge))
       {Mov rax, $a;
        Cmp rax, $b;
        KeepFree rax;
        my $Op = ucfirst $op;

        eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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


=head2 Then($body)

Then body for an If statement

     Parameter  Description
  1  $body      Then body

B<Example:>


    my $a = V(a, 3);  $a->outNL;
    my $b = K(b, 2);  $b->outNL;
    my $c = $a +  $b; $c->outNL;
    my $d = $c -  $a; $d->outNL;
    my $e = $d == $b; $e->outNL;
    my $f = $d != $b; $f->outNL;
    my $g = $a *  $b; $g->outNL;
    my $h = $g /  $b; $h->outNL;
    my $i = $a %  $b; $i->outNL;

    If ($a == 3,

    Then  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {PrintOutStringNL "a == 3"
     },
    Else
     {PrintOutStringNL "a != 3"
     });

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


=head2 Else($body)

Else body for an If statement

     Parameter  Description
  1  $body      Else body

B<Example:>


    my $a = V(a, 3);  $a->outNL;
    my $b = K(b, 2);  $b->outNL;
    my $c = $a +  $b; $c->outNL;
    my $d = $c -  $a; $d->outNL;
    my $e = $d == $b; $e->outNL;
    my $f = $d != $b; $f->outNL;
    my $g = $a *  $b; $g->outNL;
    my $h = $g /  $b; $h->outNL;
    my $i = $a %  $b; $i->outNL;

    If ($a == 3,
    Then
     {PrintOutStringNL "a == 3"
     },

    Else  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {PrintOutStringNL "a != 3"
     });

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


=head2 IfEq($then, $else)

If equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    my $cmp = sub
     {my ($a, $b) = @_;

      for my $op(qw(eq ne lt le gt ge))
       {Mov rax, $a;
        Cmp rax, $b;
        KeepFree rax;
        my $Op = ucfirst $op;
        eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
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


=head2 IfNe($then, $else)

If not equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    my $cmp = sub
     {my ($a, $b) = @_;

      for my $op(qw(eq ne lt le gt ge))
       {Mov rax, $a;
        Cmp rax, $b;
        KeepFree rax;
        my $Op = ucfirst $op;
        eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
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


=head2 IfNz($then, $else)

If the zero flag is not set then execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    Mov rax, 0;
    Test rax,rax;

    IfNz  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Then
     {PrintOutRegisterInHex rax;
     },
    Else
     {PrintOutRegisterInHex rbx;
     };
    KeepFree rax;
    Mov rax, 1;
    Test rax,rax;

    IfNz  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Then
     {PrintOutRegisterInHex rcx;
     },
    Else
     {PrintOutRegisterInHex rdx;
     };

    ok Assemble =~ m(rbx.*rcx)s;


=head2 IfZ($then, $else)

If the zero flag is set then execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


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

    SetZF;

    IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    ClearZF;
    IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

    Mov r15, 5;
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};

    ok Assemble(debug=>0, eq => <<END);
  ZF=1
  ZF=0
  ZF=1
  ZF=1
  ZF=0
  Zero
  NOT zero
  Carry
  NO carry
  Carry
  NO carry
  END


=head2 IfC($then, $else)

If the carry flag is set then execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


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

    SetZF;
    IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};
    ClearZF;
    IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

    Mov r15, 5;

    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};

    ok Assemble(debug=>0, eq => <<END);
  ZF=1
  ZF=0
  ZF=1
  ZF=1
  ZF=0
  Zero
  NOT zero
  Carry
  NO carry
  Carry
  NO carry
  END


=head2 IfNc($then, $else)

If the carry flag is not set then execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


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

    SetZF;
    IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};
    ClearZF;
    IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

    Mov r15, 5;
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};

    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble(debug=>0, eq => <<END);
  ZF=1
  ZF=0
  ZF=1
  ZF=1
  ZF=0
  Zero
  NOT zero
  Carry
  NO carry
  Carry
  NO carry
  END


=head2 IfLt($then, $else)

If less than execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    my $cmp = sub
     {my ($a, $b) = @_;

      for my $op(qw(eq ne lt le gt ge))
       {Mov rax, $a;
        Cmp rax, $b;
        KeepFree rax;
        my $Op = ucfirst $op;
        eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
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


=head2 IfLe($then, $else)

If less than or equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    my $cmp = sub
     {my ($a, $b) = @_;

      for my $op(qw(eq ne lt le gt ge))
       {Mov rax, $a;
        Cmp rax, $b;
        KeepFree rax;
        my $Op = ucfirst $op;
        eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
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


=head2 IfGt($then, $else)

If greater than execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    my $cmp = sub
     {my ($a, $b) = @_;

      for my $op(qw(eq ne lt le gt ge))
       {Mov rax, $a;
        Cmp rax, $b;
        KeepFree rax;
        my $Op = ucfirst $op;
        eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
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


=head2 IfGe($then, $else)

If greater than or equal execute the then body else the else body

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    my $cmp = sub
     {my ($a, $b) = @_;

      for my $op(qw(eq ne lt le gt ge))
       {Mov rax, $a;
        Cmp rax, $b;
        KeepFree rax;
        my $Op = ucfirst $op;
        eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
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


=head2 Block($body)

Execute a block of code one with the option of jumping out of the block or restarting the block via the supplied labels.

     Parameter  Description
  1  $body      Body

B<Example:>


    Mov rax, 0;

    Block  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {my ($start, $end) = @_;
      PrintOutRegisterInHex rax;
      Cmp rax, 3;
      Jge $end;
      Inc rax;
      PrintOutRegisterInHex rax
      Jmp $start;
     };

    ok Assemble(debug => 0, eq => <<END);
     rax: 0000 0000 0000 0000
     rax: 0000 0000 0000 0001
     rax: 0000 0000 0000 0002
     rax: 0000 0000 0000 0003
  END


=head2 For($body, $register, $limit, $increment)

For - iterate the body as long as register is less than limit incrementing by increment each time

     Parameter   Description
  1  $body       Body
  2  $register   Register
  3  $limit      Limit on loop
  4  $increment  Increment on each iteration

B<Example:>



    For  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {my ($start, $end, $next) = @_;
      Cmp rax, 3;
      Jge $end;
      PrintOutRegisterInHex rax;
     } rax, 16, 1;

    ok Assemble(debug => 0, eq => <<END);
     rax: 0000 0000 0000 0000
     rax: 0000 0000 0000 0001
     rax: 0000 0000 0000 0002
  END


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

=head2 CommentWithTraceBack(@comment)

Insert a comment into the assembly code with a traceback showing how it was generated

     Parameter  Description
  1  @comment   Text of comment

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
    Exit(0);

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

B<Example:>


    my $q = Rs('abababab');
    Mov(rax, "[$q]");

    PrintOutString "rax: ";  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRaxInHex;
    PrintOutNL;
    Xor rax, rax;

    PrintOutString "rax: ";  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRaxInHex;
    PrintOutNL;

    ok Assemble =~ m(rax: 6261 6261 6261 6261.*rax: 0000 0000 0000 0000)s;


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


    ok Assemble(debug=>0, eq => <<END);
      r8: 6867 6665 6463 6261
  END


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


    SetZF;
    IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};
    ClearZF;
    IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

    Mov r15, 5;
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};
    Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};

    ok Assemble(debug=>0, eq => <<END);
  ZF=1
  ZF=0
  ZF=1
  ZF=1
  ZF=0
  Zero
  NOT zero
  Carry
  NO carry
  Carry
  NO carry
  END


=head1 Variables

Variable definitions and operations

=head2 Definitions

Variable definitions

=head3 Variable($size, $name, $expr, %options)

Create a new variable with the specified size and name initialized via an expression

     Parameter  Description
  1  $size      Size as a power of 2
  2  $name      Name of variable
  3  $expr      Optional expression initializing variable
  4  %options   Options

=head3 V($name, $expr, %options)

Define a quad variable

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression
  3  %options   Options

B<Example:>



    my $a = V(a, 3);  $a->outNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $b = K(b, 2);  $b->outNL;
    my $c = $a +  $b; $c->outNL;
    my $d = $c -  $a; $d->outNL;
    my $e = $d == $b; $e->outNL;
    my $f = $d != $b; $f->outNL;
    my $g = $a *  $b; $g->outNL;
    my $h = $g /  $b; $h->outNL;
    my $i = $a %  $b; $i->outNL;

    If ($a == 3,
    Then
     {PrintOutStringNL "a == 3"
     },
    Else
     {PrintOutStringNL "a != 3"
     });

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


=head3 K($name, $expr, %options)

Define a quad constant

     Parameter  Description
  1  $name      Name of variable
  2  $expr      Initializing expression
  3  %options   Options

B<Example:>


    my $a = V(a, 3);  $a->outNL;

    my $b = K(b, 2);  $b->outNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    my $c = $a +  $b; $c->outNL;
    my $d = $c -  $a; $d->outNL;
    my $e = $d == $b; $e->outNL;
    my $f = $d != $b; $f->outNL;
    my $g = $a *  $b; $g->outNL;
    my $h = $g /  $b; $h->outNL;
    my $i = $a %  $b; $i->outNL;

    If ($a == 3,
    Then
     {PrintOutStringNL "a == 3"
     },
    Else
     {PrintOutStringNL "a != 3"
     });

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


=head3 R($name, $size)

Define a reference variable

     Parameter  Description
  1  $name      Name of variable
  2  $size      Variable being referenced

=head2 Print variables

Print the values of variables or the memory addressed by them

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

=head2 Operations

Variable operations

=head3 Nasm::X86::Variable::address($left, $offset)

Get the address of a variable with an optional offset

     Parameter  Description
  1  $left      Left variable
  2  $offset    Optional offset

=head3 Nasm::X86::Variable::copy($left, $right, $Transfer)

Copy one variable into another

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable
  3  $Transfer  Optional transfer register

=head3 Nasm::X86::Variable::copyAddress($left, $right, $Transfer)

Copy a reference to a variable

     Parameter  Description
  1  $left      Left variable
  2  $right     Right variable
  3  $Transfer  Optional transfer register

=head3 Nasm::X86::Variable::copyZF($var)

Copy the current state of the zero flag into a variable

     Parameter  Description
  1  $var       Variable

B<Example:>


    Mov r15, 1;
    my $z = V(zf);
    Cmp r15, 1; $z->copyZF;         $z->outNL;
    Cmp r15, 2; $z->copyZF;         $z->outNL;
    Cmp r15, 1; $z->copyZFInverted; $z->outNL;
    Cmp r15, 2; $z->copyZFInverted; $z->outNL;

    is_deeply Assemble(debug=>0), <<END;
  zf: 0000 0000 0000 0001
  zf: 0000 0000 0000 0000
  zf: 0000 0000 0000 0000
  zf: 0000 0000 0000 0001
  END


=head3 Nasm::X86::Variable::copyZFInverted($var)

Copy the opposite of the current state of the zero flag into a variable

     Parameter  Description
  1  $var       Variable

B<Example:>


    Mov r15, 1;
    my $z = V(zf);
    Cmp r15, 1; $z->copyZF;         $z->outNL;
    Cmp r15, 2; $z->copyZF;         $z->outNL;
    Cmp r15, 1; $z->copyZFInverted; $z->outNL;
    Cmp r15, 2; $z->copyZFInverted; $z->outNL;

    is_deeply Assemble(debug=>0), <<END;
  zf: 0000 0000 0000 0001
  zf: 0000 0000 0000 0000
  zf: 0000 0000 0000 0000
  zf: 0000 0000 0000 0001
  END


=head3 Nasm::X86::Variable::clone($var)

Clone a variable to create a new variable

     Parameter  Description
  1  $var       Variable to clone

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

=head3 Nasm::X86::Variable::booleanC($cmov, $op, $left, $right)

Combine the left hand variable with the right hand variable via a boolean operator using a conditional move instruction.

     Parameter  Description
  1  $cmov      Conditional move instruction name
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


    my $a = V("a", 1);
    my $b = V("b", 2);
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


    my $a = V("a", 1);
    my $b = V("b", 2);
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


    my $start  = V("Start",  7);
    my $length = V("Length", 3);
    $start->setMask($length, k7);
    PrintOutRegisterInHex k7;

    is_deeply Assemble, <<END;
      k7: 0000 0000 0000 0380
  END

    my $z = V('zero', 0);
    my $o = V('one',  1);
    my $t = V('two',  2);
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

=head3 Nasm::X86::Variable::setMaskBit($index, $mask)

Set a bit in the specified mask register retaining the other bits

     Parameter  Description
  1  $index     Variable containing bit position to set
  2  $mask      Mask register

=head3 Nasm::X86::Variable::clearMaskBit($index, $mask)

Clear a bit in the specified mask register retaining the other bits

     Parameter  Description
  1  $index     Variable containing bit position to clear
  2  $mask      Mask register

=head3 Nasm::X86::Variable::setBit($index, $mask)

Set a bit in the specified register retaining the other bits

     Parameter  Description
  1  $index     Variable containing bit position to set
  2  $mask      Mask register

=head3 Nasm::X86::Variable::clearBit($index, $mask)

Clear a bit in the specified mask register retaining the other bits

     Parameter  Description
  1  $index     Variable containing bit position to clear
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
    my $source = V(Source, $s);

    if (1)                                                                        # First block
     {my $offset = V(Offset, 7);
      my $length = V(Length, 3);
      $source->setZmm(0, $offset, $length);
     }

    if (1)                                                                        # Second block
     {my $offset = V(Offset, 33);
      my $length = V(Length, 12);
      $source->setZmm(0, $offset, $length);
     }

    PrintOutRegisterInHex zmm0;

    is_deeply Assemble, <<END;
    zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 000B 0A09 0807   0605 0403 0201 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0201   0000 0000 0000 0000
  END


=head3 Nasm::X86::Variable::loadZmm($source, $zmm)

Load bytes from the memory addressed by the specified source variable into the numbered zmm register.

     Parameter  Description
  1  $source    Variable containing the address of the source
  2  $zmm       Number of zmm to get

=head3 loadFromZmm($register, $size, $zmm, $offset)

Load the specified register from the offset located in the numbered zmm.

     Parameter  Description
  1  $register  Register to load
  2  $size      "b|w|d|q" for size
  3  $zmm       Numbered zmm register to load from
  4  $offset    Constant offset in bytes

=head3 putIntoZmm($register, $size, $zmm, $offset)

Put the specified register into the numbered zmm at the from the offset located in the numbered zmm.

     Parameter  Description
  1  $register  Register to load
  2  $size      Bwdq for size
  3  $zmm       Numbered zmm register to load from
  4  $offset    Constant offset in bytes

=head3 getBwdqFromMm($size, $mm, $offset, $Transfer)

Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $size      Size of get
  2  $mm        Mm register
  3  $offset    Offset in bytes either as a constant or as a variable
  4  $Transfer  Optional transfer register

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

=head3 getDFromZmm($zmm, $offset, $transfer)

Get the double word from the numbered zmm register and return it in a variable

     Parameter  Description
  1  $zmm       Numbered zmm
  2  $offset    Offset in bytes
  3  $transfer  Optional transfer register

B<Example:>


    my $s = Rb(0..8);
    my $c = V("Content",   "[$s]");
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
    my $c = V("Content",   "[$s]");
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


    my $N = V(size, 2048);
    my $q = Rs('a'..'p');
    AllocateMemory($N, my $address = V(address));

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


    V(limit,10)->for(sub
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
    IfZ Then {PrintOutStringNL "0 & 0 == 0"};
    PrintOutZF;

    LoadConstantIntoMaskRegister k1, 1;
    Ktestq k1, k1;
    IfNz Then {PrintOutStringNL "1 & 1 != 0"};
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


    my $a = V('aaaa');
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
    Then
     {Mov rbx, rax;
      WaitPid;
      GetPid;                                                                     # Pid of parent as seen in parent
      Mov rcx,rax;
      PrintOutRegisterInHex rax, rbx, rcx;
     },
    Else                                                                          # Child
     {Mov r8,rax;
      GetPid;                                                                     # Child pid as seen in child
      Mov r9,rax;
      GetPPid;                                                                    # Parent pid as seen in child
      Mov r10,rax;
      PrintOutRegisterInHex r8, r9, r10;
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
    Then
     {Mov rbx, rax;
      WaitPid;

      GetPid;                                                                     # Pid of parent as seen in parent  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      Mov rcx,rax;
      PrintOutRegisterInHex rax, rbx, rcx;
     },
    Else                                                                          # Child
     {Mov r8,rax;

      GetPid;                                                                     # Child pid as seen in child  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      Mov r9,rax;
      GetPPid;                                                                    # Parent pid as seen in child
      Mov r10,rax;
      PrintOutRegisterInHex r8, r9, r10;
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
    Then
     {Mov rbx, rax;
      WaitPid;
      GetPid;                                                                     # Pid of parent as seen in parent
      Mov rcx,rax;
      PrintOutRegisterInHex rax, rbx, rcx;
     },
    Else                                                                          # Child
     {Mov r8,rax;
      GetPid;                                                                     # Child pid as seen in child
      Mov r9,rax;

      GetPPid;                                                                    # Parent pid as seen in child  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      Mov r10,rax;
      PrintOutRegisterInHex r8, r9, r10;
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
    Then
     {Mov rbx, rax;

      WaitPid;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      GetPid;                                                                     # Pid of parent as seen in parent
      Mov rcx,rax;
      PrintOutRegisterInHex rax, rbx, rcx;
     },
    Else                                                                          # Child
     {Mov r8,rax;
      GetPid;                                                                     # Child pid as seen in child
      Mov r9,rax;
      GetPPid;                                                                    # Parent pid as seen in child
      Mov r10,rax;
      PrintOutRegisterInHex r8, r9, r10;
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
    AllocateMemory(K(size, $N), my $a = V(address));
    CopyMemory(V(source, $s), V(size, $N), target => $a);

    AllocateMemory(K(size, $N), my $b = V(address));
    CopyMemory(source => $a, target => $b, K(size, $N));

    $b->setReg(rax);
    Mov rdi, $N;

    PrintOutMemoryInHexNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble(debug=>0, eq => <<END);
  0001 0203 0405 06070809 0A0B 0C0D 0E0F1011 1213 1415 16171819 1A1B 1C1D 1E1F2021 2223 2425 26272829 2A2B 2C2D 2E2F3031 3233 3435 36373839 3A3B 3C3D 3E3F4041 4243 4445 46474849 4A4B 4C4D 4E4F5051 5253 5455 56575859 5A5B 5C5D 5E5F6061 6263 6465 66676869 6A6B 6C6D 6E6F7071 7273 7475 76777879 7A7B 7C7D 7E7F8081 8283 8485 86878889 8A8B 8C8D 8E8F9091 9293 9495 96979899 9A9B 9C9D 9E9FA0A1 A2A3 A4A5 A6A7A8A9 AAAB ACAD AEAFB0B1 B2B3 B4B5 B6B7B8B9 BABB BCBD BEBFC0C1 C2C3 C4C5 C6C7C8C9 CACB CCCD CECFD0D1 D2D3 D4D5 D6D7D8D9 DADB DCDD DEDFE0E1 E2E3 E4E5 E6E7E8E9 EAEB ECED EEEFF0F1 F2F3 F4F5 F6F7F8F9 FAFB FCFD FEFF
  END


=head3 PrintMemory()

Print the memory addressed by rax for a length of rdi on the specified channel


B<Example:>


    ReadFile(V(file, Rs($0)), (my $s = V(size)), my $a = V(address));             # Read file
    $a->setReg(rax);                                                              # Address of file in memory
    $s->setReg(rdi);                                                              # Length  of file in memory
    PrintOutMemory;                                                               # Print contents of memory to stdout

    my $r = Assemble;                                                             # Assemble and execute
    ok stringMd5Sum($r) eq fileMd5Sum($0);                                        # Output contains this file


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

    Exit(0);

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


    my $N = V(size, 2048);
    my $q = Rs('a'..'p');

    AllocateMemory($N, my $address = V(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


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

    my $N = V(size, 4096);                                                        # Size of the initial allocation which should be one or more pages


    AllocateMemory($N, my $A = V(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


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

    AllocateMemory(K(size, $N), my $a = V(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CopyMemory(V(source, $s), V(size, $N), target => $a);


    AllocateMemory(K(size, $N), my $b = V(address));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CopyMemory(source => $a, target => $b, K(size, $N));

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


    my $N = V(size, 4096);                                                        # Size of the initial allocation which should be one or more pages

    AllocateMemory($N, my $A = V(address));

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


    my $N = V(size, 4096);                                                        # Size of the initial allocation which should be one or more pages

    AllocateMemory($N, my $A = V(address));


    ClearMemory($N, $A);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    $A->setReg(rax);
    $N->setReg(rdi);
    PrintOutMemoryInHexNL;

    FreeMemory($N, $A);

    ok Assemble(eq => <<END);
  0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head3 MaskMemory22(@variables)

Write the specified byte into locations in the target mask that correspond to the locations in the source that contain the specified byte.

     Parameter   Description
  1  @variables  Variables

=head3 MaskMemoryInRange4_22(@variables)

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

    CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutMemoryInHex;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(xmm1: 0000 0000 0000 0004   0000 0003 0002 0100);
    ok $r =~ m(0001 0200 0300 00000400 0000 0000 0000);

    my $N = 256;
    my $s = Rb 0..$N-1;
    AllocateMemory(K(size, $N), my $a = V(address));

    CopyMemory(V(source, $s), V(size, $N), target => $a);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    AllocateMemory(K(size, $N), my $b = V(address));

    CopyMemory(source => $a, target => $b, K(size, $N));  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


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



    ReadFile(V(file, Rs($0)), (my $s = V(size)), my $a = V(address));             # Read file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->setReg(rax);                                                              # Address of file in memory
    $s->setReg(rdi);                                                              # Length  of file in memory
    PrintOutMemory;                                                               # Print contents of memory to stdout

    my $r = Assemble;                                                             # Assemble and execute
    ok stringMd5Sum($r) eq fileMd5Sum($0);                                        # Output contains this file


=head3 executeFileViaBash(@variables)

Execute the file named in the arena addressed by rax with bash

     Parameter   Description
  1  @variables  Variables

B<Example:>


    my $s = CreateArena;                                                          # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write         (my $f = V('file', Rs("zzz.sh")));                          # Write code to a file

    executeFileViaBash($f);                                                       # Execute the file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    unlinkFile        ($f);                                                       # Delete the file

    my $u = qx(whoami); chomp($u);
    ok Assemble(emulator=>0) =~ m($u);                                            # The Intel Software Development Emulator is way too slow on these operations.


=head3 unlinkFile(@variables)

Unlink the named file

     Parameter   Description
  1  @variables  Variables

B<Example:>


    my $s = CreateArena;                                                          # Create a string
    $s->ql(<<END);                                                                # Write code to execute
  #!/usr/bin/bash
  whoami
  ls -la
  pwd
  END
    $s->write         (my $f = V('file', Rs("zzz.sh")));                          # Write code to a file
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


    if (0)                                                                        # Hash various strings  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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


    my @p = my ($out, $size, $fail) = (V(out), V(size), V('fail'));

    my $Chars = Rb(0x24, 0xc2, 0xa2, 0xc9, 0x91, 0xE2, 0x82, 0xAC, 0xF0, 0x90, 0x8D, 0x88);
    my $chars = V(chars, $Chars);

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
AAAAAAAA);                        # A sample sentence to parse

    my $s = K(statement, Rs($statement));
    my $l = K(size,  length($statement));

    AllocateMemory($l, my $address = V(address));                                 # Allocate enough memory for a copy of the string
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
  END


=head2 ClassifyInRange(@parameters)

Character classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with each word in zmm1 having the classification in the highest 8 bits and with zmm0 and zmm1 having the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.  The classification bits from the first matching range are copied into the high (unused) byte of each utf32 character in the block of memory.

     Parameter    Description
  1  @parameters  Parameters

=head2 ClassifyWithInRange(@parameters)

Bracket classification: Classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification range in the highest 8 bits of zmm0 and zmm1 and the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.  The classification bits from the position within the first matching range are copied into the high (unused) byte of each utf32 character in the block of memory.

     Parameter    Description
  1  @parameters  Parameters

=head2 ClassifyWithInRangeAndSaveOffset(@parameters)

Alphabetic classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification code in the high byte of zmm1 and the offset of the first element in the range in the high byte of zmm0.  The lowest 21 bits of each double word in zmm0 and zmm1  contain the utf32 characters marking the start and end of each range. The classification bits from zmm1 for the first matching range are copied into the high byte of each utf32 character in the block of memory.  The offset in the range is copied into the lowest byte of each utf32 character in the block of memory.  The middle two bytes are cleared.  The net effect is to reduce 21 bits of utf32 to 16 bits.

     Parameter    Description
  1  @parameters  Parameters

=head1 Short Strings

Operations on Short Strings

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

=head1 Arenas

An arena is single extensible block of memory which contains other data structures such as strings, arrays, trees within it.

=head2 StringLength(@parameters)

Length of a zero terminated string

     Parameter    Description
  1  @parameters  Parameters

B<Example:>



    StringLength(V(string, Rs("abcd")))->outNL;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Assemble(debug => 0, eq => <<END);
  size: 0000 0000 0000 0004
  END


=head2 CreateArena(%options)

Create an relocatable arena and returns its address in rax. Optionally add a chain header so that 64 byte blocks of memory can be freed and reused within the arena.

     Parameter  Description
  1  %options   Free=>1 adds a free chain.

B<Example:>



    my $a = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('aa');
    $a->out;
    PrintOutNL;
    is_deeply Assemble, <<END;                                                    # Assemble and execute
  aa
  END


    my $a = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $b = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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


    my $a = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $b = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('aa');
    $a->q('AA');
    $a->out;
    PrintOutNL;
    is_deeply Assemble, <<END;                                                    # Assemble and execute
  aaAA
  END


    my $a = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    my $b = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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


    my $a = CreateArena;                                                     # Create a string  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $a->q('ab');

    my $b = CreateArena;                                                     # Create target arena  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);
    $a->append(source=>$b->bs);
    $b->append(source=>$a->bs);
    $a->append(source=>$b->bs);
    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);
    $b->append(source=>$a->bs);


    $a->out;   PrintOutNL;                                                        # Print arena
    $b->out;   PrintOutNL;                                                        # Print arena
    $a->length(my $sa = V(size)); $sa->outNL;
    $b->length(my $sb = V(size)); $sb->outNL;
    $a->clear;
    $a->length(my $sA = V(size)); $sA->outNL;
    $b->length(my $sB = V(size)); $sB->outNL;

    is_deeply Assemble, <<END;                                                    # Assemble and execute
  abababababababab
  ababababababababababababababababababababababababababababababababababababab
  size: 0000 0000 0000 0010
  size: 0000 0000 0000 004A
  size: 0000 0000 0000 0000
  size: 0000 0000 0000 004A
  END


=head2 Nasm::X86::Arena::length($arena, @variables)

Get the length of an arena

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

=head2 Nasm::X86::Arena::makeReadOnly($arena)

Make an arena read only

     Parameter  Description
  1  $arena     Arena descriptor

=head2 Nasm::X86::Arena::makeWriteable($arena)

Make an arena writable

     Parameter  Description
  1  $arena     Arena descriptor

=head2 Nasm::X86::Arena::allocate($arena, @variables)

Allocate the amount of space indicated in rdi in the arena addressed by rax and return the offset of the allocation in the arena in rdi

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

=head2 Nasm::X86::Arena::allocZmmBlock($arena, @variables)

Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

     Parameter   Description
  1  $arena      Arena
  2  @variables  Variables

=head2 Nasm::X86::Arena::allocBlock($arena)

Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

     Parameter  Description
  1  $arena     Arena

B<Example:>


    my $a = CreateArena; $a->dump;
    my $b1 = $a->allocBlock;  $a->dump;
    my $b2 = $a->allocBlock;  $a->dump;
    $a->freeBlock($b2);       $a->dump;
    $a->freeBlock($b1);       $a->dump;

    ok Assemble(debug => 0, eq => <<END);
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0018
  0000: 0010 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0058
  0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head2 Nasm::X86::Arena::m($arena, @variables)

Append the content with length rdi addressed by rsi to the arena addressed by rax

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

=head2 Nasm::X86::Arena::q($arena, $string)

Append a constant string to the arena

     Parameter  Description
  1  $arena     Arena descriptor
  2  $string    String

=head2 Nasm::X86::Arena::ql($arena, $const)

Append a quoted string containing new line characters to the arena addressed by rax

     Parameter  Description
  1  $arena     Arena
  2  $const     Constant

=head2 Nasm::X86::Arena::char($arena, $char)

Append a character expressed as a decimal number to the arena addressed by rax

     Parameter  Description
  1  $arena     Arena descriptor
  2  $char      Number of character to be appended

=head2 Nasm::X86::Arena::nl($arena)

Append a new line to the arena addressed by rax

     Parameter  Description
  1  $arena     Arena descriptor

=head2 Nasm::X86::Arena::z($arena)

Append a trailing zero to the arena addressed by rax

     Parameter  Description
  1  $arena     Arena descriptor

=head2 Nasm::X86::Arena::append($arena, @variables)

Append one arena to another

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

=head2 Nasm::X86::Arena::clear($arena)

Clear the arena addressed by rax

     Parameter  Description
  1  $arena     Arena descriptor

=head2 Nasm::X86::Arena::write($arena, @variables)

Write the content in an arena addressed by rax to a temporary file and replace the arena content with the name of the  temporary file

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

=head2 Nasm::X86::Arena::read($arena, @variables)

Read the named file (terminated with a zero byte) and place it into the named arena.

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

=head2 Nasm::X86::Arena::out($arena)

Print the specified arena addressed by rax on sysout

     Parameter  Description
  1  $arena     Arena descriptor

=head2 Nasm::X86::Arena::dump($arena, $depth)

Dump details of an arena

     Parameter  Description
  1  $arena     Arena descriptor
  2  $depth     Optional amount of memory to dump  as the number of 64 byte blocks

=head1 String

Strings made from zmm sized blocks of text

=head2 Nasm::X86::Arena::CreateString($arena)

Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the arena addressed by rax and return its descriptor

     Parameter  Description
  1  $arena     Arena description

=head2 Nasm::X86::String::dump($String)

Dump a string to sysout

     Parameter  Description
  1  $String    String descriptor

=head2 Nasm::X86::String::len($String, $size)

Find the length of a string

     Parameter  Description
  1  $String    String descriptor
  2  $size      Size variable

=head2 Nasm::X86::String::concatenate($target, $source)

Concatenate two strings by appending a copy of the source to the target string.

     Parameter  Description
  1  $target    Target string
  2  $source    Source string

=head2 Nasm::X86::String::insertChar($String, @variables)

Insert a character into a string

     Parameter   Description
  1  $String     String
  2  @variables  Variables

=head2 Nasm::X86::String::deleteChar($String, @variables)

Delete a character in a string

     Parameter   Description
  1  $String     String
  2  @variables  Variables

=head2 Nasm::X86::String::getCharacter($String, @variables)

Get a character from a string

     Parameter   Description
  1  $String     String
  2  @variables  Variables

=head2 Nasm::X86::String::append($String, @variables)

Append the specified content in memory to the specified string

     Parameter   Description
  1  $String     String descriptor
  2  @variables  Variables

=head2 Nasm::X86::String::clear($String)

Clear the block by freeing all but the first block

     Parameter  Description
  1  $String    String descriptor

=head1 Array

Array constructed as a set of blocks in an arena

=head2 Nasm::X86::Arena::CreateArray($arena)

Create a array in an arena

     Parameter  Description
  1  $arena     Arena description

=head2 Nasm::X86::Array::dump($Array, @variables)

Dump a array

     Parameter   Description
  1  $Array      Array descriptor
  2  @variables  Variables

=head2 Nasm::X86::Array::push($Array, @variables)

Push an element onto the array

     Parameter   Description
  1  $Array      Array descriptor
  2  @variables  Variables

=head2 Nasm::X86::Array::pop($Array, @variables)

Pop an element from an array

     Parameter   Description
  1  $Array      Array descriptor
  2  @variables  Variables

=head2 Nasm::X86::Array::get($Array, @variables)

Get an element from the array

     Parameter   Description
  1  $Array      Array descriptor
  2  @variables  Variables

=head2 Nasm::X86::Array::put($Array, @variables)

Put an element into an array as long as it is with in its limits established by pushing.

     Parameter   Description
  1  $Array      Array descriptor
  2  @variables  Variables

=head1 Tree

Tree constructed as sets of blocks in an arena.

=head2 Nasm::X86::Arena::DescribeTree($arena)

Return a descriptor for a tree in the specified arena

     Parameter  Description
  1  $arena     Arena descriptor

=head2 Nasm::X86::Arena::CreateTree($arena)

Create a tree in an arena.

     Parameter  Description
  1  $arena     Arena description

B<Example:>


    my $N = 12;
    my $b = CreateArena;                                                     # Resizable memory block
    my $t = $b->CreateTree;                                          # Multi way tree in memory block

    K(count, $N)->for(sub                                                         # Add some entries to the tree
     {my ($index, $start, $next, $end) = @_;
      my $k = $index + 1;
      $t->insert($k,      $k + 0x100);
      $t->insert($k + $N, $k + 0x200);
     });

    $t->by(sub                                                                    # Iterate through the tree
     {my ($iter, $end) = @_;
      $iter->key ->out('key: ');
      $iter->data->out(' data: ');
      $iter->tree->depth($iter->node, my $D = V(depth));

      $t->find($iter->key);
      $t->found->out(' found: '); $t->data->out(' data: '); $D->outNL(' depth: ');
     });

    $t->find(K(key, 0xffff));  $t->found->outNL('Found: ');                      # Find some entries
    $t->find(K(key, 0xd));     $t->found->outNL('Found: ');
    If ($t->found,
    Then
     {$t->data->outNL("Data : ");
     });

    ok Assemble(debug => 0, eq => <<END);
  key: 0000 0000 0000 0001 data: 0000 0000 0000 0101 found: 0000 0000 0000 0001 data: 0000 0000 0000 0101 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0002 data: 0000 0000 0000 0102 found: 0000 0000 0000 0001 data: 0000 0000 0000 0102 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0003 data: 0000 0000 0000 0103 found: 0000 0000 0000 0001 data: 0000 0000 0000 0103 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0004 data: 0000 0000 0000 0104 found: 0000 0000 0000 0001 data: 0000 0000 0000 0104 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0005 data: 0000 0000 0000 0105 found: 0000 0000 0000 0001 data: 0000 0000 0000 0105 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0006 data: 0000 0000 0000 0106 found: 0000 0000 0000 0001 data: 0000 0000 0000 0106 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0007 data: 0000 0000 0000 0107 found: 0000 0000 0000 0001 data: 0000 0000 0000 0107 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0008 data: 0000 0000 0000 0108 found: 0000 0000 0000 0001 data: 0000 0000 0000 0108 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0009 data: 0000 0000 0000 0109 found: 0000 0000 0000 0001 data: 0000 0000 0000 0109 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000A data: 0000 0000 0000 010A found: 0000 0000 0000 0001 data: 0000 0000 0000 010A depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000B data: 0000 0000 0000 010B found: 0000 0000 0000 0001 data: 0000 0000 0000 010B depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000C data: 0000 0000 0000 010C found: 0000 0000 0000 0001 data: 0000 0000 0000 010C depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000D data: 0000 0000 0000 0201 found: 0000 0000 0000 0001 data: 0000 0000 0000 0201 depth: 0000 0000 0000 0001
  key: 0000 0000 0000 000E data: 0000 0000 0000 0202 found: 0000 0000 0000 0001 data: 0000 0000 0000 0202 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000F data: 0000 0000 0000 0203 found: 0000 0000 0000 0001 data: 0000 0000 0000 0203 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0010 data: 0000 0000 0000 0204 found: 0000 0000 0000 0001 data: 0000 0000 0000 0204 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0011 data: 0000 0000 0000 0205 found: 0000 0000 0000 0001 data: 0000 0000 0000 0205 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0012 data: 0000 0000 0000 0206 found: 0000 0000 0000 0001 data: 0000 0000 0000 0206 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0013 data: 0000 0000 0000 0207 found: 0000 0000 0000 0001 data: 0000 0000 0000 0207 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0014 data: 0000 0000 0000 0208 found: 0000 0000 0000 0001 data: 0000 0000 0000 0208 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0015 data: 0000 0000 0000 0209 found: 0000 0000 0000 0001 data: 0000 0000 0000 0209 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0016 data: 0000 0000 0000 020A found: 0000 0000 0000 0001 data: 0000 0000 0000 020A depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0017 data: 0000 0000 0000 020B found: 0000 0000 0000 0001 data: 0000 0000 0000 020B depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0018 data: 0000 0000 0000 020C found: 0000 0000 0000 0001 data: 0000 0000 0000 020C depth: 0000 0000 0000 0002
  Found: 0000 0000 0000 0000
  Found: 0000 0000 0000 0001
  Data : 0000 0000 0000 0201
  END


=head2 Nasm::X86::Tree::Clone($tree)

Clone the specified tree descriptions

     Parameter  Description
  1  $tree      Tree descriptor

B<Example:>


    my $L = K(loop, 4);
    my $b = CreateArena;
    my $T = $b->CreateTree;
    my $t = $T->Clone;

    $L->for(sub
     {my ($i, $start, $next, $end) = @_;
      $t->insertTreeAndClone($i);
      $t->first->outNL;
     });

    $t->insert($L, $L*2);

    my $f = $T->Clone;
    $L->for(sub
     {my ($i, $start, $next, $end) = @_;
      $f->findAndClone($i);
      $i->out('i: '); $f->found->out('  f: '); $f->data->out('  d: '); $f->subTree->outNL('  s: ');
     });
    $f->find($L);
    $L->out('N: '); $f->found->out('  f: '); $f->data->out('  d: ');   $f->subTree->outNL('  s: ');

    ok Assemble(debug => 0, eq => <<END);
  first: 0000 0000 0000 0098
  first: 0000 0000 0000 0118
  first: 0000 0000 0000 0198
  first: 0000 0000 0000 0218
  i: 0000 0000 0000 0000  f: 0000 0000 0000 0001  d: 0000 0000 0000 0098  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0001  f: 0000 0000 0000 0001  d: 0000 0000 0000 0118  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0002  f: 0000 0000 0000 0001  d: 0000 0000 0000 0198  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0003  f: 0000 0000 0000 0001  d: 0000 0000 0000 0218  s: 0000 0000 0000 0001
  N: 0000 0000 0000 0004  f: 0000 0000 0000 0001  d: 0000 0000 0000 0008  s: 0000 0000 0000 0000
  END


=head2 Nasm::X86::Tree::find($t, $key)

Find a key in a tree and test whether the found data is a sub tree.  The results are held in the variables "found", "data", "subTree" addressed by the tree descriptor.

     Parameter  Description
  1  $t         Tree descriptor
  2  $key       Key field to search for

=head2 Nasm::X86::Tree::findAndClone($t, $key)

Find a key in the specified tree and clone it is it is a sub tree.

     Parameter  Description
  1  $t         Tree descriptor
  2  $key       Key as a dword

B<Example:>


    my $L = K(loop, 4);
    my $b = CreateArena;
    my $T = $b->CreateTree;
    my $t = $T->Clone;

    $L->for(sub
     {my ($i, $start, $next, $end) = @_;
      $t->insertTreeAndClone($i);
      $t->first->outNL;
     });

    $t->insert($L, $L*2);

    my $f = $T->Clone;
    $L->for(sub
     {my ($i, $start, $next, $end) = @_;
      $f->findAndClone($i);
      $i->out('i: '); $f->found->out('  f: '); $f->data->out('  d: '); $f->subTree->outNL('  s: ');
     });
    $f->find($L);
    $L->out('N: '); $f->found->out('  f: '); $f->data->out('  d: ');   $f->subTree->outNL('  s: ');

    ok Assemble(debug => 0, eq => <<END);
  first: 0000 0000 0000 0098
  first: 0000 0000 0000 0118
  first: 0000 0000 0000 0198
  first: 0000 0000 0000 0218
  i: 0000 0000 0000 0000  f: 0000 0000 0000 0001  d: 0000 0000 0000 0098  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0001  f: 0000 0000 0000 0001  d: 0000 0000 0000 0118  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0002  f: 0000 0000 0000 0001  d: 0000 0000 0000 0198  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0003  f: 0000 0000 0000 0001  d: 0000 0000 0000 0218  s: 0000 0000 0000 0001
  N: 0000 0000 0000 0004  f: 0000 0000 0000 0001  d: 0000 0000 0000 0008  s: 0000 0000 0000 0000
  END


=head2 Nasm::X86::Tree::insertDataOrTree($t, $tnd, $key, $data)

Insert either a key, data pair into the tree or create a sub tree at the specified key (if it does not already exist) and return the offset of the first block of the sub tree in the data variable.

     Parameter  Description
  1  $t         Tree descriptor
  2  $tnd       0 - data or 1 - tree
  3  $key       Key as a dword
  4  $data      Data as a dword

=head2 Nasm::X86::Tree::insert($t, $key, $data)

Insert a dword into into the specified tree at the specified key.

     Parameter  Description
  1  $t         Tree descriptor
  2  $key       Key as a dword
  3  $data      Data as a dword

=head2 Nasm::X86::Tree::insertTree($t, $key, $subTree)

Insert a sub tree into the specified tree tree under the specified key. If no sub tree is supplied an empty one is provided gratis.

     Parameter  Description
  1  $t         Tree descriptor
  2  $key       Key as a dword
  3  $subTree   Sub tree to insert else an empty one will be added

B<Example:>


    my $b = CreateArena;
    my $t = $b->CreateTree;
    my $T = $b->CreateTree;

    $T->insert    (K(key, 2), K(data, 4));
    $t->insertTree(K(key, 1), $T);

    $t->print;

    ok Assemble(debug => 0, eq => <<END);
  Tree at:    r15: 0000 0000 0000 0018
  key: 0000 0000 0000 0001 data: 0000 0000 0000 0098 depth: 0000 0000 0000 0001
  Tree at:    r15: 0000 0000 0000 0098
  key: 0000 0000 0000 0002 data: 0000 0000 0000 0004 depth: 0000 0000 0000 0001
  END


=head2 Nasm::X86::Tree::insertTreeAndClone($t, $key)

Insert a new sub tree into the specified tree tree under the specified key and return a descriptor for it.  If the tree already exists, return a descriptor for it.

     Parameter  Description
  1  $t         Tree descriptor
  2  $key       Key as a dword

B<Example:>


    my $L = K(loop, 4);
    my $b = CreateArena;
    my $T = $b->CreateTree;
    my $t = $T->Clone;

    $L->for(sub
     {my ($i, $start, $next, $end) = @_;
      $t->insertTreeAndClone($i);
      $t->first->outNL;
     });

    $t->insert($L, $L*2);

    my $f = $T->Clone;
    $L->for(sub
     {my ($i, $start, $next, $end) = @_;
      $f->findAndClone($i);
      $i->out('i: '); $f->found->out('  f: '); $f->data->out('  d: '); $f->subTree->outNL('  s: ');
     });
    $f->find($L);
    $L->out('N: '); $f->found->out('  f: '); $f->data->out('  d: ');   $f->subTree->outNL('  s: ');

    ok Assemble(debug => 0, eq => <<END);
  first: 0000 0000 0000 0098
  first: 0000 0000 0000 0118
  first: 0000 0000 0000 0198
  first: 0000 0000 0000 0218
  i: 0000 0000 0000 0000  f: 0000 0000 0000 0001  d: 0000 0000 0000 0098  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0001  f: 0000 0000 0000 0001  d: 0000 0000 0000 0118  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0002  f: 0000 0000 0000 0001  d: 0000 0000 0000 0198  s: 0000 0000 0000 0001
  i: 0000 0000 0000 0003  f: 0000 0000 0000 0001  d: 0000 0000 0000 0218  s: 0000 0000 0000 0001
  N: 0000 0000 0000 0004  f: 0000 0000 0000 0001  d: 0000 0000 0000 0008  s: 0000 0000 0000 0000
  END


=head2 Nasm::X86::Tree::leftOrRightMost($t, $dir, @variables)

Return the left most or right most node

     Parameter   Description
  1  $t          Tree descriptor
  2  $dir        Direction: left = 0 or right = 1
  3  @variables  Variables

=head2 Nasm::X86::Tree::leftMost($t, @variables)

Return the left most node

     Parameter   Description
  1  $t          Tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::Tree::rightMost($t, @variables)

Return the right most node

     Parameter   Description
  1  $t          Tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::Tree::depth($t, @variables)

Return the depth of a node within a tree.

     Parameter   Description
  1  $t          Tree descriptor
  2  @variables  Variables

=head2 Sub trees

Construct trees of trees.

=head2 Print

Print a tree

=head3 Nasm::X86::Tree::print($t)

Print a tree

     Parameter  Description
  1  $t         Tree

B<Example:>


    my $L = V(loop, 45);
    my $b = CreateArena;
    my $t = $b->CreateTree;

    $L->for(sub
     {my ($i, $start, $next, $end) = @_;
      my $l = $L - $i;
      If ($i % 2 == 0, sub
       {$t->insert($i, $l);
        $t->insertTree($l);
       });
     });

    $t->print;

    ok Assemble(debug => 0, eq => <<END);
  Tree at:    r15: 0000 0000 0000 0018
  key: 0000 0000 0000 0000 data: 0000 0000 0000 002D depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0001 data: 0000 0000 0000 0ED8 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0002 data: 0000 0000 0000 002B depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0003 data: 0000 0000 0000 0E58 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0004 data: 0000 0000 0000 0029 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0005 data: 0000 0000 0000 0DD8 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0006 data: 0000 0000 0000 0027 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0007 data: 0000 0000 0000 0D58 depth: 0000 0000 0000 0001
  key: 0000 0000 0000 0008 data: 0000 0000 0000 0025 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0009 data: 0000 0000 0000 0CD8 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000A data: 0000 0000 0000 0023 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000B data: 0000 0000 0000 0C58 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000C data: 0000 0000 0000 0021 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000D data: 0000 0000 0000 0BD8 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 000E data: 0000 0000 0000 001F depth: 0000 0000 0000 0001
  key: 0000 0000 0000 000F data: 0000 0000 0000 0B58 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0010 data: 0000 0000 0000 001D depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0011 data: 0000 0000 0000 0AD8 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0012 data: 0000 0000 0000 001B depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0013 data: 0000 0000 0000 0998 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0014 data: 0000 0000 0000 0019 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0015 data: 0000 0000 0000 0918 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0016 data: 0000 0000 0000 0017 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0017 data: 0000 0000 0000 0898 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0018 data: 0000 0000 0000 0015 depth: 0000 0000 0000 0001
  key: 0000 0000 0000 0019 data: 0000 0000 0000 0818 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 001A data: 0000 0000 0000 0013 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 001B data: 0000 0000 0000 06D8 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 001C data: 0000 0000 0000 0011 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 001D data: 0000 0000 0000 0658 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 001E data: 0000 0000 0000 000F depth: 0000 0000 0000 0002
  key: 0000 0000 0000 001F data: 0000 0000 0000 05D8 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0020 data: 0000 0000 0000 000D depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0021 data: 0000 0000 0000 0398 depth: 0000 0000 0000 0001
  key: 0000 0000 0000 0022 data: 0000 0000 0000 000B depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0023 data: 0000 0000 0000 0318 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0024 data: 0000 0000 0000 0009 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0025 data: 0000 0000 0000 0298 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0026 data: 0000 0000 0000 0007 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0027 data: 0000 0000 0000 0218 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0028 data: 0000 0000 0000 0005 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 0029 data: 0000 0000 0000 0198 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 002A data: 0000 0000 0000 0003 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 002B data: 0000 0000 0000 0118 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 002C data: 0000 0000 0000 0001 depth: 0000 0000 0000 0002
  key: 0000 0000 0000 002D data: 0000 0000 0000 0098 depth: 0000 0000 0000 0002
  Tree at:    r15: 0000 0000 0000 0098
  Tree at:    r15: 0000 0000 0000 0118
  Tree at:    r15: 0000 0000 0000 0198
  Tree at:    r15: 0000 0000 0000 0218
  Tree at:    r15: 0000 0000 0000 0298
  Tree at:    r15: 0000 0000 0000 0318
  Tree at:    r15: 0000 0000 0000 0398
  Tree at:    r15: 0000 0000 0000 05D8
  Tree at:    r15: 0000 0000 0000 0658
  Tree at:    r15: 0000 0000 0000 06D8
  Tree at:    r15: 0000 0000 0000 0818
  Tree at:    r15: 0000 0000 0000 0898
  Tree at:    r15: 0000 0000 0000 0918
  Tree at:    r15: 0000 0000 0000 0998
  Tree at:    r15: 0000 0000 0000 0AD8
  Tree at:    r15: 0000 0000 0000 0B58
  Tree at:    r15: 0000 0000 0000 0BD8
  Tree at:    r15: 0000 0000 0000 0C58
  Tree at:    r15: 0000 0000 0000 0CD8
  Tree at:    r15: 0000 0000 0000 0D58
  Tree at:    r15: 0000 0000 0000 0DD8
  Tree at:    r15: 0000 0000 0000 0E58
  Tree at:    r15: 0000 0000 0000 0ED8
  END


=head2 Iteration

Iterate through a tree non recursively

=head3 Nasm::X86::Tree::iterator($b)

Iterate through a multi way tree

     Parameter  Description
  1  $b         Tree

=head3 Nasm::X86::Tree::Iterator::next($iter)

Next element in the tree

     Parameter  Description
  1  $iter      Iterator

=head3 Nasm::X86::Tree::by($b, $body)

Call the specified body with each (key, data) from the specified tree in order

     Parameter  Description
  1  $b         Tree descriptor
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

B<Example:>


    Comment "Print a string from memory";
    my $s = "Hello World";
    Mov rax, Rs($s);
    Mov rdi, length $s;
    PrintOutMemory;

    Exit(0);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(Hello World);


=head2 Assemble(%options)

Assemble the generated code.

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

Arena definition.

=head4 constant

Constant if true

=head4 count

Counter - number of node

=head4 data

Data at this position

=head4 expr

Expression that initializes the variable

=head4 first

Variable addressing offset to first block of keys.

=head4 found

Variable indicating whether the last find was successful or not

=head4 free

Free chain offset

=head4 key

Key at this position

=head4 label

Address in memory

=head4 leftLength

Left split length

=head4 length

Maximum length in a block

=head4 lengthOffset

Offset of length in keys block.  The length field is a word - see: "MultiWayTree.svg"

=head4 links

Location of links in bytes in zmm

=head4 loop

Offset of keys, data, node loop.

=head4 maxKeys

Maximum number of keys.

=head4 more

Iteration not yet finished

=head4 name

Name of the variable

=head4 next

Location of next offset in block in bytes

=head4 node

Current node within tree

=head4 pos

Current position within node

=head4 prev

Location of prev offset in block in bytes

=head4 purpose

Purpose of this variable

=head4 reference

Reference to another variable

=head4 rightLength

Right split length

=head4 size

Size field details

=head4 slots1

Number of slots in first block

=head4 slots2

Number of slots in second and subsequent blocks

=head4 splittingKey

POint at which to split a full block

=head4 structure

Structure details

=head4 subTree

Variable indicating whether the last find found a sub tree

=head4 tree

Tree we are iterating over

=head4 treeBits

Offset of tree bits in keys block.  The tree bits field is a word, each bit of which tells us whether the corresponding data element is the offset (or not) to a sub tree of this tree .

=head4 treeBitsMask

14 tree bits

=head4 up

Offset of up in data block.

=head4 used

Used field details

=head4 width

Width of a key or data slot.



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


=head2 Nasm::X86::Variable::dump($left, $channel, $newLine, $title1, $title2)

Dump the value of a variable to the specified channel adding an optional title and new line if requested

     Parameter  Description
  1  $left      Left variable
  2  $channel   Channel
  3  $newLine   New line required
  4  $title1    Optional leading title
  5  $title2    Optional trailing title

B<Example:>


    my $a = V(a, 3);  $a->outNL;
    my $b = K(b, 2);  $b->outNL;
    my $c = $a +  $b; $c->outNL;
    my $d = $c -  $a; $d->outNL;
    my $e = $d == $b; $e->outNL;
    my $f = $d != $b; $f->outNL;
    my $g = $a *  $b; $g->outNL;
    my $h = $g /  $b; $h->outNL;
    my $i = $a %  $b; $i->outNL;

    If ($a == 3,
    Then
     {PrintOutStringNL "a == 3"
     },
    Else
     {PrintOutStringNL "a != 3"
     });

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
  1  $recordOffsetInRange  Record offset in classification in high byte if 1 else in classification if 2
  2  @parameters           Parameters

=head2 PrintUtf32($n, $m)

Print the specified number of utf32 characters at the specified address

     Parameter  Description
  1  $n         Variable: number of characters to print
  2  $m         Variable: address of memory

=head2 Cstrlen()

Length of the C style string addressed by rax returning the length in r15


=head2 Nasm::X86::Arena::chain($arena, $bs, $variable, @offsets)

Return a variable with the end point of a chain of double words in the arena starting at the specified variable.

     Parameter  Description
  1  $arena     Arena descriptor
  2  $bs        Arena locator
  3  $variable  Start variable
  4  @offsets   Offsets chain

B<Example:>


    my $format = Rd(map{4*$_+24} 0..64);

    my $b = CreateArena;
    my $a = $b->allocBlock;
    Vmovdqu8 zmm31, "[$format]";
    $b->putBlock($b->bs, $a, 31);
    my $r = $b->chain($b->bs, V(start, 0x18), 4);       $r->outNL("chain1: ");
    my $s = $b->chain($b->bs, $r, 4);                   $s->outNL("chain2: ");
    my $t = $b->chain($b->bs, $s, 4);                   $t->outNL("chain3: ");
    my $A = $b->chain($b->bs, V(start, 0x18), 4, 4, 4); $A->outNL("chain4: ");    # Get a long chain

    $b->putChain($b->bs, V(start, 0x18), V(end, 0xff), 4, 4, 4);                  # Put at the end of a long chain

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
     } name=> 'aaa', in => [qw(c)], io => [qw(d  e  f)];

    my $c = K(c, -1);
    my $d = K(d, -1);
    my $e = V(e,  1);
    my $f = V(f,  2);

    $sub->call($c, $d, $e, $f);
    $f->outNL('F3: ');

    ok Assemble(debug => 0, eq => <<END);
  chain1: 0000 0000 0000 001C
  chain2: 0000 0000 0000 0020
  chain3: 0000 0000 0000 0024
  chain4: 0000 0000 0000 0024
  Arena
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


=head2 Nasm::X86::Arena::putChain($arena, $bs, $start, $value, @offsets)

Write the double word in the specified variable to the double word location at the the specified offset in the specified arena.

     Parameter  Description
  1  $arena     Arena descriptor
  2  $bs        Arena locator variable
  3  $start     Start variable
  4  $value     Value to put as a variable
  5  @offsets   Offsets chain

=head2 Nasm::X86::Arena::updateSpace($arena, @variables)

Make sure that the arena addressed by rax has enough space to accommodate content of length rdi

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

=head2 Nasm::X86::Arena::blockSize($arena)

Size of a block

     Parameter  Description
  1  $arena     Arena

=head2 Nasm::X86::Arena::firstFreeBlock($arena)

Create and load a variable with the first free block on the free block chain or zero if no such block in the given arena

     Parameter  Description
  1  $arena     Arena address as a variable

=head2 Nasm::X86::Arena::setFirstFreeBlock($arena, $offset)

Set the first free block field from a variable

     Parameter  Description
  1  $arena     Arena descriptor
  2  $offset    First free block offset as a variable

=head2 Nasm::X86::Arena::freeBlock($arena, @variables)

Free a block in an arena by placing it on the free chain

     Parameter   Description
  1  $arena      Arena descriptor
  2  @variables  Variables

B<Example:>


    my $a = CreateArena; $a->dump;
    my $b1 = $a->allocBlock;  $a->dump;
    my $b2 = $a->allocBlock;  $a->dump;
    $a->freeBlock($b2);       $a->dump;
    $a->freeBlock($b1);       $a->dump;

    ok Assemble(debug => 0, eq => <<END);
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0018
  0000: 0010 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0058
  0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  Arena
    Size: 0000 0000 0000 1000
    Used: 0000 0000 0000 0098
  0000: 0010 0000 0000 00009800 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
  END


=head2 Nasm::X86::Arena::getBlock($arena, $bsa, $block, $zmm)

Get the block with the specified offset in the specified string and return it in the numbered zmm

     Parameter  Description
  1  $arena     Arena descriptor
  2  $bsa       Arena variable
  3  $block     Offset of the block as a variable
  4  $zmm       Number of zmm register to contain block

=head2 Nasm::X86::Arena::putBlock($arena, $bsa, $block, $zmm)

Write the numbered zmm to the block at the specified offset in the specified arena

     Parameter  Description
  1  $arena     Arena descriptor
  2  $bsa       Arena variable
  3  $block     Block in arena
  4  $zmm       Content variable

=head2 Nasm::X86::String::address($String)

Address of a string

     Parameter  Description
  1  $String    String descriptor

=head2 Nasm::X86::String::allocBlock($String)

Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

     Parameter  Description
  1  $String    String descriptor

=head2 Nasm::X86::String::getBlockLength($String, $zmm)

Get the block length of the numbered zmm and return it in a variable

     Parameter  Description
  1  $String    String descriptor
  2  $zmm       Number of zmm register

=head2 Nasm::X86::String::setBlockLengthInZmm($String, $length, $zmm)

Set the block length of the numbered zmm to the specified length

     Parameter  Description
  1  $String    String descriptor
  2  $length    Length as a variable
  3  $zmm       Number of zmm register

=head2 Nasm::X86::String::getBlock($String, $bsa, $block, $zmm)

Get the block with the specified offset in the specified string and return it in the numbered zmm

     Parameter  Description
  1  $String    String descriptor
  2  $bsa       Arena variable
  3  $block     Offset of the block as a variable
  4  $zmm       Number of zmm register to contain block

=head2 Nasm::X86::String::putBlock($String, $bsa, $block, $zmm)

Write the numbered zmm to the block at the specified offset in the specified arena

     Parameter  Description
  1  $String    String descriptor
  2  $bsa       Arena variable
  3  $block     Block in arena
  4  $zmm       Content variable

=head2 Nasm::X86::String::getNextAndPrevBlockOffsetFromZmm($String, $zmm)

Get the offsets of the next and previous blocks as variables from the specified zmm

     Parameter  Description
  1  $String    String descriptor
  2  $zmm       Zmm containing block

=head2 Nasm::X86::String::putNextandPrevBlockOffsetIntoZmm($String, $zmm, $next, $prev)

Save next and prev offsets into a zmm representing a block

     Parameter  Description
  1  $String    String descriptor
  2  $zmm       Zmm containing block
  3  $next      Next offset as a variable
  4  $prev      Prev offset as a variable

=head2 Nasm::X86::Array::address($Array)

Address of a string

     Parameter  Description
  1  $Array     Array descriptor

=head2 Nasm::X86::Array::allocBlock($Array)

Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

     Parameter  Description
  1  $Array     Array descriptor

=head2 Nasm::X86::Tree::allocKeysDataNode($t, $K, $D, $N, @variables)

Allocate a keys/data/node block and place it in the numbered zmm registers

     Parameter   Description
  1  $t          Tree descriptor
  2  $K          Numbered zmm for keys
  3  $D          Numbered zmm for data
  4  $N          Numbered zmm for children
  5  @variables  Variables

=head2 Nasm::X86::Tree::splitNode($t, $bs, $node, $key, @variables)

Split a node given its offset in an arena retaining the key being inserted in the node split while putting the remainder to the left or right.

     Parameter   Description
  1  $t          Tree descriptor
  2  $bs         Backing arena
  3  $node       Offset of node
  4  $key        Key
  5  @variables  Variables

=head2 Nasm::X86::Tree::reParent($t, $bs, $PK, $PD, $PN, @variables)

Reparent the children of a node held in registers. The children are in the backing arena not registers.

     Parameter   Description
  1  $t          Tree descriptor
  2  $bs         Backing arena
  3  $PK         Numbered zmm key node
  4  $PD         Numbered zmm data node
  5  $PN         Numbered zmm child node
  6  @variables  Variables

=head2 Nasm::X86::Tree::transferTreeBitsFromParent($b, $parent, $left, $right)

Transfer tree bits when splitting a full node.

     Parameter  Description
  1  $b         Tree descriptor
  2  $parent    Numbered parent zmm
  3  $left      Numbered left zmm
  4  $right     Numbered right zmm

B<Example:>


    my $B = Rb(0..63);
    Vmovdqu8 zmm0, "[$B]";
    loadFromZmm r15, w, zmm, 14;

    my $b = CreateArena;
    my $t = $b->CreateTree;
    $t->getTreeBits(0, r14);

    PrintOutRegisterInHex zmm0, r15, r14;

    Mov r14, my $treeBits = 0xDCBA;
    $t->putTreeBits(1, r14);
    PrintOutRegisterInHex zmm1;

    $t->transferTreeBitsFromParent(1, 2, 3);
    PrintOutStringNL "Split:";
    PrintOutRegisterInHex zmm1, zmm2, zmm3;

    my $left  =  $treeBits & ((1<<$t->leftLength)  - 1);
    my $right = ($treeBits >>    ($t->leftLength   + 1)) & ((1<<$t->rightLength) - 1);

    my $l = sprintf("%02X", $left);
    my $r = sprintf("%02X", $right);

    ok Assemble(debug => 0, eq => <<END);
    zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
     r15: 0000 0000 0000 0F0E
     r14: 0000 0000 0000 3B3A
    zmm1: 0000 0000 DCBA 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  Split:
    zmm1: 0000 0000 0001 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm2: 0000 0000 00$l 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm3: 0000 0000 00$r 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  END


=head2 Nasm::X86::Tree::transferTreeBitsFromLeftOrRight($b, $rnl, $point, $parent, $left, $right)

Transfer tree bits when splitting a full left or right node.

     Parameter  Description
  1  $b         Tree descriptor
  2  $rnl       0 - left 1 - right
  3  $point     Register indicating point of left in parent
  4  $parent    Numbered parent zmm
  5  $left      Numbered left zmm
  6  $right     Numbered right zmm

=head2 Nasm::X86::Tree::transferTreeBitsFromLeft($b, $point, $parent, $left, $right)

Transfer tree bits when splitting a full left node

     Parameter  Description
  1  $b         Tree descriptor
  2  $point     Register indicating point of left in parent
  3  $parent    Numbered parent zmm
  4  $left      Numbered left zmm
  5  $right     Numbered right zmm

B<Example:>


    my $b = CreateArena;
    my $t = $b->CreateTree;
    my $lR = "110110";
    my $lP = "1";
    my $lL = "1110111";

    my $p1 = "01010_110010";
    my $p2 = "1";

    my $epe = sprintf("%04X", eval "0b$p1$lP$p2");
    my $ele = sprintf("%04X", eval "0b$lL"      );
    my $ere = sprintf("%04X", eval "0b$lR"      );

    my @expected;
    for my $i(0..1)
     {Mov r15, eval "0b$lR$lP$lL"; $t->putTreeBits(1+$i, r15);
      Mov r15, eval "0b$p1$p2";    $t->putTreeBits(0,    r15);

      PrintOutRegisterInHex zmm 0, 1+$i;

      Mov r15, 0b10;
      $t->transferTreeBitsFromLeft (r15, 0, 1, 2) unless $i;
      $t->transferTreeBitsFromRight(r15, 0, 1, 2) if     $i;
      PrintOutRegisterInHex zmm 0..2;

      my $zzz = $i ? "zmm2" : "zmm1";
      push @expected, <<END;
    zmm0: 0000 0000 0565 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    $zzz: 0000 0000 36F7 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm0: 0000 0000 $epe 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm1: 0000 0000 $ele 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm2: 0000 0000 $ere 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  END
     }

    ok Assemble(debug => 0, eq => join "", @expected);


=head2 Nasm::X86::Tree::transferTreeBitsFromRight($b, $point, $parent, $left, $right)

Transfer tree bits when splitting a full right node

     Parameter  Description
  1  $b         Tree descriptor
  2  $point     Register indicating point of right in parent
  3  $parent    Numbered parent zmm
  4  $left      Numbered left zmm
  5  $right     Numbered right zmm

B<Example:>


    my $b = CreateArena;
    my $t = $b->CreateTree;
    my $lR = "110110";
    my $lP = "1";
    my $lL = "1110111";

    my $p1 = "01010_110010";
    my $p2 = "1";

    my $epe = sprintf("%04X", eval "0b$p1$lP$p2");
    my $ele = sprintf("%04X", eval "0b$lL"      );
    my $ere = sprintf("%04X", eval "0b$lR"      );

    my @expected;
    for my $i(0..1)
     {Mov r15, eval "0b$lR$lP$lL"; $t->putTreeBits(1+$i, r15);
      Mov r15, eval "0b$p1$p2";    $t->putTreeBits(0,    r15);

      PrintOutRegisterInHex zmm 0, 1+$i;

      Mov r15, 0b10;
      $t->transferTreeBitsFromLeft (r15, 0, 1, 2) unless $i;
      $t->transferTreeBitsFromRight(r15, 0, 1, 2) if     $i;
      PrintOutRegisterInHex zmm 0..2;

      my $zzz = $i ? "zmm2" : "zmm1";
      push @expected, <<END;
    zmm0: 0000 0000 0565 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    $zzz: 0000 0000 36F7 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm0: 0000 0000 $epe 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm1: 0000 0000 $ele 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
    zmm2: 0000 0000 $ere 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  END
     }

    ok Assemble(debug => 0, eq => join "", @expected);


=head2 Nasm::X86::Tree::splitFullRoot($t)

Split a full root block held in 31..29 and place the left block in 28..26 and the right block in 25..23. The left and right blocks should have their loop offsets set so they can be inserted into the root.

     Parameter  Description
  1  $t         Tree descriptor

=head2 Nasm::X86::Tree::splitFullLeftOrRightNode($t, $right)

Split a full a full left node (held in 28..26) or a full right node (held in 25..23) whose parent is in 31..29.

     Parameter  Description
  1  $t         Tree descriptor
  2  $right     0 left or 1 right

=head2 Nasm::X86::Tree::splitFullLeftNode($t)

Split a full left node block held in 28..26 whose parent is in 31..29 and place the new right block in 25..23. The parent is assumed to be not full. The loop and length fields are assumed to be authoritative and hence are preserved.

     Parameter  Description
  1  $t         Tree descriptor

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

    my $b = CreateArena;
    my $t = $b->CreateTree;

    Vmovdqu8 zmm31, "[$Sk]";
    Vmovdqu8 zmm30, "[$Sd]";
    Vmovdqu8 zmm29, "[$Sn]";

    Vmovdqu8 zmm28, "[$sk]";
    Vmovdqu8 zmm27, "[$sd]";
    Vmovdqu8 zmm26, "[$sn]";

    Vmovdqu8 zmm25, "[$rk]";
    Vmovdqu8 zmm24, "[$rd]";
    Vmovdqu8 zmm23, "[$rn]";

     $t->splitFullLeftNode;

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


=head2 Nasm::X86::Tree::splitFullRightNode($t)

Split a full right node block held in 25..23 whose parent is in 31..29 and place the new left block in 28..26.  The loop and length fields are assumed to be authoritative and hence are preserved.

     Parameter  Description
  1  $t         Tree descriptor

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

    my $b = CreateArena;
    my $t = $b->CreateTree;

    Vmovdqu8 zmm31, "[$tk]";
    Vmovdqu8 zmm30, "[$td]";
    Vmovdqu8 zmm29, "[$tn]";

    Vmovdqu8 zmm28, "[$lk]";
    Vmovdqu8 zmm27, "[$ld]";
    Vmovdqu8 zmm26, "[$ln]";

    Vmovdqu8 zmm25, "[$rk]";
    Vmovdqu8 zmm24, "[$rd]";
    Vmovdqu8 zmm23, "[$rn]";

    $t->splitFullRightNode;

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


=head2 Nasm::X86::Tree::findAndSplit($t, @variables)

Find a key in a tree which is known to contain at least one key splitting full nodes along the path to the key.

     Parameter   Description
  1  $t          Tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::Tree::getKeysData($t, $offset, $zmmKeys, $zmmData)

Load the keys and data blocks for a node

     Parameter  Description
  1  $t         Tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys

=head2 Nasm::X86::Tree::putKeysData($t, $offset, $zmmKeys, $zmmData)

Save the key and data blocks for a node

     Parameter  Description
  1  $t         Tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys

=head2 Nasm::X86::Tree::getNode($t, $offset, $zmmNode)

Load the child nodes for a node

     Parameter  Description
  1  $t         Tree descriptor
  2  $offset    Offset of nodes
  3  $zmmNode   Numbered zmm for keys

=head2 Nasm::X86::Tree::getKeysDataNode($t, $offset, $zmmKeys, $zmmData, $zmmNode)

Load the keys, data and child nodes for a node

     Parameter  Description
  1  $t         Tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys
  5  $zmmNode   Numbered numbered for keys

=head2 Nasm::X86::Tree::putKeysDataNode($t, $offset, $zmmKeys, $zmmData, $zmmNode)

Save the keys, data and child nodes for a node

     Parameter  Description
  1  $t         Tree descriptor
  2  $offset    Offset as a variable
  3  $zmmKeys   Numbered zmm for keys
  4  $zmmData   Numbered data for keys
  5  $zmmNode   Numbered numbered for keys

=head2 Nasm::X86::Tree::getLengthInKeys($t, $zmm)

Get the length of the keys block in the numbered zmm and return it as a variable

     Parameter  Description
  1  $t         Tree descriptor
  2  $zmm       Zmm number

=head2 Nasm::X86::Tree::putLengthInKeys($t, $zmm, $length)

Get the length of the block in the numbered zmm from the specified variable

     Parameter  Description
  1  $t         Tree
  2  $zmm       Zmm number
  3  $length    Length variable

=head2 Nasm::X86::Tree::getUpFromData($t, $zmm)

Get the up offset from the data block in the numbered zmm and return it as a variable

     Parameter  Description
  1  $t         Tree descriptor
  2  $zmm       Zmm number

=head2 Nasm::X86::Tree::putUpIntoData($t, $offset, $zmm)

Put the offset of the parent keys block expressed as a variable into the numbered zmm

     Parameter  Description
  1  $t         Tree descriptor
  2  $offset    Variable containing up offset
  3  $zmm       Zmm number

=head2 Nasm::X86::Tree::getLoop($t, $zmm, $transfer)

Return the value of the loop field as a variable

     Parameter  Description
  1  $t         Tree descriptor
  2  $zmm       Numbered zmm
  3  $transfer  Optional transfer register

=head2 Nasm::X86::Tree::putLoop($t, $value, $zmm)

Set the value of the loop field from a variable

     Parameter  Description
  1  $t         Tree descriptor
  2  $value     Variable containing offset of next loop entry
  3  $zmm       Numbered zmm

=head2 Nasm::X86::Tree::nodeFromData($t, $data, $node)

Load the the node block into the numbered zmm corresponding to the data block held in the numbered zmm.

     Parameter  Description
  1  $t         Tree descriptor
  2  $data      Numbered zmm containing data
  3  $node      Numbered zmm to hold node block

=head2 Nasm::X86::Tree::address($t)

Address of the arena containing a tree

     Parameter  Description
  1  $t         Tree descriptor

=head2 Nasm::X86::Tree::allocBlock($t, @variables)

Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

     Parameter   Description
  1  $t          Tree descriptor
  2  @variables  Variables

=head2 Nasm::X86::Tree::isTree($t, $register, $zmm)

Set the Zero Flag to oppose the tree bit in the numbered zmm register holding the keys of a node to indicate whether the data element indicated by the specified register is an offset to a sub tree in the containing arena or not.

     Parameter  Description
  1  $t         Tree descriptor
  2  $register  Word register holding a bit shifted into the position to test
  3  $zmm       Numbered zmm register holding the keys for a node in the tree

=head2 Nasm::X86::Tree::setOrClearTree($t, $set, $register, $zmm)

Set or clear the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indicated by the specified register is an offset to a sub tree in the containing arena.

     Parameter  Description
  1  $t         Tree descriptor
  2  $set       Set if true else clear
  3  $register  Register holding a single one in the lowest 14 bits at the insertion point
  4  $zmm       Numbered zmm register holding the keys for a node in the tree

=head2 Nasm::X86::Tree::setTree($t, $register, $zmm)

Set the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing arena.

     Parameter  Description
  1  $t         Tree descriptor
  2  $register  Register holding data element index 0..13
  3  $zmm       Numbered zmm register holding the keys for a node in the tree

=head2 Nasm::X86::Tree::clearTree($t, $register, $zmm)

Clear the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing arena.

     Parameter  Description
  1  $t         Tree descriptor
  2  $register  Register holding data element index 0..13
  3  $zmm       Numbered zmm register holding the keys for a node in the tree

=head2 Nasm::X86::Tree::getTreeBits($t, $zmm, $register)

Load the tree bits from the numbered zmm into the specified register.

     Parameter  Description
  1  $t         Tree descriptor
  2  $zmm       Numbered zmm
  3  $register  Target register

=head2 Nasm::X86::Tree::putTreeBits($t, $zmm, $register)

Put the tree bits in the specified register into the numbered zmm.

     Parameter  Description
  1  $t         Tree descriptor
  2  $zmm       Numbered zmm
  3  $register  Target register

=head2 Nasm::X86::Tree::expandTreeBitsWithZeroOrOne($t, $onz, $zmm, $point)

Insert a zero or one into the tree bits field in the numbered zmm at the specified point

     Parameter  Description
  1  $t         Tree descriptor
  2  $onz       0 - zero or 1 - one
  3  $zmm       Numbered zmm
  4  $point     Register indicating point

=head2 Nasm::X86::Tree::expandTreeBitsWithZero($t, $zmm, $point)

Insert a zero into the tree bits field in the numbered zmm at the specified point

     Parameter  Description
  1  $t         Tree descriptor
  2  $zmm       Numbered zmm
  3  $point     Register indicating point

=head2 Nasm::X86::Tree::expandTreeBitsWithOne($t, $zmm, $point)

Insert a one into the tree bits field in the numbered zmm at the specified point

     Parameter  Description
  1  $t         Tree descriptor
  2  $zmm       Numbered zmm
  3  $point     Register indicating point

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

4 L<Assemble|/Assemble> - Assemble the generated code.

5 L<Block|/Block> - Execute a block of code one with the option of jumping out of the block or restarting the block via the supplied labels.

6 L<CallC|/CallC> - Call a C subroutine

7 L<ChooseRegisters|/ChooseRegisters> - Choose the specified numbers of registers excluding those on the specified list

8 L<ClassifyInRange|/ClassifyInRange> - Character classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with each word in zmm1 having the classification in the highest 8 bits and with zmm0 and zmm1 having the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.

9 L<ClassifyRange|/ClassifyRange> - Implementation of ClassifyInRange and ClassifyWithinRange

10 L<ClassifyWithInRange|/ClassifyWithInRange> - Bracket classification: Classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification range in the highest 8 bits of zmm0 and zmm1 and the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 21 bits.

11 L<ClassifyWithInRangeAndSaveOffset|/ClassifyWithInRangeAndSaveOffset> - Alphabetic classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification code in the high byte of zmm1 and the offset of the first element in the range in the high byte of zmm0.

12 L<ClearMemory|/ClearMemory> - Clear memory - the address of the memory is in rax, the length in rdi

13 L<ClearRegisters|/ClearRegisters> - Clear registers by setting them to zero

14 L<ClearZF|/ClearZF> - Clear the zero flag

15 L<CloseFile|/CloseFile> - Close the file whose descriptor is in rax

16 L<Comment|/Comment> - Insert a comment into the assembly code

17 L<CommentWithTraceBack|/CommentWithTraceBack> - Insert a comment into the assembly code with a traceback showing how it was generated

18 L<ConcatenateShortStrings|/ConcatenateShortStrings> - Concatenate the numbered source zmm containing a short string with the short string in the numbered target zmm.

19 L<ConvertUtf8ToUtf32|/ConvertUtf8ToUtf32> - Convert a string of utf8 to an allocated block of utf32 and return its address and length.

20 L<CopyMemory|/CopyMemory> - Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi

21 L<cr|/cr> - Call a subroutine with a reordering of the registers.

22 L<CreateArena|/CreateArena> - Create an relocatable arena and returns its address in rax.

23 L<Cstrlen|/Cstrlen> - Length of the C style string addressed by rax returning the length in r15

24 L<Db|/Db> - Layout bytes in the data segment and return their label

25 L<Dbwdq|/Dbwdq> - Layout data

26 L<DComment|/DComment> - Insert a comment into the data segment

27 L<Dd|/Dd> - Layout double words in the data segment and return their label

28 L<Dq|/Dq> - Layout quad words in the data segment and return their label

29 L<Ds|/Ds> - Layout bytes in memory and return their label

30 L<Dw|/Dw> - Layout words in the data segment and return their label

31 L<Else|/Else> - Else body for an If statement

32 L<executeFileViaBash|/executeFileViaBash> - Execute the file named in the arena addressed by rax with bash

33 L<Exit|/Exit> - Exit with the specified return code or zero if no return code supplied.

34 L<Extern|/Extern> - Name external references

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

58 L<IfC|/IfC> - If the carry flag is set then execute the then body else the else body

59 L<IfEq|/IfEq> - If equal execute the then body else the else body

60 L<IfGe|/IfGe> - If greater than or equal execute the then body else the else body

61 L<IfGt|/IfGt> - If greater than execute the then body else the else body

62 L<IfLe|/IfLe> - If less than or equal execute the then body else the else body

63 L<IfLt|/IfLt> - If less than execute the then body else the else body

64 L<IfNc|/IfNc> - If the carry flag is not set then execute the then body else the else body

65 L<IfNe|/IfNe> - If not equal execute the then body else the else body

66 L<IfNz|/IfNz> - If the zero flag is not set then execute the then body else the else body

67 L<IfZ|/IfZ> - If the zero flag is set then execute the then body else the else body

68 L<InsertOneIntoRegisterAtPoint|/InsertOneIntoRegisterAtPoint> - Insert a one into the specified register at the point indicated by another register

69 L<InsertZeroIntoRegisterAtPoint|/InsertZeroIntoRegisterAtPoint> - Insert a zero into the specified register at the point indicated by another register

70 L<K|/K> - Define a quad constant

71 L<Keep|/Keep> - Mark registers as in use so that they cannot be updated  until we explicitly free them.

72 L<KeepFree|/KeepFree> - Free registers so that they can be reused

73 L<KeepPop|/KeepPop> - Reset the status of the specified registers to the status quo ante the last push

74 L<KeepPush|/KeepPush> - Push the current status of the specified registers and then mark them as free

75 L<KeepReturn|/KeepReturn> - Pop the specified register and mark it as in use to effect a subroutine return with this register.

76 L<KeepSet|/KeepSet> - Confirm that the specified registers are in use

77 L<Label|/Label> - Create a unique label

78 L<Link|/Link> - Libraries to link with

79 L<LoadBitsIntoMaskRegister|/LoadBitsIntoMaskRegister> - Load a bit string specification into a mask register

80 L<LoadConstantIntoMaskRegister|/LoadConstantIntoMaskRegister> - Set a mask register equal to a constant.

81 L<loadFromZmm|/loadFromZmm> - Load the specified register from the offset located in the numbered zmm.

82 L<LoadShortStringFromMemoryToZmm|/LoadShortStringFromMemoryToZmm> - Load the short string addressed by rax into the zmm register with the specified number

83 L<LoadZmm|/LoadZmm> - Load a numbered zmm with the specified bytes

84 L<LocalData|/LocalData> - Map local data

85 L<LocateIntelEmulator|/LocateIntelEmulator> - Locate the Intel Software Development Emulator

86 L<Macro|/Macro> - Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub

87 L<MaskMemory22|/MaskMemory22> - Write the specified byte into locations in the target mask that correspond to the locations in the source that contain the specified byte.

88 L<MaskMemoryInRange4_22|/MaskMemoryInRange4_22> - Write the specified byte into locations in the target mask that correspond to the locations in the source that contain 4 bytes in the specified range.

89 L<Nasm::X86::Arena::allocate|/Nasm::X86::Arena::allocate> - Allocate the amount of space indicated in rdi in the arena addressed by rax and return the offset of the allocation in the arena in rdi

90 L<Nasm::X86::Arena::allocBlock|/Nasm::X86::Arena::allocBlock> - Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

91 L<Nasm::X86::Arena::allocZmmBlock|/Nasm::X86::Arena::allocZmmBlock> - Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

92 L<Nasm::X86::Arena::append|/Nasm::X86::Arena::append> - Append one arena to another

93 L<Nasm::X86::Arena::blockSize|/Nasm::X86::Arena::blockSize> - Size of a block

94 L<Nasm::X86::Arena::chain|/Nasm::X86::Arena::chain> - Return a variable with the end point of a chain of double words in the arena starting at the specified variable.

95 L<Nasm::X86::Arena::char|/Nasm::X86::Arena::char> - Append a character expressed as a decimal number to the arena addressed by rax

96 L<Nasm::X86::Arena::clear|/Nasm::X86::Arena::clear> - Clear the arena addressed by rax

97 L<Nasm::X86::Arena::CreateArray|/Nasm::X86::Arena::CreateArray> - Create a array in an arena

98 L<Nasm::X86::Arena::CreateString|/Nasm::X86::Arena::CreateString> - Create a string from a doubly link linked list of 64 byte blocks linked via 4 byte offsets in the arena addressed by rax and return its descriptor

99 L<Nasm::X86::Arena::CreateTree|/Nasm::X86::Arena::CreateTree> - Create a tree in an arena.

100 L<Nasm::X86::Arena::DescribeTree|/Nasm::X86::Arena::DescribeTree> - Return a descriptor for a tree in the specified arena

101 L<Nasm::X86::Arena::dump|/Nasm::X86::Arena::dump> - Dump details of an arena

102 L<Nasm::X86::Arena::firstFreeBlock|/Nasm::X86::Arena::firstFreeBlock> - Create and load a variable with the first free block on the free block chain or zero if no such block in the given arena

103 L<Nasm::X86::Arena::freeBlock|/Nasm::X86::Arena::freeBlock> - Free a block in an arena by placing it on the free chain

104 L<Nasm::X86::Arena::getBlock|/Nasm::X86::Arena::getBlock> - Get the block with the specified offset in the specified string and return it in the numbered zmm

105 L<Nasm::X86::Arena::length|/Nasm::X86::Arena::length> - Get the length of an arena

106 L<Nasm::X86::Arena::m|/Nasm::X86::Arena::m> - Append the content with length rdi addressed by rsi to the arena addressed by rax

107 L<Nasm::X86::Arena::makeReadOnly|/Nasm::X86::Arena::makeReadOnly> - Make an arena read only

108 L<Nasm::X86::Arena::makeWriteable|/Nasm::X86::Arena::makeWriteable> - Make an arena writable

109 L<Nasm::X86::Arena::nl|/Nasm::X86::Arena::nl> - Append a new line to the arena addressed by rax

110 L<Nasm::X86::Arena::out|/Nasm::X86::Arena::out> - Print the specified arena addressed by rax on sysout

111 L<Nasm::X86::Arena::putBlock|/Nasm::X86::Arena::putBlock> - Write the numbered zmm to the block at the specified offset in the specified arena

112 L<Nasm::X86::Arena::putChain|/Nasm::X86::Arena::putChain> - Write the double word in the specified variable to the double word location at the the specified offset in the specified arena.

113 L<Nasm::X86::Arena::q|/Nasm::X86::Arena::q> - Append a constant string to the arena

114 L<Nasm::X86::Arena::ql|/Nasm::X86::Arena::ql> - Append a quoted string containing new line characters to the arena addressed by rax

115 L<Nasm::X86::Arena::read|/Nasm::X86::Arena::read> - Read the named file (terminated with a zero byte) and place it into the named arena.

116 L<Nasm::X86::Arena::setFirstFreeBlock|/Nasm::X86::Arena::setFirstFreeBlock> - Set the first free block field from a variable

117 L<Nasm::X86::Arena::updateSpace|/Nasm::X86::Arena::updateSpace> - Make sure that the arena addressed by rax has enough space to accommodate content of length rdi

118 L<Nasm::X86::Arena::write|/Nasm::X86::Arena::write> - Write the content in an arena addressed by rax to a temporary file and replace the arena content with the name of the  temporary file

119 L<Nasm::X86::Arena::z|/Nasm::X86::Arena::z> - Append a trailing zero to the arena addressed by rax

120 L<Nasm::X86::Array::address|/Nasm::X86::Array::address> - Address of a string

121 L<Nasm::X86::Array::allocBlock|/Nasm::X86::Array::allocBlock> - Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

122 L<Nasm::X86::Array::dump|/Nasm::X86::Array::dump> - Dump a array

123 L<Nasm::X86::Array::get|/Nasm::X86::Array::get> - Get an element from the array

124 L<Nasm::X86::Array::pop|/Nasm::X86::Array::pop> - Pop an element from an array

125 L<Nasm::X86::Array::push|/Nasm::X86::Array::push> - Push an element onto the array

126 L<Nasm::X86::Array::put|/Nasm::X86::Array::put> - Put an element into an array as long as it is with in its limits established by pushing.

127 L<Nasm::X86::LocalData::allocate8|/Nasm::X86::LocalData::allocate8> - Add some 8 byte local variables and return an array of variable definitions

128 L<Nasm::X86::LocalData::free|/Nasm::X86::LocalData::free> - Free a local data area on the stack

129 L<Nasm::X86::LocalData::start|/Nasm::X86::LocalData::start> - Start a local data area on the stack

130 L<Nasm::X86::LocalData::variable|/Nasm::X86::LocalData::variable> - Add a local variable

131 L<Nasm::X86::LocalVariable::stack|/Nasm::X86::LocalVariable::stack> - Address a local variable on the stack

132 L<Nasm::X86::String::address|/Nasm::X86::String::address> - Address of a string

133 L<Nasm::X86::String::allocBlock|/Nasm::X86::String::allocBlock> - Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

134 L<Nasm::X86::String::append|/Nasm::X86::String::append> - Append the specified content in memory to the specified string

135 L<Nasm::X86::String::clear|/Nasm::X86::String::clear> - Clear the block by freeing all but the first block

136 L<Nasm::X86::String::concatenate|/Nasm::X86::String::concatenate> - Concatenate two strings by appending a copy of the source to the target string.

137 L<Nasm::X86::String::deleteChar|/Nasm::X86::String::deleteChar> - Delete a character in a string

138 L<Nasm::X86::String::dump|/Nasm::X86::String::dump> - Dump a string to sysout

139 L<Nasm::X86::String::getBlock|/Nasm::X86::String::getBlock> - Get the block with the specified offset in the specified string and return it in the numbered zmm

140 L<Nasm::X86::String::getBlockLength|/Nasm::X86::String::getBlockLength> - Get the block length of the numbered zmm and return it in a variable

141 L<Nasm::X86::String::getCharacter|/Nasm::X86::String::getCharacter> - Get a character from a string

142 L<Nasm::X86::String::getNextAndPrevBlockOffsetFromZmm|/Nasm::X86::String::getNextAndPrevBlockOffsetFromZmm> - Get the offsets of the next and previous blocks as variables from the specified zmm

143 L<Nasm::X86::String::insertChar|/Nasm::X86::String::insertChar> - Insert a character into a string

144 L<Nasm::X86::String::len|/Nasm::X86::String::len> - Find the length of a string

145 L<Nasm::X86::String::putBlock|/Nasm::X86::String::putBlock> - Write the numbered zmm to the block at the specified offset in the specified arena

146 L<Nasm::X86::String::putNextandPrevBlockOffsetIntoZmm|/Nasm::X86::String::putNextandPrevBlockOffsetIntoZmm> - Save next and prev offsets into a zmm representing a block

147 L<Nasm::X86::String::setBlockLengthInZmm|/Nasm::X86::String::setBlockLengthInZmm> - Set the block length of the numbered zmm to the specified length

148 L<Nasm::X86::Structure::field|/Nasm::X86::Structure::field> - Add a field of the specified length with an optional comment

149 L<Nasm::X86::StructureField::addr|/Nasm::X86::StructureField::addr> - Address a field in a structure by either the default register or the named register

150 L<Nasm::X86::Sub::call|/Nasm::X86::Sub::call> - Call a sub passing it some parameters

151 L<Nasm::X86::Tree::address|/Nasm::X86::Tree::address> - Address of the arena containing a tree

152 L<Nasm::X86::Tree::allocBlock|/Nasm::X86::Tree::allocBlock> - Allocate a block to hold a zmm register in the specified arena and return the offset of the block in a variable

153 L<Nasm::X86::Tree::allocKeysDataNode|/Nasm::X86::Tree::allocKeysDataNode> - Allocate a keys/data/node block and place it in the numbered zmm registers

154 L<Nasm::X86::Tree::by|/Nasm::X86::Tree::by> - Call the specified body with each (key, data) from the specified tree in order

155 L<Nasm::X86::Tree::clearTree|/Nasm::X86::Tree::clearTree> - Clear the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing arena.

156 L<Nasm::X86::Tree::Clone|/Nasm::X86::Tree::Clone> - Clone the specified tree descriptions

157 L<Nasm::X86::Tree::depth|/Nasm::X86::Tree::depth> - Return the depth of a node within a tree.

158 L<Nasm::X86::Tree::expandTreeBitsWithOne|/Nasm::X86::Tree::expandTreeBitsWithOne> - Insert a one into the tree bits field in the numbered zmm at the specified point

159 L<Nasm::X86::Tree::expandTreeBitsWithZero|/Nasm::X86::Tree::expandTreeBitsWithZero> - Insert a zero into the tree bits field in the numbered zmm at the specified point

160 L<Nasm::X86::Tree::expandTreeBitsWithZeroOrOne|/Nasm::X86::Tree::expandTreeBitsWithZeroOrOne> - Insert a zero or one into the tree bits field in the numbered zmm at the specified point

161 L<Nasm::X86::Tree::find|/Nasm::X86::Tree::find> - Find a key in a tree and test whether the found data is a sub tree.

162 L<Nasm::X86::Tree::findAndClone|/Nasm::X86::Tree::findAndClone> - Find a key in the specified tree and clone it is it is a sub tree.

163 L<Nasm::X86::Tree::findAndSplit|/Nasm::X86::Tree::findAndSplit> - Find a key in a tree which is known to contain at least one key splitting full nodes along the path to the key.

164 L<Nasm::X86::Tree::getKeysData|/Nasm::X86::Tree::getKeysData> - Load the keys and data blocks for a node

165 L<Nasm::X86::Tree::getKeysDataNode|/Nasm::X86::Tree::getKeysDataNode> - Load the keys, data and child nodes for a node

166 L<Nasm::X86::Tree::getLengthInKeys|/Nasm::X86::Tree::getLengthInKeys> - Get the length of the keys block in the numbered zmm and return it as a variable

167 L<Nasm::X86::Tree::getLoop|/Nasm::X86::Tree::getLoop> - Return the value of the loop field as a variable

168 L<Nasm::X86::Tree::getNode|/Nasm::X86::Tree::getNode> - Load the child nodes for a node

169 L<Nasm::X86::Tree::getTreeBits|/Nasm::X86::Tree::getTreeBits> - Load the tree bits from the numbered zmm into the specified register.

170 L<Nasm::X86::Tree::getUpFromData|/Nasm::X86::Tree::getUpFromData> - Get the up offset from the data block in the numbered zmm and return it as a variable

171 L<Nasm::X86::Tree::insert|/Nasm::X86::Tree::insert> - Insert a dword into into the specified tree at the specified key.

172 L<Nasm::X86::Tree::insertDataOrTree|/Nasm::X86::Tree::insertDataOrTree> - Insert either a key, data pair into the tree or create a sub tree at the specified key (if it does not already exist) and return the offset of the first block of the sub tree in the data variable.

173 L<Nasm::X86::Tree::insertTree|/Nasm::X86::Tree::insertTree> - Insert a sub tree into the specified tree tree under the specified key.

174 L<Nasm::X86::Tree::insertTreeAndClone|/Nasm::X86::Tree::insertTreeAndClone> - Insert a new sub tree into the specified tree tree under the specified key and return a descriptor for it.

175 L<Nasm::X86::Tree::isTree|/Nasm::X86::Tree::isTree> - Set the Zero Flag to oppose the tree bit in the numbered zmm register holding the keys of a node to indicate whether the data element indicated by the specified register is an offset to a sub tree in the containing arena or not.

176 L<Nasm::X86::Tree::iterator|/Nasm::X86::Tree::iterator> - Iterate through a multi way tree

177 L<Nasm::X86::Tree::Iterator::next|/Nasm::X86::Tree::Iterator::next> - Next element in the tree

178 L<Nasm::X86::Tree::leftMost|/Nasm::X86::Tree::leftMost> - Return the left most node

179 L<Nasm::X86::Tree::leftOrRightMost|/Nasm::X86::Tree::leftOrRightMost> - Return the left most or right most node

180 L<Nasm::X86::Tree::nodeFromData|/Nasm::X86::Tree::nodeFromData> - Load the the node block into the numbered zmm corresponding to the data block held in the numbered zmm.

181 L<Nasm::X86::Tree::print|/Nasm::X86::Tree::print> - Print a tree

182 L<Nasm::X86::Tree::putKeysData|/Nasm::X86::Tree::putKeysData> - Save the key and data blocks for a node

183 L<Nasm::X86::Tree::putKeysDataNode|/Nasm::X86::Tree::putKeysDataNode> - Save the keys, data and child nodes for a node

184 L<Nasm::X86::Tree::putLengthInKeys|/Nasm::X86::Tree::putLengthInKeys> - Get the length of the block in the numbered zmm from the specified variable

185 L<Nasm::X86::Tree::putLoop|/Nasm::X86::Tree::putLoop> - Set the value of the loop field from a variable

186 L<Nasm::X86::Tree::putTreeBits|/Nasm::X86::Tree::putTreeBits> - Put the tree bits in the specified register into the numbered zmm.

187 L<Nasm::X86::Tree::putUpIntoData|/Nasm::X86::Tree::putUpIntoData> - Put the offset of the parent keys block expressed as a variable into the numbered zmm

188 L<Nasm::X86::Tree::reParent|/Nasm::X86::Tree::reParent> - Reparent the children of a node held in registers.

189 L<Nasm::X86::Tree::rightMost|/Nasm::X86::Tree::rightMost> - Return the right most node

190 L<Nasm::X86::Tree::setOrClearTree|/Nasm::X86::Tree::setOrClearTree> - Set or clear the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indicated by the specified register is an offset to a sub tree in the containing arena.

191 L<Nasm::X86::Tree::setTree|/Nasm::X86::Tree::setTree> - Set the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing arena.

192 L<Nasm::X86::Tree::splitFullLeftNode|/Nasm::X86::Tree::splitFullLeftNode> - Split a full left node block held in 28.

193 L<Nasm::X86::Tree::splitFullLeftOrRightNode|/Nasm::X86::Tree::splitFullLeftOrRightNode> - Split a full a full left node (held in 28.

194 L<Nasm::X86::Tree::splitFullRightNode|/Nasm::X86::Tree::splitFullRightNode> - Split a full right node block held in 25.

195 L<Nasm::X86::Tree::splitFullRoot|/Nasm::X86::Tree::splitFullRoot> - Split a full root block held in 31.

196 L<Nasm::X86::Tree::splitNode|/Nasm::X86::Tree::splitNode> - Split a node given its offset in an arena retaining the key being inserted in the node split while putting the remainder to the left or right.

197 L<Nasm::X86::Tree::transferTreeBitsFromLeft|/Nasm::X86::Tree::transferTreeBitsFromLeft> - Transfer tree bits when splitting a full left node

198 L<Nasm::X86::Tree::transferTreeBitsFromLeftOrRight|/Nasm::X86::Tree::transferTreeBitsFromLeftOrRight> - Transfer tree bits when splitting a full left or right node.

199 L<Nasm::X86::Tree::transferTreeBitsFromParent|/Nasm::X86::Tree::transferTreeBitsFromParent> - Transfer tree bits when splitting a full node.

200 L<Nasm::X86::Tree::transferTreeBitsFromRight|/Nasm::X86::Tree::transferTreeBitsFromRight> - Transfer tree bits when splitting a full right node

201 L<Nasm::X86::Variable::add|/Nasm::X86::Variable::add> - Add the right hand variable to the left hand variable and return the result as a new variable

202 L<Nasm::X86::Variable::address|/Nasm::X86::Variable::address> - Get the address of a variable with an optional offset

203 L<Nasm::X86::Variable::allocateMemory|/Nasm::X86::Variable::allocateMemory> - Allocate the specified amount of memory via mmap and return its address

204 L<Nasm::X86::Variable::and|/Nasm::X86::Variable::and> - And two variables

205 L<Nasm::X86::Variable::arithmetic|/Nasm::X86::Variable::arithmetic> - Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables

206 L<Nasm::X86::Variable::assign|/Nasm::X86::Variable::assign> - Assign to the left hand side the value of the right hand side

207 L<Nasm::X86::Variable::boolean|/Nasm::X86::Variable::boolean> - Combine the left hand variable with the right hand variable via a boolean operator

208 L<Nasm::X86::Variable::booleanC|/Nasm::X86::Variable::booleanC> - Combine the left hand variable with the right hand variable via a boolean operator using a conditional move instruction.

209 L<Nasm::X86::Variable::clearBit|/Nasm::X86::Variable::clearBit> - Clear a bit in the specified mask register retaining the other bits

210 L<Nasm::X86::Variable::clearMaskBit|/Nasm::X86::Variable::clearMaskBit> - Clear a bit in the specified mask register retaining the other bits

211 L<Nasm::X86::Variable::clearMemory|/Nasm::X86::Variable::clearMemory> - Clear the memory described in this variable

212 L<Nasm::X86::Variable::clone|/Nasm::X86::Variable::clone> - Clone a variable to create a new variable

213 L<Nasm::X86::Variable::copy|/Nasm::X86::Variable::copy> - Copy one variable into another

214 L<Nasm::X86::Variable::copyAddress|/Nasm::X86::Variable::copyAddress> - Copy a reference to a variable

215 L<Nasm::X86::Variable::copyMemory|/Nasm::X86::Variable::copyMemory> - Copy from one block of memory to another

216 L<Nasm::X86::Variable::copyZF|/Nasm::X86::Variable::copyZF> - Copy the current state of the zero flag into a variable

217 L<Nasm::X86::Variable::copyZFInverted|/Nasm::X86::Variable::copyZFInverted> - Copy the opposite of the current state of the zero flag into a variable

218 L<Nasm::X86::Variable::debug|/Nasm::X86::Variable::debug> - Dump the value of a variable on stdout with an indication of where the dump came from

219 L<Nasm::X86::Variable::dec|/Nasm::X86::Variable::dec> - Decrement a variable

220 L<Nasm::X86::Variable::divide|/Nasm::X86::Variable::divide> - Divide the left hand variable by the right hand variable and return the result as a new variable

221 L<Nasm::X86::Variable::division|/Nasm::X86::Variable::division> - Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side

222 L<Nasm::X86::Variable::dump|/Nasm::X86::Variable::dump> - Dump the value of a variable to the specified channel adding an optional title and new line if requested

223 L<Nasm::X86::Variable::eq|/Nasm::X86::Variable::eq> - Check whether the left hand variable is equal to the right hand variable

224 L<Nasm::X86::Variable::equals|/Nasm::X86::Variable::equals> - Equals operator

225 L<Nasm::X86::Variable::err|/Nasm::X86::Variable::err> - Dump the value of a variable on stderr

226 L<Nasm::X86::Variable::errNL|/Nasm::X86::Variable::errNL> - Dump the value of a variable on stderr and append a new line

227 L<Nasm::X86::Variable::for|/Nasm::X86::Variable::for> - Iterate the body limit times.

228 L<Nasm::X86::Variable::freeMemory|/Nasm::X86::Variable::freeMemory> - Free the memory addressed by this variable for the specified length

229 L<Nasm::X86::Variable::ge|/Nasm::X86::Variable::ge> - Check whether the left hand variable is greater than or equal to the right hand variable

230 L<Nasm::X86::Variable::getBFromZmm|/Nasm::X86::Variable::getBFromZmm> - Get the byte from the numbered zmm register and put it in a variable

231 L<Nasm::X86::Variable::getConst|/Nasm::X86::Variable::getConst> - Load the variable from a constant in effect setting a variable to a specified value

232 L<Nasm::X86::Variable::getDFromZmm|/Nasm::X86::Variable::getDFromZmm> - Get the double word from the numbered zmm register and put it in a variable

233 L<Nasm::X86::Variable::getQFromZmm|/Nasm::X86::Variable::getQFromZmm> - Get the quad word from the numbered zmm register and put it in a variable

234 L<Nasm::X86::Variable::getReg|/Nasm::X86::Variable::getReg> - Load the variable from the named registers

235 L<Nasm::X86::Variable::getWFromZmm|/Nasm::X86::Variable::getWFromZmm> - Get the word from the numbered zmm register and put it in a variable

236 L<Nasm::X86::Variable::gt|/Nasm::X86::Variable::gt> - Check whether the left hand variable is greater than the right hand variable

237 L<Nasm::X86::Variable::inc|/Nasm::X86::Variable::inc> - Increment a variable

238 L<Nasm::X86::Variable::incDec|/Nasm::X86::Variable::incDec> - Increment or decrement a variable

239 L<Nasm::X86::Variable::isRef|/Nasm::X86::Variable::isRef> - Check whether the specified  variable is a reference to another variable

240 L<Nasm::X86::Variable::le|/Nasm::X86::Variable::le> - Check whether the left hand variable is less than or equal to the right hand variable

241 L<Nasm::X86::Variable::loadZmm|/Nasm::X86::Variable::loadZmm> - Load bytes from the memory addressed by the specified source variable into the numbered zmm register.

242 L<Nasm::X86::Variable::lt|/Nasm::X86::Variable::lt> - Check whether the left hand variable is less than the right hand variable

243 L<Nasm::X86::Variable::max|/Nasm::X86::Variable::max> - Maximum of two variables

244 L<Nasm::X86::Variable::min|/Nasm::X86::Variable::min> - Minimum of two variables

245 L<Nasm::X86::Variable::minusAssign|/Nasm::X86::Variable::minusAssign> - Implement minus and assign

246 L<Nasm::X86::Variable::mod|/Nasm::X86::Variable::mod> - Divide the left hand variable by the right hand variable and return the remainder as a new variable

247 L<Nasm::X86::Variable::ne|/Nasm::X86::Variable::ne> - Check whether the left hand variable is not equal to the right hand variable

248 L<Nasm::X86::Variable::or|/Nasm::X86::Variable::or> - Or two variables

249 L<Nasm::X86::Variable::out|/Nasm::X86::Variable::out> - Dump the value of a variable on stdout

250 L<Nasm::X86::Variable::outNL|/Nasm::X86::Variable::outNL> - Dump the value of a variable on stdout and append a new line

251 L<Nasm::X86::Variable::plusAssign|/Nasm::X86::Variable::plusAssign> - Implement plus and assign

252 L<Nasm::X86::Variable::pop|/Nasm::X86::Variable::pop> - Pop a variable from the stack

253 L<Nasm::X86::Variable::printErrMemoryInHexNL|/Nasm::X86::Variable::printErrMemoryInHexNL> - Write the memory addressed by a variable to stderr

254 L<Nasm::X86::Variable::printMemoryInHexNL|/Nasm::X86::Variable::printMemoryInHexNL> - Write the memory addressed by a variable to stdout or stderr

255 L<Nasm::X86::Variable::printOutMemoryInHexNL|/Nasm::X86::Variable::printOutMemoryInHexNL> - Write the memory addressed by a variable to stdout

256 L<Nasm::X86::Variable::push|/Nasm::X86::Variable::push> - Push a variable onto the stack

257 L<Nasm::X86::Variable::putBIntoXmm|/Nasm::X86::Variable::putBIntoXmm> - Place the value of the content variable at the byte in the numbered xmm register

258 L<Nasm::X86::Variable::putBIntoZmm|/Nasm::X86::Variable::putBIntoZmm> - Place the value of the content variable at the byte in the numbered zmm register

259 L<Nasm::X86::Variable::putBwdqIntoMm|/Nasm::X86::Variable::putBwdqIntoMm> - Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register

260 L<Nasm::X86::Variable::putDIntoXmm|/Nasm::X86::Variable::putDIntoXmm> - Place the value of the content variable at the double word in the numbered xmm register

261 L<Nasm::X86::Variable::putDIntoZmm|/Nasm::X86::Variable::putDIntoZmm> - Place the value of the content variable at the double word in the numbered zmm register

262 L<Nasm::X86::Variable::putQIntoXmm|/Nasm::X86::Variable::putQIntoXmm> - Place the value of the content variable at the quad word in the numbered xmm register

263 L<Nasm::X86::Variable::putQIntoZmm|/Nasm::X86::Variable::putQIntoZmm> - Place the value of the content variable at the quad word in the numbered zmm register

264 L<Nasm::X86::Variable::putWIntoXmm|/Nasm::X86::Variable::putWIntoXmm> - Place the value of the content variable at the word in the numbered xmm register

265 L<Nasm::X86::Variable::putWIntoZmm|/Nasm::X86::Variable::putWIntoZmm> - Place the value of the content variable at the word in the numbered zmm register

266 L<Nasm::X86::Variable::setBit|/Nasm::X86::Variable::setBit> - Set a bit in the specified register retaining the other bits

267 L<Nasm::X86::Variable::setMask|/Nasm::X86::Variable::setMask> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

268 L<Nasm::X86::Variable::setMaskBit|/Nasm::X86::Variable::setMaskBit> - Set a bit in the specified mask register retaining the other bits

269 L<Nasm::X86::Variable::setMaskFirst|/Nasm::X86::Variable::setMaskFirst> - Set the first bits in the specified mask register

270 L<Nasm::X86::Variable::setReg|/Nasm::X86::Variable::setReg> - Set the named registers from the content of the variable

271 L<Nasm::X86::Variable::setZmm|/Nasm::X86::Variable::setZmm> - Load bytes from the memory addressed by specified source variable into the numbered zmm register at the offset in the specified offset moving the number of bytes in the specified variable

272 L<Nasm::X86::Variable::str|/Nasm::X86::Variable::str> - The name of the variable

273 L<Nasm::X86::Variable::sub|/Nasm::X86::Variable::sub> - Subtract the right hand variable from the left hand variable and return the result as a new variable

274 L<Nasm::X86::Variable::times|/Nasm::X86::Variable::times> - Multiply the left hand variable by the right hand variable and return the result as a new variable

275 L<Nasm::X86::Variable::zBroadCastD|/Nasm::X86::Variable::zBroadCastD> - Broadcast a double word in a variable into the numbered zmm.

276 L<OpenRead|/OpenRead> - Open a file, whose name is addressed by rax, for read and return the file descriptor in rax

277 L<OpenWrite|/OpenWrite> - Create the file named by the terminated string addressed by rax for write

278 L<PeekR|/PeekR> - Peek at register on stack

279 L<PopEax|/PopEax> - We cannot pop a double word from the stack in 64 bit long mode using pop so we improvise

280 L<PopR|/PopR> - Pop registers from the stack

281 L<PopRR|/PopRR> - Pop registers from the stack without tracking

282 L<PrintErrMemory|/PrintErrMemory> - Print the memory addressed by rax for a length of rdi on stderr

283 L<PrintErrMemoryInHex|/PrintErrMemoryInHex> - Dump memory from the address in rax for the length in rdi on stderr

284 L<PrintErrMemoryInHexNL|/PrintErrMemoryInHexNL> - Dump memory from the address in rax for the length in rdi and then print a new line

285 L<PrintErrMemoryNL|/PrintErrMemoryNL> - Print the memory addressed by rax for a length of rdi followed by a new line on stderr

286 L<PrintErrNL|/PrintErrNL> - Print a new line to stderr

287 L<PrintErrRaxInHex|/PrintErrRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to stderr

288 L<PrintErrRegisterInHex|/PrintErrRegisterInHex> - Print the named registers as hex strings on stderr

289 L<PrintErrString|/PrintErrString> - Print a constant string to stderr.

290 L<PrintErrStringNL|/PrintErrStringNL> - Print a constant string followed by a new line to stderr

291 L<PrintErrZF|/PrintErrZF> - Print the zero flag without disturbing it on stderr

292 L<PrintMemory|/PrintMemory> - Print the memory addressed by rax for a length of rdi on the specified channel

293 L<PrintMemoryInHex|/PrintMemoryInHex> - Dump memory from the address in rax for the length in rdi on the specified channel.

294 L<PrintNL|/PrintNL> - Print a new line to stdout  or stderr

295 L<PrintOutMemory|/PrintOutMemory> - Print the memory addressed by rax for a length of rdi on stdout

296 L<PrintOutMemoryInHex|/PrintOutMemoryInHex> - Dump memory from the address in rax for the length in rdi on stdout

297 L<PrintOutMemoryInHexNL|/PrintOutMemoryInHexNL> - Dump memory from the address in rax for the length in rdi and then print a new line

298 L<PrintOutMemoryNL|/PrintOutMemoryNL> - Print the memory addressed by rax for a length of rdi followed by a new line on stdout

299 L<PrintOutNL|/PrintOutNL> - Print a new line to stderr

300 L<PrintOutRaxInHex|/PrintOutRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to stderr

301 L<PrintOutRaxInReverseInHex|/PrintOutRaxInReverseInHex> - Write the content of register rax to stderr in hexadecimal in little endian notation

302 L<PrintOutRegisterInHex|/PrintOutRegisterInHex> - Print the named registers as hex strings on stdout

303 L<PrintOutRegistersInHex|/PrintOutRegistersInHex> - Print the general purpose registers in hex

304 L<PrintOutRflagsInHex|/PrintOutRflagsInHex> - Print the flags register in hex

305 L<PrintOutRipInHex|/PrintOutRipInHex> - Print the instruction pointer in hex

306 L<PrintOutString|/PrintOutString> - Print a constant string to stdout.

307 L<PrintOutStringNL|/PrintOutStringNL> - Print a constant string followed by a new line to stdout

308 L<PrintOutZF|/PrintOutZF> - Print the zero flag without disturbing it on stdout

309 L<PrintRaxInHex|/PrintRaxInHex> - Write the content of register rax in hexadecimal in big endian notation to the specified channel

310 L<PrintRegisterInHex|/PrintRegisterInHex> - Print the named registers as hex strings

311 L<PrintString|/PrintString> - Print a constant string to the specified channel

312 L<PrintUtf32|/PrintUtf32> - Print the specified number of utf32 characters at the specified address

313 L<PushR|/PushR> - Push registers onto the stack

314 L<PushRR|/PushRR> - Push registers onto the stack without tracking

315 L<putIntoZmm|/putIntoZmm> - Put the specified register into the numbered zmm at the from the offset located in the numbered zmm.

316 L<R|/R> - Define a reference variable

317 L<Rb|/Rb> - Layout bytes in the data segment and return their label

318 L<Rbwdq|/Rbwdq> - Layout data

319 L<RComment|/RComment> - Insert a comment into the read only data segment

320 L<Rd|/Rd> - Layout double words in the data segment and return their label

321 L<ReadFile|/ReadFile> - Read a file whose name is addressed by rax into memory.

322 L<ReadTimeStampCounter|/ReadTimeStampCounter> - Read the time stamp counter and return the time in nanoseconds in rax

323 L<RegisterSize|/RegisterSize> - Return the size of a register

324 L<removeNonAsciiChars|/removeNonAsciiChars> - Return a copy of the specified string with all the non ascii characters removed

325 L<ReorderSyscallRegisters|/ReorderSyscallRegisters> - Map the list of registers provided to the 64 bit system call sequence

326 L<RestoreFirstFour|/RestoreFirstFour> - Restore the first 4 parameter registers

327 L<RestoreFirstFourExceptRax|/RestoreFirstFourExceptRax> - Restore the first 4 parameter registers except rax so it can return its value

328 L<RestoreFirstFourExceptRaxAndRdi|/RestoreFirstFourExceptRaxAndRdi> - Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values

329 L<RestoreFirstSeven|/RestoreFirstSeven> - Restore the first 7 parameter registers

330 L<RestoreFirstSevenExceptRax|/RestoreFirstSevenExceptRax> - Restore the first 7 parameter registers except rax which is being used to return the result

331 L<RestoreFirstSevenExceptRaxAndRdi|/RestoreFirstSevenExceptRaxAndRdi> - Restore the first 7 parameter registers except rax and rdi which are being used to return the results

332 L<Rq|/Rq> - Layout quad words in the data segment and return their label

333 L<Rs|/Rs> - Layout bytes in read only memory and return their label

334 L<Rutf8|/Rutf8> - Layout a utf8 encoded string as bytes in read only memory and return their label

335 L<Rw|/Rw> - Layout words in the data segment and return their label

336 L<SaveFirstFour|/SaveFirstFour> - Save the first 4 parameter registers making any parameter registers read only

337 L<SaveFirstSeven|/SaveFirstSeven> - Save the first 7 parameter registers

338 L<SetLabel|/SetLabel> - Create (if necessary) and set a label in the code section returning the label so set.

339 L<SetLengthOfShortString|/SetLengthOfShortString> - Set the length of the short string held in the numbered zmm register into the specified register

340 L<SetMaskRegister|/SetMaskRegister> - Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere

341 L<SetZF|/SetZF> - Set the zero flag

342 L<Start|/Start> - Initialize the assembler

343 L<StatSize|/StatSize> - Stat a file whose name is addressed by rax to get its size in rax

344 L<StringLength|/StringLength> - Length of a zero terminated string

345 L<Structure|/Structure> - Create a structure addressed by a register

346 L<Subroutine|/Subroutine> - Create a subroutine that can be called in assembler code

347 L<Then|/Then> - Then body for an If statement

348 L<totalBytesAssembled|/totalBytesAssembled> - Total size in bytes of all files assembled during testing

349 L<Trace|/Trace> - Add tracing code

350 L<unlinkFile|/unlinkFile> - Unlink the named file

351 L<UnReorderSyscallRegisters|/UnReorderSyscallRegisters> - Recover the initial values in registers that were reordered

352 L<V|/V> - Define a quad variable

353 L<Variable|/Variable> - Create a new variable with the specified size and name initialized via an expression

354 L<WaitPid|/WaitPid> - Wait for the pid in rax to complete

355 L<xmm|/xmm> - Add xmm to the front of a list of register expressions

356 L<ymm|/ymm> - Add ymm to the front of a list of register expressions

357 L<zmm|/zmm> - Add zmm to the front of a list of register expressions

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

my $localTest = ((caller(1))[0]//'Nasm::X86') eq "Nasm::X86";                   # Local testing mode

Test::More->builder->output("/dev/null") if $localTest;                         # Reduce number of confirmation messages during testing

if ($^O =~ m(bsd|linux|cygwin)i)                                                # Supported systems
 {if (confirmHasCommandLineCommand(q(nasm)) and LocateIntelEmulator)            # Network assembler and Intel Software Development emulator
   {plan tests => 150;
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

if (1) {                                                                        #TMov #TComment #TRs #TPrintOutMemory #TExit
  Comment "Print a string from memory";
  my $s = "Hello World";
  Mov rax, Rs($s);
  Mov rdi, length $s;
  PrintOutMemory;
  Exit(0);

  ok Assemble =~ m(Hello World);
 }

if (1) {                                                                        #TPrintOutRaxInHex #TPrintOutNL #TPrintOutString
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

if (1) {                                                                        #TDs TRs
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

  ok Assemble(debug=>0, eq => <<END);
    r8: 6867 6665 6463 6261
END
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

if (1) {                                                                        #TNasm::X86::Variable::copyZF #TNasm::X86::Variable::copyZFInverted
  Mov r15, 1;
  my $z = V(zf);
  Cmp r15, 1; $z->copyZF;         $z->outNL;
  Cmp r15, 2; $z->copyZF;         $z->outNL;
  Cmp r15, 1; $z->copyZFInverted; $z->outNL;
  Cmp r15, 2; $z->copyZFInverted; $z->outNL;

  is_deeply Assemble(debug=>0), <<END;
zf: 0000 0000 0000 0001
zf: 0000 0000 0000 0000
zf: 0000 0000 0000 0000
zf: 0000 0000 0000 0001
END
 }

if (1) {                                                                        #TAllocateMemory #TNasm::X86::Variable::freeMemory
  my $N = V(size, 2048);
  my $q = Rs('a'..'p');
  AllocateMemory($N, my $address = V(address));

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

if (1) {                                                                        #TIfNz
  Mov rax, 0;
  Test rax,rax;
  IfNz
  Then
   {PrintOutRegisterInHex rax;
   },
  Else
   {PrintOutRegisterInHex rbx;
   };
  KeepFree rax;
  Mov rax, 1;
  Test rax,rax;
  IfNz
  Then
   {PrintOutRegisterInHex rcx;
   },
  Else
   {PrintOutRegisterInHex rdx;
   };

  ok Assemble =~ m(rbx.*rcx)s;
 }

if (1) {                                                                        #TFork #TGetPid #TGetPPid #TWaitPid
  Fork;                                                                         # Fork

  Test rax,rax;
  IfNz                                                                          # Parent
  Then
   {Mov rbx, rax;
    WaitPid;
    GetPid;                                                                     # Pid of parent as seen in parent
    Mov rcx,rax;
    PrintOutRegisterInHex rax, rbx, rcx;
   },
  Else                                                                          # Child
   {Mov r8,rax;
    GetPid;                                                                     # Child pid as seen in child
    Mov r9,rax;
    GetPPid;                                                                    # Parent pid as seen in child
    Mov r10,rax;
    PrintOutRegisterInHex r8, r9, r10;
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
   {my ($start, $end, $next) = @_;
    Cmp rax, 3;
    Jge $end;
    PrintOutRegisterInHex rax;
   } rax, 16, 1;

  ok Assemble(debug => 0, eq => <<END);
   rax: 0000 0000 0000 0000
   rax: 0000 0000 0000 0001
   rax: 0000 0000 0000 0002
END
 }

if (1) {                                                                        #TBlock
  Mov rax, 0;
  Block
   {my ($start, $end) = @_;
    PrintOutRegisterInHex rax;
    Cmp rax, 3;
    Jge $end;
    Inc rax;
    PrintOutRegisterInHex rax
    Jmp $start;
   };

  ok Assemble(debug => 0, eq => <<END);
   rax: 0000 0000 0000 0000
   rax: 0000 0000 0000 0001
   rax: 0000 0000 0000 0002
   rax: 0000 0000 0000 0003
END
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
  my $N = V(size, 4096);                                                        # Size of the initial allocation which should be one or more pages

  AllocateMemory($N, my $A = V(address));

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
  ReadFile(V(file, Rs($0)), (my $s = V(size)), my $a = V(address));             # Read file
  $a->setReg(rax);                                                              # Address of file in memory
  $s->setReg(rdi);                                                              # Length  of file in memory
  PrintOutMemory;                                                               # Print contents of memory to stdout

  my $r = Assemble;                                                             # Assemble and execute
  ok stringMd5Sum($r) eq fileMd5Sum($0);                                        # Output contains this file
 }

#latest:;
if (1) {                                                                        #TCreateArena #TArena::clear #TArena::out #TArena::copy #TArena::nl
  my $a = CreateArena;                                                     # Create a string
  $a->q('aa');
  $a->out;
  PrintOutNL;
  is_deeply Assemble, <<END;                                                    # Assemble and execute
aa
END
 }

if (1) {                                                                        #TCreateArena #TArena::clear #TArena::out #TArena::copy #TArena::nl
  my $a = CreateArena;                                                     # Create a string
  my $b = CreateArena;                                                     # Create a string
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

if (1) {                                                                        #TCreateArena #TArena::clear #TArena::out #TArena::copy #TArena::nl
  my $a = CreateArena;                                                     # Create a string
  my $b = CreateArena;                                                     # Create a string
  $a->q('aa');
  $a->q('AA');
  $a->out;
  PrintOutNL;
  is_deeply Assemble, <<END;                                                    # Assemble and execute
aaAA
END
 }

if (1) {                                                                        #TCreateArena #TArena::clear #TArena::out #TArena::copy #TArena::nl
  my $a = CreateArena;                                                     # Create a string
  my $b = CreateArena;                                                     # Create a string
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

if (1) {                                                                        #TCreateArena #TArena::length  #TArena::clear #TArena::out #TArena::copy #TArena::nl
  my $a = CreateArena;                                                     # Create a string
  $a->q('ab');
  my $b = CreateArena;                                                     # Create target arena
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);
  $a->append(source=>$b->bs);
  $b->append(source=>$a->bs);
  $a->append(source=>$b->bs);
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);
  $b->append(source=>$a->bs);


  $a->out;   PrintOutNL;                                                        # Print arena
  $b->out;   PrintOutNL;                                                        # Print arena
  $a->length(my $sa = V(size)); $sa->outNL;
  $b->length(my $sb = V(size)); $sb->outNL;
  $a->clear;
  $a->length(my $sA = V(size)); $sA->outNL;
  $b->length(my $sB = V(size)); $sB->outNL;

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
  Mov   rax, 8;                                                                 # Append a constant to the arena
  Lzcnt rax, rax;                                                               # New line
  PrintOutRegisterInHex rax;
  KeepFree rax;

  Mov   rax, 8;                                                                 # Append a constant to the arena
  Tzcnt rax, rax;                                                               # New line
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: 0000 0000 0000 003C.*rax: 0000 0000 0000 0003)s;
 }

if (1) {                                                                        #TArena::nl
  my $s = CreateArena;
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

if (1) {                                                                        # Print this file  #TArena::read #TArena::z #TArena::q
  my $s = CreateArena;                                                          # Create a string
  $s->read(V(file, Rs($0)));
  $s->out;

  my $r = Assemble;
  is_deeply stringMd5Sum($r), fileMd5Sum($0);                                   # Output contains this file
 }

if (1) {                                                                        # Print rdi in hex into an arena #TGetPidInHex
  GetPidInHex;
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: 00);
 }

if (1) {                                                                        # Execute the content of an arena #TexecuteFileViaBash #TArena::write #TArena::out #TunlinkFile #TArena::ql
  my $s = CreateArena;                                                          # Create a string
  $s->ql(<<END);                                                                # Write code to execute
#!/usr/bin/bash
whoami
ls -la
pwd
END
  $s->write         (my $f = V('file', Rs("zzz.sh")));                          # Write code to a file
  executeFileViaBash($f);                                                       # Execute the file
  unlinkFile        ($f);                                                       # Delete the file

  my $u = qx(whoami); chomp($u);
  ok Assemble(emulator=>0) =~ m($u);                                            # The Intel Software Development Emulator is way too slow on these operations.
 }

if (1) {                                                                        # Make an arena readonly
  my $s = CreateArena;                                                          # Create an arena
  $s->q("Hello");                                                               # Write code to arena
  $s->makeReadOnly;                                                             # Make arena read only
  $s->q(" World");                                                              # Try to write to arena

  ok Assemble(debug=>2) =~ m(SDE ERROR: DEREFERENCING BAD MEMORY POINTER.*mov byte ptr .rax.rdx.1., r8b);
 }

if (1) {                                                                        # Make a read only arena writable  #TArena::makeReadOnly #TArena::makeWriteable
  my $s = CreateArena;                                                          # Create an arena
  $s->q("Hello");                                                               # Write data to arena
  $s->makeReadOnly;                                                             # Make arena read only - tested above
  $s->makeWriteable;                                                            # Make arena writable again
  $s->q(" World");                                                              # Try to write to arena
  $s->out;

  ok Assemble =~ m(Hello World);
 }

if (1) {                                                                        # Allocate some space in arena #TArena::allocate
  my $s = CreateArena;                                                          # Create an arena
  $s->allocate(V(size, 0x20), my $o1 = V(offset));                              # Allocate space wanted
  $s->allocate(V(size, 0x30), my $o2 = V(offset));
  $s->allocate(V(size, 0x10), my $o3 = V(offset));
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

#latest:;
if (1) {                                                                        #TPrintOutZF #TSetZF #TClearZF #TIfC #TIfNc #TIfZ #IfNz
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

  SetZF;
  IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};
  ClearZF;
  IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

  Mov r15, 5;
  Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
  Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
  Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};
  Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};

  ok Assemble(debug=>0, eq => <<END);
ZF=1
ZF=0
ZF=1
ZF=1
ZF=0
Zero
NOT zero
Carry
NO carry
Carry
NO carry
END
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
  CopyMemory(V(source, rsi), V(target, rax), V(size, rdi));
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
  AllocateMemory(K(size, $N), my $a = V(address));
  CopyMemory(V(source, $s), V(size, $N), target => $a);

  AllocateMemory(K(size, $N), my $b = V(address));
  CopyMemory(source => $a, target => $b, K(size, $N));

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
  StringLength(V(string, Rs("abcd")))->outNL;
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

  if (0)                                                                        # Hash various strings
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

if (1) {                                                                        #TIf #TIfEq #TIfNe #TIfLe #TIfLt #TIfGe #TIfGt
  my $cmp = sub
   {my ($a, $b) = @_;

    for my $op(qw(eq ne lt le gt ge))
     {Mov rax, $a;
      Cmp rax, $b;
      KeepFree rax;
      my $Op = ucfirst $op;
      eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
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

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::dump  #TNasm::X86::Variable::print #TThen #TElse #TV #TK
  my $a = V(a, 3);  $a->outNL;
  my $b = K(b, 2);  $b->outNL;
  my $c = $a +  $b; $c->outNL;
  my $d = $c -  $a; $d->outNL;
  my $e = $d == $b; $e->outNL;
  my $f = $d != $b; $f->outNL;
  my $g = $a *  $b; $g->outNL;
  my $h = $g /  $b; $h->outNL;
  my $i = $a %  $b; $i->outNL;

  If ($a == 3,
  Then
   {PrintOutStringNL "a == 3"
   },
  Else
   {PrintOutStringNL "a != 3"
   });

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
  V(limit,10)->for(sub
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
  my $a = V("a", 1);
  my $b = V("b", 2);
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
  my $start  = V("Start",  7);
  my $length = V("Length", 3);
  $start->setMask($length, k7);
  PrintOutRegisterInHex k7;

  is_deeply Assemble, <<END;
    k7: 0000 0000 0000 0380
END
 }

if (1) {                                                                        #TNasm::X86::Variable::setZmm
  my $s = Rb(0..128);
  my $source = V(Source, $s);

  if (1)                                                                        # First block
   {my $offset = V(Offset, 7);
    my $length = V(Length, 3);
    $source->setZmm(0, $offset, $length);
   }

  if (1)                                                                        # Second block
   {my $offset = V(Offset, 33);
    my $length = V(Length, 12);
    $source->setZmm(0, $offset, $length);
   }

  PrintOutRegisterInHex zmm0;

  is_deeply Assemble, <<END;
  zmm0: 0000 0000 0000 0000   0000 0000 0000 0000   0000 000B 0A09 0807   0605 0403 0201 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0201   0000 0000 0000 0000
END
 }

#latest:;
if (1) {                                                                        #TLoadZmm #Tzmm
  LoadZmm 0, 0..63;
  PrintOutRegisterInHex zmm 0;

  is_deeply Assemble, <<END;
  zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
END
 }

#latest:;
if (1) {                                                                        #TgetDFromZmm #TNasm::X86::Variable::putDIntoZmm
  my $s = Rb(0..8);
  my $c = V("Content",   "[$s]");
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
if (1) {                                                                        #TCreateString
  my $s = Rb(0..255);
  my $B =     CreateArena;
  my $b = $B->CreateString;
  $b->append(V(source, $s), V(size,  3)); $b->dump;
  $b->append(V(source, $s), V(size,  4)); $b->dump;
  $b->append(V(source, $s), V(size,  5)); $b->dump;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0201 0003

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0007
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0302 0100 0201 0007

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 000C
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0004 0302 0100   0302 0100 0201 000C

END
 }

if (1) {                                                                        #TCreateString
  my $s = Rb(0..255);
  my $B =     CreateArena;
  my $b = $B->CreateString;
  $b->append(V(source, $s), V(size, 165)); $b->dump;
  $b->append(V(source, $s), V(size,   2)); $b->dump;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 0018 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37

string Dump
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

if (1) {                                                                        #TCreateString
  my $s = Rb(0..255);
  my $B =     CreateArena;
  my $b = $B->CreateString;
  $b->append(V(source, $s), V(size,  56)); $b->dump;
  $b->append(V(source, $s), V(size,   4)); $b->dump;
  $b->append(V(source, $s), V(size,   5)); $b->dump;
  $b->append(V(source, $s), V(size,   0)); $b->dump;
  $b->append(V(source, $s), V(size, 256)); $b->dump;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0001
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 3701

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0005
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0302 0100 3705

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 000A
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0004 0302   0100 0302 0100 370A

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 000A
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0004 0302   0100 0302 0100 370A

string Dump
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
  my $B = CreateArena;
  my $b = $B->CreateString;

  $b->append(source=>V(source, $s), V(size, 256));
  $b->len(my $size = V(size));
  $size->outNL;
  $b->clear;

  $b->append(V(source, $s), size => V(size,  16)); $b->dump;
  $b->len(my $size2 = V(size));
  $size2->outNL;

  is_deeply Assemble, <<END;
size: 0000 0000 0000 0100
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0010
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 000F   0E0D 0C0B 0A09 0807   0605 0403 0201 0010

size: 0000 0000 0000 0010
END
 }

#latest:;
if (1) {
  my $c = Rb(0..255);
  my $S = CreateArena;   my $s = $S->CreateString;
  my $T = CreateArena;   my $t = $T->CreateString;

  $s->append(source=>V(source, $c), V(size, 256));
  $t->concatenate($s);
  $t->dump;

  ok Assemble(debug => 0, eq => <<END);
string Dump
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
if (1) {                                                                        # Insert char in a one string
  my $c = Rb(0..255);
  my $S = CreateArena;   my $s = $S->CreateString;

  $s->append(source=>V(source, $c), V(size, 3));
  $s->dump;

  $s->insertChar(character=>V(source, 0x44), position => V(size, 2));
  $s->dump;

  $s->insertChar(character=>V(source, 0x88), position => V(size, 2));
  $s->dump;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0201 0003

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0004
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0002 4401 0004

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0005
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0244 8801 0005

END
 }

#latest:;

if (1) {                                                                        # Insert char in a multi string at position 22
  my $c = Rb(0..255);
  my $S = CreateArena;   my $s = $S->CreateString;

  $s->append(source=>V(source, $c), V(size, 58));
  $s->dump;

  $s->insertChar(V(character, 0x44), V(position, 22));
  $s->dump;

  $s->insertChar(V(character, 0x88), V(position, 22));
  $s->dump;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 3938 3703

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0016
 zmm31: 0000 0098 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0016
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0022
 zmm31: 0000 0058 0000 0058   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 5836 3534   3332 3130 2F2E 2D2C   2B2A 2928 2726 2524   2322 2120 1F1E 1D1C   1B1A 1918 1716 4422
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 3938 3703

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0017
 zmm31: 0000 0098 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   8815 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0017
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0022
 zmm31: 0000 0058 0000 0058   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 5836 3534   3332 3130 2F2E 2D2C   2B2A 2928 2726 2524   2322 2120 1F1E 1D1C   1B1A 1918 1716 4422
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 3938 3703

END
 }

if (1) {                                                                        #String::insertChar
  my $c = Rb(0..255);
  my $S = CreateArena;   my $s = $S->CreateString;

  $s->append(source=>V(source, $c), V(size, 166));
  $s->dump;

  $s->insertChar(V(character, 0x44), V(position, 64));
  $s->dump;

  $s->insertChar(V(character, 0x88), V(position, 64));
  $s->dump;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 00D8   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 00D8 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37
Offset: 0000 0000 0000 00D8   Length: 0000 0000 0000 0001
 zmm31: 0000 0018 0000 0098   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 A501

string Dump
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

string Dump
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
  my $S = CreateArena;   my $s = $S->CreateString;

  $s->append(source=>V(source, $c),  V(size, 3));      $s->dump;
  $s->insertChar(V(character, 0x44), V(position, 64)); $s->dump;
  $s->len(my $size = V(size));                          $size->outNL;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0003
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0201 0003

string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0004
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0044 0201 0004

size: 0000 0000 0000 0004
END
 }

if (1) {                                                                        #TString::deleteChar #TString::len
  my $c = Rb(0..255);
  my $S = CreateArena;   my $s = $S->CreateString;

  $s->append(source=>V(source, $c),  V(size, 165)); $s->dump;
  $s->deleteChar(V(position, 0x44));                 $s->dump;
  $s->len(my $size = V(size));                       $size->outNL;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0098   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0098 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737
Offset: 0000 0000 0000 0098   Length: 0000 0000 0000 0037
 zmm31: 0000 0018 0000 0058   A4A3 A2A1 A09F 9E9D   9C9B 9A99 9897 9695   9493 9291 908F 8E8D   8C8B 8A89 8887 8685   8483 8281 807F 7E7D   7C7B 7A79 7877 7675   7473 7271 706F 6E37

string Dump
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

if (1) {                                                                        #TString::getChar
  my $c = Rb(0..255);
  my $S = CreateArena;   my $s = $S->CreateString;

  $s->append(source=>V(source, $c),  V(size, 110)); $s->dump;
  $s->getCharacter(V(position, 0x44), my $out = V(out)); $out->outNL;

  ok Assemble(debug => 0, eq => <<END);
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0037
 zmm31: 0000 0058 0000 0058   3635 3433 3231 302F   2E2D 2C2B 2A29 2827   2625 2423 2221 201F   1E1D 1C1B 1A19 1817   1615 1413 1211 100F   0E0D 0C0B 0A09 0807   0605 0403 0201 0037
Offset: 0000 0000 0000 0058   Length: 0000 0000 0000 0037
 zmm31: 0000 0018 0000 0018   6D6C 6B6A 6968 6766   6564 6362 6160 5F5E   5D5C 5B5A 5958 5756   5554 5352 5150 4F4E   4D4C 4B4A 4948 4746   4544 4342 4140 3F3E   3D3C 3B3A 3938 3737

out: 0000 0000 0000 0044
END
 }

#latest:;

if (1) {                                                                        #TNasm::X86::Variable::setMask
  my $z = V('zero', 0);
  my $o = V('one',  1);
  my $t = V('two',  2);
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
if (1) {                                                                        #TCreateArray  #TArray::push
  my $c = Rb(0..255);
  my $A = CreateArena;  my $a = $A->CreateArray;

  $a->push(element => V($_, $_)) for 1..15;  $A->dump;
  $a->push(element => V($_, $_)) for 0xff;   $A->dump;
  $a->push(element => V($_, $_)) for 17..31; $A->dump;
  $a->push(element => V($_, $_)) for 0xee;   $A->dump;
  $a->push(element => V($_, $_)) for 33..36; $A->dump;

  ok Assemble(debug => 0, eq => <<END);
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0058
0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000F00 0000 0100 00000200 0000 0300 00000400 0000 0500 00000600 0000 0700 00000800 0000 0900 0000
0040: 0A00 0000 0B00 00000C00 0000 0D00 00000E00 0000 0F00 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00001000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 00D8
0000: 0010 0000 0000 0000D800 0000 0000 00000000 0000 0000 00001F00 0000 5800 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00001100 0000 1200 00001300 0000 1400 00001500 0000 1600 00001700 0000 1800 00001900 0000 1A00 0000
00C0: 1B00 0000 1C00 00001D00 0000 1E00 00001F00 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 00D8
0000: 0010 0000 0000 0000D800 0000 0000 00000000 0000 0000 00002000 0000 5800 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00001100 0000 1200 00001300 0000 1400 00001500 0000 1600 00001700 0000 1800 00001900 0000 1A00 0000
00C0: 1B00 0000 1C00 00001D00 0000 1E00 00001F00 0000 EE00 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0118
0000: 0010 0000 0000 00001801 0000 0000 00000000 0000 0000 00002400 0000 5800 00009800 0000 D800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0080: 0B00 0000 0C00 00000D00 0000 0E00 00000F00 0000 FF00 00001100 0000 1200 00001300 0000 1400 00001500 0000 1600 00001700 0000 1800 00001900 0000 1A00 0000
00C0: 1B00 0000 1C00 00001D00 0000 1E00 00001F00 0000 EE00 00002100 0000 2200 00002300 0000 2400 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

#latest:;
if (1) {                                                                        #TCreateArray  #TArray::push #TArray::pop #TArray::put #TArray::get
  my $c = Rb(0..255);
  my $A = CreateArena;  my $a = $A->CreateArray;
  my $l = V(limit, 15);
  my $L = $l + 5;

  my sub put                                                                    # Put a constant or a variable
   {my ($e) = @_;
    $a->push(element => (ref($e) ? $e : V($e, $e)));
   };

  my sub get                                                                    # Get a constant or a variable
   {my ($i) = @_;
    $a->get(index=>(my $v = ref($i) ? $i : V('index', $i)), my $e = V(element));
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
   {$a->put(my $i = V('index',  9), my $e = V(element, 0xFFF9));
    get(9);
   }

  if (1)
   {$a->put(my $i = V('index', 19), my $e = V(element, 0xEEE9));
    get(19);
   }

  $a->dump;
  ($l+$L+1)->for(sub
   {my ($i, $start, $next, $end) = @_;
    $a->pop(my $e = V(element));
    $e->outNL;
    If (($e == 33)|($e == 32)|($e == 17)|($e == 16)|($e == 15)|($e == 14)|($e == 1)|($e == 0), sub
     {$a->dump;
     });
   });

  V(limit, 38)->for(sub                                                         # Push using a loop and reusing the freed space
   {my ($index, $start, $next, $end) = @_;
    $a->push(element=>$index*2);
   });

  $a->dump;

  V(limit, 38)->for(sub                                                         # Push using a loop and reusing the freed space
   {my ($index, $start, $next, $end) = @_;
    $a->pop(my $e = V(element));
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
array
Size: 0000 0000 0000 0024   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 00D8 0000 0098   0000 0058 0000 0024
Full: 0000 0000 0000 0058   zmm30: 0000 0010 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 FFF9 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
Full: 0000 0000 0000 0098   zmm30: 0000 0020 0000 001F   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 EEE9 0000 0013   0000 0012 0000 0011
Last: 0000 0000 0000 00D8   zmm30: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0024 0000 0023   0000 0022 0000 0021
element: 0000 0000 0000 0024
element: 0000 0000 0000 0023
element: 0000 0000 0000 0022
element: 0000 0000 0000 0021
array
Size: 0000 0000 0000 0020   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0098   0000 0058 0000 0020
Full: 0000 0000 0000 0058   zmm30: 0000 0010 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 FFF9 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
Full: 0000 0000 0000 0098   zmm30: 0000 0020 0000 001F   0000 001E 0000 001D   0000 001C 0000 001B   0000 001A 0000 0019   0000 0018 0000 0017   0000 0016 0000 0015   0000 EEE9 0000 0013   0000 0012 0000 0011
element: 0000 0000 0000 0020
array
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
array
Size: 0000 0000 0000 0010   zmm31: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0058 0000 0010
Full: 0000 0000 0000 0058   zmm30: 0000 0010 0000 000F   0000 000E 0000 000D   0000 000C 0000 000B   0000 FFF9 0000 0009   0000 0008 0000 0007   0000 0006 0000 0005   0000 0004 0000 0003   0000 0002 0000 0001
element: 0000 0000 0000 0010
array
Size: 0000 0000 0000 000F   zmm31: 0000 000F 0000 000E   0000 000D 0000 000C   0000 000B 0000 FFF9   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 000F
element: 0000 0000 0000 000F
array
Size: 0000 0000 0000 000E   zmm31: 0000 000F 0000 000E   0000 000D 0000 000C   0000 000B 0000 FFF9   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 000E
element: 0000 0000 0000 000E
array
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
array
Size: 0000 0000 0000 0000   zmm31: 0000 000F 0000 000E   0000 000D 0000 000C   0000 000B 0000 FFF9   0000 0009 0000 0008   0000 0007 0000 0006   0000 0005 0000 0004   0000 0003 0000 0002   0000 0001 0000 0000
array
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
array
Size: 0000 0000 0000 0000   zmm31: 0000 001C 0000 001A   0000 0018 0000 0016   0000 0014 0000 0012   0000 0010 0000 000E   0000 000C 0000 000A   0000 0008 0000 0006   0000 0004 0000 0002   0000 0000 0000 0000
END
 }
#exit if $develop;

#latest:;
if (1) {                                                                        #TNasm::X86::Arena::allocBlock #TNasm::X86::Arena::freeBlock
  my $a = CreateArena; $a->dump;
  my $b1 = $a->allocBlock;  $a->dump;
  my $b2 = $a->allocBlock;  $a->dump;
  $a->freeBlock($b2);       $a->dump;
  $a->freeBlock($b1);       $a->dump;

  ok Assemble(debug => 0, eq => <<END);
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0018
0000: 0010 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0058
0000: 0010 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00005800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0098
0000: 0010 0000 0000 00009800 0000 0000 00001800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000000 0000 5800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

#latest:;

if (1) {                                                                        #TCreateArray  #TArray::push
  my $c = Rb(0..255);
  my $A = CreateArena;  my $a = $A->CreateArray;

  my sub put
   {my ($e) = @_;
    $a->push(element => V($e, $e));
   };

  my sub get
   {my ($i) = @_;                                                               # Parameters
    $a->get(my $v = V('index', $i), my $e = V(element));
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
if (1) {                                                                        # Insert key for Tree
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
if (1) {                                                                        #TNasm::X86::Arena::chain
  my $format = Rd(map{4*$_+24} 0..64);

  my $b = CreateArena;
  my $a = $b->allocBlock;
  Vmovdqu8 zmm31, "[$format]";
  $b->putBlock($b->bs, $a, 31);
  my $r = $b->chain($b->bs, V(start, 0x18), 4);       $r->outNL("chain1: ");
  my $s = $b->chain($b->bs, $r, 4);                   $s->outNL("chain2: ");
  my $t = $b->chain($b->bs, $s, 4);                   $t->outNL("chain3: ");
  my $A = $b->chain($b->bs, V(start, 0x18), 4, 4, 4); $A->outNL("chain4: ");    # Get a long chain

  $b->putChain($b->bs, V(start, 0x18), V(end, 0xff), 4, 4, 4);                  # Put at the end of a long chain

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
   } name=> 'aaa', in => [qw(c)], io => [qw(d  e  f)];

  my $c = K(c, -1);
  my $d = K(d, -1);
  my $e = V(e,  1);
  my $f = V(f,  2);

  $sub->call($c, $d, $e, $f);
  $f->outNL('F3: ');

  ok Assemble(debug => 0, eq => <<END);
chain1: 0000 0000 0000 001C
chain2: 0000 0000 0000 0020
chain3: 0000 0000 0000 0024
chain4: 0000 0000 0000 0024
Arena
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
if (1) {                                                                        #TLoadConstantIntoMaskRegister #TPopEax #IfZ
  Mov r14, 0;
  Kmovq k0, r14;
  KeepFree r14;
  Ktestq k0, k0;
  IfZ Then {PrintOutStringNL "0 & 0 == 0"};
  PrintOutZF;

  LoadConstantIntoMaskRegister k1, 1;
  Ktestq k1, k1;
  IfNz Then {PrintOutStringNL "1 & 1 != 0"};
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

  my $a = V('aaaa');
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
if (1) {                                                                        #TNasm::X86::Tree::splitFullLeftNode
  my $Sk = Rd(17..28, 0, 0, 12,   0xFF);
  my $Sd = Rd(17..28, 0, 0, 0xDD, 0xEE);
  my $Sn = Rd(1..13,     0, 0,    0xCC);

  my $sk = Rd(1..14, 14,   0xA1);
  my $sd = Rd(1..14, 0xCC, 0xA2);
  my $sn = Rd(1..15,       0xA3);

  my $rk = Rd((0)x14, 14,   0xB1);
  my $rd = Rd((0)x14, 0xCC, 0xB2);
  my $rn = Rd((0)x15,       0xB3);

  my $b = CreateArena;
  my $t = $b->CreateTree;

  Vmovdqu8 zmm31, "[$Sk]";
  Vmovdqu8 zmm30, "[$Sd]";
  Vmovdqu8 zmm29, "[$Sn]";

  Vmovdqu8 zmm28, "[$sk]";
  Vmovdqu8 zmm27, "[$sd]";
  Vmovdqu8 zmm26, "[$sn]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

   $t->splitFullLeftNode;

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

  my $b = CreateArena;
  my $t = $b->CreateTree;

  Vmovdqu8 zmm31, "[$tk]";
  Vmovdqu8 zmm30, "[$td]";
  Vmovdqu8 zmm29, "[$tn]";

  Vmovdqu8 zmm28, "[$lk]";
  Vmovdqu8 zmm27, "[$ld]";
  Vmovdqu8 zmm26, "[$ln]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

  $t->splitFullLeftNode;

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
if (1) {                                                                        #TNasm::X86::Tree::splitFullRightNode
  my $tk = Rd(1..12, 0, 0, 12,      0xC1);
  my $td = Rd(1..12, 0, 0,  0,      0xC2);
  my $tn = Rd(1, 0xBB, 3..13, 0, 0, 0xCC);

  my $lk = Rd(17..30, 14,   0xA1);
  my $ld = Rd(17..30, 0xCC, 0xA2);
  my $ln = Rd(17..31,       0xAA);

  my $rk = Rd(17..30, 14,   0xB1);
  my $rd = Rd(17..30, 0xCC, 0xB2);
  my $rn = Rd(17..31,       0xBB);

  my $b = CreateArena;
  my $t = $b->CreateTree;

  Vmovdqu8 zmm31, "[$tk]";
  Vmovdqu8 zmm30, "[$td]";
  Vmovdqu8 zmm29, "[$tn]";

  Vmovdqu8 zmm28, "[$lk]";
  Vmovdqu8 zmm27, "[$ld]";
  Vmovdqu8 zmm26, "[$ln]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

  $t->splitFullRightNode;

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

  my $b = CreateArena;
  my $t = $b->CreateTree;

  Vmovdqu8 zmm31, "[$tk]";
  Vmovdqu8 zmm30, "[$td]";
  Vmovdqu8 zmm29, "[$tn]";

  Vmovdqu8 zmm28, "[$lk]";
  Vmovdqu8 zmm27, "[$ld]";
  Vmovdqu8 zmm26, "[$ln]";

  Vmovdqu8 zmm25, "[$rk]";
  Vmovdqu8 zmm24, "[$rd]";
  Vmovdqu8 zmm23, "[$rn]";

  $t->splitFullRightNode;

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
  my $b = CreateArena;
  my $t = $b->CreateTree;

  V(count, 24)->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $k = $index + 1; my $d = $k + 0x100;
    $t->insert($k, $d);
   });

  $t->getKeysDataNode($t->first, 31, 30, 29);
  PrintOutStringNL "Root"; $t->first->outNL('First: ');
  PrintOutRegisterInHex zmm31, zmm30, zmm29;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0xd8), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0x258), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0x198), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

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
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Arena::CreateTree
  my $N = 12;
  my $b = CreateArena;                                                     # Resizable memory block
  my $t = $b->CreateTree;                                          # Multi way tree in memory block

  K(count, $N)->for(sub                                                         # Add some entries to the tree
   {my ($index, $start, $next, $end) = @_;
    my $k = $index + 1;
    $t->insert($k,      $k + 0x100);
    $t->insert($k + $N, $k + 0x200);
   });

  $t->by(sub                                                                    # Iterate through the tree
   {my ($iter, $end) = @_;
    $iter->key ->out('key: ');
    $iter->data->out(' data: ');
    $iter->tree->depth($iter->node, my $D = V(depth));

    $t->find($iter->key);
    $t->found->out(' found: '); $t->data->out(' data: '); $D->outNL(' depth: ');
   });

  $t->find(K(key, 0xffff));  $t->found->outNL('Found: ');                      # Find some entries
  $t->find(K(key, 0xd));     $t->found->outNL('Found: ');
  If ($t->found,
  Then
   {$t->data->outNL("Data : ");
   });

  ok Assemble(debug => 0, eq => <<END);
key: 0000 0000 0000 0001 data: 0000 0000 0000 0101 found: 0000 0000 0000 0001 data: 0000 0000 0000 0101 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0002 data: 0000 0000 0000 0102 found: 0000 0000 0000 0001 data: 0000 0000 0000 0102 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0003 data: 0000 0000 0000 0103 found: 0000 0000 0000 0001 data: 0000 0000 0000 0103 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0004 data: 0000 0000 0000 0104 found: 0000 0000 0000 0001 data: 0000 0000 0000 0104 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0005 data: 0000 0000 0000 0105 found: 0000 0000 0000 0001 data: 0000 0000 0000 0105 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0006 data: 0000 0000 0000 0106 found: 0000 0000 0000 0001 data: 0000 0000 0000 0106 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0007 data: 0000 0000 0000 0107 found: 0000 0000 0000 0001 data: 0000 0000 0000 0107 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0008 data: 0000 0000 0000 0108 found: 0000 0000 0000 0001 data: 0000 0000 0000 0108 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0009 data: 0000 0000 0000 0109 found: 0000 0000 0000 0001 data: 0000 0000 0000 0109 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000A data: 0000 0000 0000 010A found: 0000 0000 0000 0001 data: 0000 0000 0000 010A depth: 0000 0000 0000 0002
key: 0000 0000 0000 000B data: 0000 0000 0000 010B found: 0000 0000 0000 0001 data: 0000 0000 0000 010B depth: 0000 0000 0000 0002
key: 0000 0000 0000 000C data: 0000 0000 0000 010C found: 0000 0000 0000 0001 data: 0000 0000 0000 010C depth: 0000 0000 0000 0002
key: 0000 0000 0000 000D data: 0000 0000 0000 0201 found: 0000 0000 0000 0001 data: 0000 0000 0000 0201 depth: 0000 0000 0000 0001
key: 0000 0000 0000 000E data: 0000 0000 0000 0202 found: 0000 0000 0000 0001 data: 0000 0000 0000 0202 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000F data: 0000 0000 0000 0203 found: 0000 0000 0000 0001 data: 0000 0000 0000 0203 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0010 data: 0000 0000 0000 0204 found: 0000 0000 0000 0001 data: 0000 0000 0000 0204 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0011 data: 0000 0000 0000 0205 found: 0000 0000 0000 0001 data: 0000 0000 0000 0205 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0012 data: 0000 0000 0000 0206 found: 0000 0000 0000 0001 data: 0000 0000 0000 0206 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0013 data: 0000 0000 0000 0207 found: 0000 0000 0000 0001 data: 0000 0000 0000 0207 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0014 data: 0000 0000 0000 0208 found: 0000 0000 0000 0001 data: 0000 0000 0000 0208 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0015 data: 0000 0000 0000 0209 found: 0000 0000 0000 0001 data: 0000 0000 0000 0209 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0016 data: 0000 0000 0000 020A found: 0000 0000 0000 0001 data: 0000 0000 0000 020A depth: 0000 0000 0000 0002
key: 0000 0000 0000 0017 data: 0000 0000 0000 020B found: 0000 0000 0000 0001 data: 0000 0000 0000 020B depth: 0000 0000 0000 0002
key: 0000 0000 0000 0018 data: 0000 0000 0000 020C found: 0000 0000 0000 0001 data: 0000 0000 0000 020C depth: 0000 0000 0000 0002
Found: 0000 0000 0000 0000
Found: 0000 0000 0000 0001
Data : 0000 0000 0000 0201
END
 }

#latest:
if (1) {                                                                        #TLoadBitsIntoMaskRegister
  for (0..7)
   {ClearRegisters "k$_";
    K($_,$_)->setMaskBit("k$_");
    PrintOutRegisterInHex "k$_";
   }

  ClearRegisters k7;
  LoadBitsIntoMaskRegister(k7, '1010', -4, +4, -2, +2, -1, +1, -1, +1);
  PrintOutRegisterInHex "k7";

  ok Assemble(debug => 0, eq => <<END);
    k0: 0000 0000 0000 0001
    k1: 0000 0000 0000 0002
    k2: 0000 0000 0000 0004
    k3: 0000 0000 0000 0008
    k4: 0000 0000 0000 0010
    k5: 0000 0000 0000 0020
    k6: 0000 0000 0000 0040
    k7: 0000 0000 0000 0080
    k7: 0000 0000 000A 0F35
END
 }

#latest:
if (1) {
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $d = V(data);
  my $f = V(found);

  my $N = 24;
  V(count, $N)->for(sub
   {my ($index, $start, $next, $end) = @_;
    if (1)
     {my $k = $index *  2 + 1;      my $d = $k + 0x100;
      $t->insert($k, $d);
     }
    if (1)
     {my $k = $index * -2 + 2 * $N; my $d = $k + 0x100;
      $t->insert($k, $d);
     }
   });

  $t->getKeysDataNode($t->first, 31, 30, 29);
  PrintOutStringNL "Root"; $t->first->outNL('First: ');
  PrintOutRegisterInHex zmm31, zmm30, zmm29;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0x258), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0x3d8), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0x318), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0xd8), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;

  KeepFree zmm 26;
  $t->getKeysDataNode(V(offset, 0x198), 28,27,26);
  PrintOutStringNL "Left";
  PrintOutRegisterInHex zmm28, zmm27, zmm26;


  $t->find(V(key, 0xffff));  $t->found->outNL('Found: ');
  $t->find(V(key, 0x1b)  );  $t->found->outNL('Found: ');

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
  my @p = my ($out, $size, $fail) = (V(out), V(size), V('fail'));

  my $Chars = Rb(0x24, 0xc2, 0xa2, 0xc9, 0x91, 0xE2, 0x82, 0xAC, 0xF0, 0x90, 0x8D, 0x88);
  my $chars = V(chars, $Chars);

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

  my $s = K(statement, Rs($statement));
  my $l = K(size,  length($statement));

  AllocateMemory($l, my $address = V(address));                                 # Allocate enough memory for a copy of the string
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
END
 }

#latest:
if (1) {                                                                        #TsetOrClearTreeBits
  ClearRegisters zmm0;
  my $b = CreateArena;
  my $t = $b->CreateTree;

  Mov r15, 8;
  $t->setTree  (r15, 0); PrintOutRegisterInHex zmm0;
  $t->isTree   (r15, 0); PrintOutZF;

  Mov r15, 16;
  $t->isTree   (r15, 0); PrintOutZF;
  $t->setTree  (r15, 0); PrintOutRegisterInHex zmm0;
  $t->clearTree(r15, 0); PrintOutRegisterInHex zmm0;
  $t->isTree   (r15, 0); PrintOutZF;

  ok Assemble(debug => 0, eq => <<END);
  zmm0: 0000 0000 0008 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
ZF=0
ZF=1
  zmm0: 0000 0000 0018 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm0: 0000 0000 0008 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
ZF=1
END
 }

#latest:
if (1) {                                                                        #TInsertZeroIntoRegisterAtPoint #TInsertOneIntoRegisterAtPoint
  Mov r15, 0x100;                                                               # Given a register with a single one in it indicating the desired position,
  Mov r14, 0xFFDC;                                                              # Insert a zero into the register at that position shifting the bits above that position up left one to make space for the new zero.
  Mov r13, 0xF03F;
  PrintOutRegisterInHex         r14, r15;
  InsertZeroIntoRegisterAtPoint r15, r14;
  PrintOutRegisterInHex r14;
  Or r14, r15;                                                                  # Replace the inserted zero with a one
  PrintOutRegisterInHex r14;
  InsertOneIntoRegisterAtPoint r15, r13;
  PrintOutRegisterInHex r13;
  ok Assemble(debug => 0, eq => <<END);
   r14: 0000 0000 0000 FFDC
   r15: 0000 0000 0000 0100
   r14: 0000 0000 0001 FEDC
   r14: 0000 0000 0001 FFDC
   r13: 0000 0000 0001 E13F
END
 }

#latest:
if (1) {
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $k = V(key,  15);

  $t->insertTree($k);  $t->data->outNL;
  $t->insertTree($k);  $t->data->outNL;                                         # Retrieve the sub tree rather than creating a new new sub tree

  ok Assemble(debug => 0, eq => <<END);
data: 0000 0000 0000 0098
data: 0000 0000 0000 0098
END
 }

#latest:
if (1) {                                                                        # Replace a scalar with a tree in the first node
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $k = V(key,  15);
  my $d = V(data, 14);

  $t->insert($k, $d);  $d->outNL;
  $t->insertTree($k);  $t->data->outNL;                                         # Retrieve the sub tree rather than creating a new new sub tree
  $t->insertTree($k);  $t->data->outNL;

  ok Assemble(debug => 0, eq => <<END);
data: 0000 0000 0000 000E
data: 0000 0000 0000 0098
data: 0000 0000 0000 0098
END
 }

#latest:
if (1) {                                                                        # Replace a scalar with a tree in the first node
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $k = V(key,  15);
  my $d = V(data, 14);

  for my $i(1..11)                                                              # Create new sub trees
   {$t->insertTree(V(key,  $i));  $t->data->outNL;                              # Retrieve the sub tree rather than creating a new new sub tree
   }

  $b->dump;
  ok Assemble(debug => 0, eq => <<END);                                         # Tree bits at 0x50
data: 0000 0000 0000 0098
data: 0000 0000 0000 0118
data: 0000 0000 0000 0198
data: 0000 0000 0000 0218
data: 0000 0000 0000 0298
data: 0000 0000 0000 0318
data: 0000 0000 0000 0398
data: 0000 0000 0000 0418
data: 0000 0000 0000 0498
data: 0000 0000 0000 0518
data: 0000 0000 0000 0598
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 0618
0000: 0010 0000 0000 00001806 0000 0000 00000000 0000 0000 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0800 00000900 0000 0A00 0000
0040: 0B00 0000 0000 00000000 0000 0000 00000B00 FF07 5800 00009800 0000 1801 00009801 0000 1802 00009802 0000 1803 00009803 0000 1804 00009804 0000 1805 0000
0080: 9805 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 D800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::transferTreeBitsFromParent
  my $B = Rb(0..63);
  Vmovdqu8 zmm0, "[$B]";
  loadFromZmm r15, w, zmm, 14;

  my $b = CreateArena;
  my $t = $b->CreateTree;
  $t->getTreeBits(0, r14);

  PrintOutRegisterInHex zmm0, r15, r14;

  Mov r14, my $treeBits = 0xDCBA;
  $t->putTreeBits(1, r14);
  PrintOutRegisterInHex zmm1;

  $t->transferTreeBitsFromParent(1, 2, 3);
  PrintOutStringNL "Split:";
  PrintOutRegisterInHex zmm1, zmm2, zmm3;

  my $left  =  $treeBits & ((1<<$t->leftLength)  - 1);
  my $right = ($treeBits >>    ($t->leftLength   + 1)) & ((1<<$t->rightLength) - 1);

  my $l = sprintf("%02X", $left);
  my $r = sprintf("%02X", $right);

  ok Assemble(debug => 0, eq => <<END);
  zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
   r15: 0000 0000 0000 0F0E
   r14: 0000 0000 0000 3B3A
  zmm1: 0000 0000 DCBA 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
Split:
  zmm1: 0000 0000 0001 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm2: 0000 0000 00$l 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm3: 0000 0000 00$r 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::transferTreeBitsFromLeft #TNasm::X86::Tree::transferTreeBitsFromRight
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $lR = "110110";
  my $lP = "1";
  my $lL = "1110111";

  my $p1 = "01010_110010";
  my $p2 = "1";

  my $epe = sprintf("%04X", eval "0b$p1$lP$p2");
  my $ele = sprintf("%04X", eval "0b$lL"      );
  my $ere = sprintf("%04X", eval "0b$lR"      );

  my @expected;
  for my $i(0..1)
   {Mov r15, eval "0b$lR$lP$lL"; $t->putTreeBits(1+$i, r15);
    Mov r15, eval "0b$p1$p2";    $t->putTreeBits(0,    r15);

    PrintOutRegisterInHex zmm 0, 1+$i;

    Mov r15, 0b10;
    $t->transferTreeBitsFromLeft (r15, 0, 1, 2) unless $i;
    $t->transferTreeBitsFromRight(r15, 0, 1, 2) if     $i;
    PrintOutRegisterInHex zmm 0..2;

    my $zzz = $i ? "zmm2" : "zmm1";
    push @expected, <<END;
  zmm0: 0000 0000 0565 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  $zzz: 0000 0000 36F7 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm0: 0000 0000 $epe 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm1: 0000 0000 $ele 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm2: 0000 0000 $ere 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
END
   }

  ok Assemble(debug => 0, eq => join "", @expected);
 }

#latest:
if (1) {                                                                        # Replace a scalar with a tree in the first node
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $k = V(key,  15);

  for my $i(1..15)                                                              # Overflow the root node to force a split
   {my $d = V(data, 2 * $i);
    $t->insert    (V(key,  $i), $d),   $d->outNL if     $i % 2;
    $t->insertTree(V(key,  $i)), $t->data->outNL unless $i % 2;
   }

  $b->dump(20);
  ok Assemble(debug => 0, eq => <<END);
data: 0000 0000 0000 0002
data: 0000 0000 0000 0098
data: 0000 0000 0000 0006
data: 0000 0000 0000 0118
data: 0000 0000 0000 000A
data: 0000 0000 0000 0198
data: 0000 0000 0000 000E
data: 0000 0000 0000 0218
data: 0000 0000 0000 0012
data: 0000 0000 0000 0298
data: 0000 0000 0000 0016
data: 0000 0000 0000 0318
data: 0000 0000 0000 001A
data: 0000 0000 0000 0398
data: 0000 0000 0000 001E
Arena
  Size: 0000 0000 0000 1000
  Used: 0000 0000 0000 05D8
0000: 0010 0000 0000 0000D805 0000 0000 00000000 0000 0000 00000800 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0040: 0000 0000 0000 00000000 0000 0000 00000100 0100 5800 00001802 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0080: 0000 0000 0000 00000000 0000 0000 00000000 0000 1804 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
00C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 D800 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0100: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0140: 0000 0000 0000 00000000 0000 0000 00000000 0000 5801 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0180: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
01C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 D801 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0200: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0240: 0000 0000 0000 00000000 0000 0000 00000000 0000 5802 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0280: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
02C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 D802 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0300: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0340: 0000 0000 0000 00000000 0000 0000 00000000 0000 5803 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0380: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
03C0: 0000 0000 0000 00000000 0000 0000 00000000 0000 D803 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0400: 0000 0000 0000 00000000 0000 0000 00000000 0000 0000 00005804 0000 1805 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
0440: 0000 0000 0000 00000000 0000 0000 00000000 0000 1800 00000100 0000 0200 00000300 0000 0400 00000500 0000 0600 00000700 0000 0000 00000000 0000 0000 0000
0480: 0000 0000 0000 00000000 0000 0000 00000700 2A00 9804 00000200 0000 9800 00000600 0000 1801 00000A00 0000 9801 00000E00 0000 0000 00000000 0000 0000 0000
04C0: 0000 0000 0000 00000000 0000 0000 00001800 0000 D804 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 00000000 0000 0000 0000
END
 }

#latest:
if (1) {                                                                        # Extended sub tree testing
  my $b  = CreateArena;
  my $t  = $b->CreateTree;
  LoadZmm(0, (0) x 58, 0xf7, (0) x 5);
  PrintOutRegisterInHex zmm0;

  Mov r15, 2;
  $t->expandTreeBitsWithZero(0, r15); PrintOutRegisterInHex zmm0;
  $t->expandTreeBitsWithZero(0, r15); PrintOutRegisterInHex zmm0;
  $t->expandTreeBitsWithZero(0, r15); PrintOutRegisterInHex zmm0;
  $t->expandTreeBitsWithZero(0, r15); PrintOutRegisterInHex zmm0;

  LoadZmm(1, (0) x 58, 0xf0, (0) x 5);
  PrintOutRegisterInHex zmm1;

  Mov r15, 2;
  $t->expandTreeBitsWithOne(1, r15); PrintOutRegisterInHex zmm1;
  $t->expandTreeBitsWithOne(1, r15); PrintOutRegisterInHex zmm1;
  $t->expandTreeBitsWithOne(1, r15); PrintOutRegisterInHex zmm1;
  $t->expandTreeBitsWithOne(1, r15); PrintOutRegisterInHex zmm1;


  ok Assemble(debug => 0, eq => <<END);
  zmm0: 0000 0000 00F7 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm0: 0000 0000 01ED 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm0: 0000 0000 03D9 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm0: 0000 0000 07B1 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm0: 0000 0000 0F61 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm1: 0000 0000 00F0 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm1: 0000 0000 01E2 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm1: 0000 0000 03C6 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm1: 0000 0000 078E 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm1: 0000 0000 0F1E 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
END
 }

#latest:
if (1) {                                                                        #
  my $N = 45; my $M = 0;
     $N % 2 == 1 or confess "Must be odd";
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $L = V(loop, $N);
  my %I;

  for(my $i = 0; $i < ($N-$M); ++$i)                                            # The insertions we intend to make
   {my $l = $N - $i;
    if ($i % 2 == 0)
     {$I{$i} = $l;                                                              # Scalar
      $I{$l} = -1;                                                              # Tree
     }
   }

  ($L-$M)->for(sub                                                              # Do the planned insertions
   {my ($i, $start, $next, $end) = @_;
    my $l = $L - $i;
    If ($i % 2 == 0, sub
     {$t->insert($i, $l);
      $t->insertTree($l);
     });
   });

  ($L+2)->for(sub                                                               # Find each key
   {my ($i, $start, $next, $end) = @_;
    $t->find($i);
    $i->out('i: '); $t->found->out('  f: '); $t->data->out('  d: '); $t->subTree->outNL('  s: ');
   });

  Assemble(debug => 0);

  if (1)                                                                        # Check output has right structure
   {my @r = readFile(q(zzzOut.txt));

    for my $l(@r)
     {my @w = split /\s*\w:\s+/, $l;
      shift @w; s/\s+//gs for @w; $_ = eval("0x$_") for @w;
      my ($k, $f, $d, $s) = @w;
                                                                                # Inserted
      if (defined(my $D = $I{$k}))
       {if ($D >= 0)                                                            # Scalar
         {$f == 1  or warn "F != 1 at key $k";
          $d == $D or warn "Wrong data    at key $k";
          $s == 0  or warn "Wrong subTree at key $k";
         }
        else
         {$d % 16 == 8 or warn "Wrong data    at key $k";
          $s == 1      or warn "Wrong subTree at key $k";
         }
       }
      else
       {$f == 0 && $d == 0 && $s == 0 or confess "Find should fail at key $k";
       }
     }
   };

  is_deeply scalar(readFile(q(zzzOut.txt))), <<END if $N == 45;
i: 0000 0000 0000 0000  f: 0000 0000 0000 0001  d: 0000 0000 0000 002D  s: 0000 0000 0000 0000
i: 0000 0000 0000 0001  f: 0000 0000 0000 0001  d: 0000 0000 0000 0ED8  s: 0000 0000 0000 0001
i: 0000 0000 0000 0002  f: 0000 0000 0000 0001  d: 0000 0000 0000 002B  s: 0000 0000 0000 0000
i: 0000 0000 0000 0003  f: 0000 0000 0000 0001  d: 0000 0000 0000 0E58  s: 0000 0000 0000 0001
i: 0000 0000 0000 0004  f: 0000 0000 0000 0001  d: 0000 0000 0000 0029  s: 0000 0000 0000 0000
i: 0000 0000 0000 0005  f: 0000 0000 0000 0001  d: 0000 0000 0000 0DD8  s: 0000 0000 0000 0001
i: 0000 0000 0000 0006  f: 0000 0000 0000 0001  d: 0000 0000 0000 0027  s: 0000 0000 0000 0000
i: 0000 0000 0000 0007  f: 0000 0000 0000 0001  d: 0000 0000 0000 0D58  s: 0000 0000 0000 0001
i: 0000 0000 0000 0008  f: 0000 0000 0000 0001  d: 0000 0000 0000 0025  s: 0000 0000 0000 0000
i: 0000 0000 0000 0009  f: 0000 0000 0000 0001  d: 0000 0000 0000 0CD8  s: 0000 0000 0000 0001
i: 0000 0000 0000 000A  f: 0000 0000 0000 0001  d: 0000 0000 0000 0023  s: 0000 0000 0000 0000
i: 0000 0000 0000 000B  f: 0000 0000 0000 0001  d: 0000 0000 0000 0C58  s: 0000 0000 0000 0001
i: 0000 0000 0000 000C  f: 0000 0000 0000 0001  d: 0000 0000 0000 0021  s: 0000 0000 0000 0000
i: 0000 0000 0000 000D  f: 0000 0000 0000 0001  d: 0000 0000 0000 0BD8  s: 0000 0000 0000 0001
i: 0000 0000 0000 000E  f: 0000 0000 0000 0001  d: 0000 0000 0000 001F  s: 0000 0000 0000 0000
i: 0000 0000 0000 000F  f: 0000 0000 0000 0001  d: 0000 0000 0000 0B58  s: 0000 0000 0000 0001
i: 0000 0000 0000 0010  f: 0000 0000 0000 0001  d: 0000 0000 0000 001D  s: 0000 0000 0000 0000
i: 0000 0000 0000 0011  f: 0000 0000 0000 0001  d: 0000 0000 0000 0AD8  s: 0000 0000 0000 0001
i: 0000 0000 0000 0012  f: 0000 0000 0000 0001  d: 0000 0000 0000 001B  s: 0000 0000 0000 0000
i: 0000 0000 0000 0013  f: 0000 0000 0000 0001  d: 0000 0000 0000 0998  s: 0000 0000 0000 0001
i: 0000 0000 0000 0014  f: 0000 0000 0000 0001  d: 0000 0000 0000 0019  s: 0000 0000 0000 0000
i: 0000 0000 0000 0015  f: 0000 0000 0000 0001  d: 0000 0000 0000 0918  s: 0000 0000 0000 0001
i: 0000 0000 0000 0016  f: 0000 0000 0000 0001  d: 0000 0000 0000 0017  s: 0000 0000 0000 0000
i: 0000 0000 0000 0017  f: 0000 0000 0000 0001  d: 0000 0000 0000 0898  s: 0000 0000 0000 0001
i: 0000 0000 0000 0018  f: 0000 0000 0000 0001  d: 0000 0000 0000 0015  s: 0000 0000 0000 0000
i: 0000 0000 0000 0019  f: 0000 0000 0000 0001  d: 0000 0000 0000 0818  s: 0000 0000 0000 0001
i: 0000 0000 0000 001A  f: 0000 0000 0000 0001  d: 0000 0000 0000 0013  s: 0000 0000 0000 0000
i: 0000 0000 0000 001B  f: 0000 0000 0000 0001  d: 0000 0000 0000 06D8  s: 0000 0000 0000 0001
i: 0000 0000 0000 001C  f: 0000 0000 0000 0001  d: 0000 0000 0000 0011  s: 0000 0000 0000 0000
i: 0000 0000 0000 001D  f: 0000 0000 0000 0001  d: 0000 0000 0000 0658  s: 0000 0000 0000 0001
i: 0000 0000 0000 001E  f: 0000 0000 0000 0001  d: 0000 0000 0000 000F  s: 0000 0000 0000 0000
i: 0000 0000 0000 001F  f: 0000 0000 0000 0001  d: 0000 0000 0000 05D8  s: 0000 0000 0000 0001
i: 0000 0000 0000 0020  f: 0000 0000 0000 0001  d: 0000 0000 0000 000D  s: 0000 0000 0000 0000
i: 0000 0000 0000 0021  f: 0000 0000 0000 0001  d: 0000 0000 0000 0398  s: 0000 0000 0000 0001
i: 0000 0000 0000 0022  f: 0000 0000 0000 0001  d: 0000 0000 0000 000B  s: 0000 0000 0000 0000
i: 0000 0000 0000 0023  f: 0000 0000 0000 0001  d: 0000 0000 0000 0318  s: 0000 0000 0000 0001
i: 0000 0000 0000 0024  f: 0000 0000 0000 0001  d: 0000 0000 0000 0009  s: 0000 0000 0000 0000
i: 0000 0000 0000 0025  f: 0000 0000 0000 0001  d: 0000 0000 0000 0298  s: 0000 0000 0000 0001
i: 0000 0000 0000 0026  f: 0000 0000 0000 0001  d: 0000 0000 0000 0007  s: 0000 0000 0000 0000
i: 0000 0000 0000 0027  f: 0000 0000 0000 0001  d: 0000 0000 0000 0218  s: 0000 0000 0000 0001
i: 0000 0000 0000 0028  f: 0000 0000 0000 0001  d: 0000 0000 0000 0005  s: 0000 0000 0000 0000
i: 0000 0000 0000 0029  f: 0000 0000 0000 0001  d: 0000 0000 0000 0198  s: 0000 0000 0000 0001
i: 0000 0000 0000 002A  f: 0000 0000 0000 0001  d: 0000 0000 0000 0003  s: 0000 0000 0000 0000
i: 0000 0000 0000 002B  f: 0000 0000 0000 0001  d: 0000 0000 0000 0118  s: 0000 0000 0000 0001
i: 0000 0000 0000 002C  f: 0000 0000 0000 0001  d: 0000 0000 0000 0001  s: 0000 0000 0000 0000
i: 0000 0000 0000 002D  f: 0000 0000 0000 0001  d: 0000 0000 0000 0098  s: 0000 0000 0000 0001
i: 0000 0000 0000 002E  f: 0000 0000 0000 0000  d: 0000 0000 0000 0000  s: 0000 0000 0000 0000
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::insertTree
  my $b = CreateArena;
  my $t = $b->CreateTree;
  my $T = $b->CreateTree;

  $T->insert    (K(key, 2), K(data, 4));
  $t->insertTree(K(key, 1), $T);

  $t->print;

  ok Assemble(debug => 0, eq => <<END);
Tree at:    r15: 0000 0000 0000 0018
key: 0000 0000 0000 0001 data: 0000 0000 0000 0098 depth: 0000 0000 0000 0001
Tree at:    r15: 0000 0000 0000 0098
key: 0000 0000 0000 0002 data: 0000 0000 0000 0004 depth: 0000 0000 0000 0001
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::print
  my $L = V(loop, 45);
  my $b = CreateArena;
  my $t = $b->CreateTree;

  $L->for(sub
   {my ($i, $start, $next, $end) = @_;
    my $l = $L - $i;
    If ($i % 2 == 0, sub
     {$t->insert($i, $l);
      $t->insertTree($l);
     });
   });

  $t->print;

  ok Assemble(debug => 0, eq => <<END);
Tree at:    r15: 0000 0000 0000 0018
key: 0000 0000 0000 0000 data: 0000 0000 0000 002D depth: 0000 0000 0000 0002
key: 0000 0000 0000 0001 data: 0000 0000 0000 0ED8 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0002 data: 0000 0000 0000 002B depth: 0000 0000 0000 0002
key: 0000 0000 0000 0003 data: 0000 0000 0000 0E58 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0004 data: 0000 0000 0000 0029 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0005 data: 0000 0000 0000 0DD8 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0006 data: 0000 0000 0000 0027 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0007 data: 0000 0000 0000 0D58 depth: 0000 0000 0000 0001
key: 0000 0000 0000 0008 data: 0000 0000 0000 0025 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0009 data: 0000 0000 0000 0CD8 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000A data: 0000 0000 0000 0023 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000B data: 0000 0000 0000 0C58 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000C data: 0000 0000 0000 0021 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000D data: 0000 0000 0000 0BD8 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000E data: 0000 0000 0000 001F depth: 0000 0000 0000 0001
key: 0000 0000 0000 000F data: 0000 0000 0000 0B58 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0010 data: 0000 0000 0000 001D depth: 0000 0000 0000 0002
key: 0000 0000 0000 0011 data: 0000 0000 0000 0AD8 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0012 data: 0000 0000 0000 001B depth: 0000 0000 0000 0002
key: 0000 0000 0000 0013 data: 0000 0000 0000 0998 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0014 data: 0000 0000 0000 0019 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0015 data: 0000 0000 0000 0918 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0016 data: 0000 0000 0000 0017 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0017 data: 0000 0000 0000 0898 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0018 data: 0000 0000 0000 0015 depth: 0000 0000 0000 0001
key: 0000 0000 0000 0019 data: 0000 0000 0000 0818 depth: 0000 0000 0000 0002
key: 0000 0000 0000 001A data: 0000 0000 0000 0013 depth: 0000 0000 0000 0002
key: 0000 0000 0000 001B data: 0000 0000 0000 06D8 depth: 0000 0000 0000 0002
key: 0000 0000 0000 001C data: 0000 0000 0000 0011 depth: 0000 0000 0000 0002
key: 0000 0000 0000 001D data: 0000 0000 0000 0658 depth: 0000 0000 0000 0002
key: 0000 0000 0000 001E data: 0000 0000 0000 000F depth: 0000 0000 0000 0002
key: 0000 0000 0000 001F data: 0000 0000 0000 05D8 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0020 data: 0000 0000 0000 000D depth: 0000 0000 0000 0002
key: 0000 0000 0000 0021 data: 0000 0000 0000 0398 depth: 0000 0000 0000 0001
key: 0000 0000 0000 0022 data: 0000 0000 0000 000B depth: 0000 0000 0000 0002
key: 0000 0000 0000 0023 data: 0000 0000 0000 0318 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0024 data: 0000 0000 0000 0009 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0025 data: 0000 0000 0000 0298 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0026 data: 0000 0000 0000 0007 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0027 data: 0000 0000 0000 0218 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0028 data: 0000 0000 0000 0005 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0029 data: 0000 0000 0000 0198 depth: 0000 0000 0000 0002
key: 0000 0000 0000 002A data: 0000 0000 0000 0003 depth: 0000 0000 0000 0002
key: 0000 0000 0000 002B data: 0000 0000 0000 0118 depth: 0000 0000 0000 0002
key: 0000 0000 0000 002C data: 0000 0000 0000 0001 depth: 0000 0000 0000 0002
key: 0000 0000 0000 002D data: 0000 0000 0000 0098 depth: 0000 0000 0000 0002
Tree at:    r15: 0000 0000 0000 0098
Tree at:    r15: 0000 0000 0000 0118
Tree at:    r15: 0000 0000 0000 0198
Tree at:    r15: 0000 0000 0000 0218
Tree at:    r15: 0000 0000 0000 0298
Tree at:    r15: 0000 0000 0000 0318
Tree at:    r15: 0000 0000 0000 0398
Tree at:    r15: 0000 0000 0000 05D8
Tree at:    r15: 0000 0000 0000 0658
Tree at:    r15: 0000 0000 0000 06D8
Tree at:    r15: 0000 0000 0000 0818
Tree at:    r15: 0000 0000 0000 0898
Tree at:    r15: 0000 0000 0000 0918
Tree at:    r15: 0000 0000 0000 0998
Tree at:    r15: 0000 0000 0000 0AD8
Tree at:    r15: 0000 0000 0000 0B58
Tree at:    r15: 0000 0000 0000 0BD8
Tree at:    r15: 0000 0000 0000 0C58
Tree at:    r15: 0000 0000 0000 0CD8
Tree at:    r15: 0000 0000 0000 0D58
Tree at:    r15: 0000 0000 0000 0DD8
Tree at:    r15: 0000 0000 0000 0E58
Tree at:    r15: 0000 0000 0000 0ED8
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::insertTreeAndClone #TNasm::X86::Tree::Clone  #TNasm::X86::Tree::findAndClone
  my $L = K(loop, 4);
  my $b = CreateArena;
  my $T = $b->CreateTree;
  my $t = $T->Clone;

  $L->for(sub
   {my ($i, $start, $next, $end) = @_;
    $t->insertTreeAndClone($i);
    $t->first->outNL;
   });

  $t->insert($L, $L*2);

  my $f = $T->Clone;
  $L->for(sub
   {my ($i, $start, $next, $end) = @_;
    $f->findAndClone($i);
    $i->out('i: '); $f->found->out('  f: '); $f->data->out('  d: '); $f->subTree->outNL('  s: ');
   });
  $f->find($L);
  $L->out('N: '); $f->found->out('  f: '); $f->data->out('  d: ');   $f->subTree->outNL('  s: ');

  ok Assemble(debug => 0, eq => <<END);
first: 0000 0000 0000 0098
first: 0000 0000 0000 0118
first: 0000 0000 0000 0198
first: 0000 0000 0000 0218
i: 0000 0000 0000 0000  f: 0000 0000 0000 0001  d: 0000 0000 0000 0098  s: 0000 0000 0000 0001
i: 0000 0000 0000 0001  f: 0000 0000 0000 0001  d: 0000 0000 0000 0118  s: 0000 0000 0000 0001
i: 0000 0000 0000 0002  f: 0000 0000 0000 0001  d: 0000 0000 0000 0198  s: 0000 0000 0000 0001
i: 0000 0000 0000 0003  f: 0000 0000 0000 0001  d: 0000 0000 0000 0218  s: 0000 0000 0000 0001
N: 0000 0000 0000 0004  f: 0000 0000 0000 0001  d: 0000 0000 0000 0008  s: 0000 0000 0000 0000
END
 }

#latest:
if (0) {
  is_deeply Assemble(debug=>1), <<END;
END
 }

ok 1 for 3..42;

unlink $_ for qw(hash print2 sde-log.txt sde-ptr-check.out.txt z.txt);          # Remove incidental files

say STDERR sprintf("Finished in %.2fs, bytes assembled: %d ",  time - $start, totalBytesAssembled);
