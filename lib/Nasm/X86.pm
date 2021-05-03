#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I. -I/home/phil/perl/cpan/AsmC/lib/
#-------------------------------------------------------------------------------
# Generate Nasm X86 code from Perl.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation
# Labels should be settable via $label->set
# Register expressions via op overloading - register size and ability to add offsets, peek, pop, push clear register
# Indent opcodes by call depth, - replace push @text with a method call
package Nasm::X86;
our $VERSION = "20210419";
use warnings FATAL => qw(all);
use strict;
use Carp qw(confess cluck);
use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use Asm::C qw(:all);
use feature qw(say current_sub);

my $develop = -e q(/home/phil/);                                                # Developing
my $sde     = q(/var/isde/sde64);                                               # Intel emulator
   $sde     = q(sde/sde64) unless $develop;                                     # Intel emulator on GitHub
my $totalBytesAssembled = 0;                                                    # Estimate the size of the output programs

binModeAllUtf8;

my %rodata;                                                                     # Read only data already written
my %rodatas;                                                                    # Read only string already written
my %subroutines;                                                                # Subroutines generated
my @rodata;                                                                     # Read only data
my @data;                                                                       # Data
my @bss;                                                                        # Block started by symbol
my @text;                                                                       # Code

my $sysin  = 0;                                                                 # File descriptor for standard input
my $sysout = 1;                                                                 # File descriptor for standard output
my $syserr = 2;                                                                 # File descriptor for standard error

BEGIN{
  my %r = (    map {$_=>[ 8,  '8'  ]}  qw(al bl cl dl r8b r9b r10b r11b r12b r13b r14b r15b sil dil spl bpl ah bh ch dh));
     %r = (%r, map {$_=>[16,  's'  ]}  qw(cs ds es fs gs ss));
     %r = (%r, map {$_=>[16,  '16' ]}  qw(ax bx cx dx r8w r9w r10w r11w r12w r13w r14w r15w si di sp bp));
     %r = (%r, map {$_=>[32,  '32a']}  qw(eax  ebx ecx edx esi edi esp ebp));
     %r = (%r, map {$_=>[32,  '32b']}  qw(r8d r8l r9d r9l r10d r10l r11d r11l r12d r12l r13d r13l r14d r14l r15d r15l));
     %r = (%r, map {$_=>[80,  'f'  ]}  qw(st0 st1 st2 st3 st4 st5 st6 st7));
     %r = (%r, map {$_=>[64,  '64' ]}  qw(rax rbx rcx rdx r8 r9 r10 r11 r12 r13 r14 r15 rsi rdi rsp rbp rip rflags));
     %r = (%r, map {$_=>[64,  '64m']}  qw(mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7));
     %r = (%r, map {$_=>[128, '128']}  qw(xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm30 xmm31));
     %r = (%r, map {$_=>[256, '256']}  qw(ymm0 ymm1 ymm2 ymm3 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm30 ymm31));
     %r = (%r, map {$_=>[512, '512']}  qw(zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm30 zmm31));
     %r = (%r, map {$_=>[64,  'm'  ]}  qw(k0 k1 k2 k3 k4 k5 k6 k7));

  my @i0 = qw(popfq pushfq rdtsc ret syscall);                                  # Zero operand instructions

  my @i1 = split /\s+/, <<END;                                                  # Single operand instructions
bswap call dec inc jmp ja jae jb jbe jc jcxz je jecxz jg jge jl jle
jna jnae jnb jnbe jnc jne jng jnge jnl jnle jno jnp jns jnz jo jp jpe jpo jrcxz
js jz not seta setae setb setbe setc sete setg setge setl setle setna setnae
setnb setnbe setnc setne setng setnge setnl setno setnp setns setnz seto setp
setpe setpo sets setz pop push
END

  my @i2 =  split /\s+/, <<END;                                                 # Double operand instructions
add and bt btc btr bts
cmova cmovae cmovb cmovbe cmovc cmove cmovg cmovge cmovl cmovle
cmovna cmovnae cmovnb cmp
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
vpinsrb vpinsrd vpinsrw vpinsrq
vgetmantps
vaddd
vmulpd vaddpd
END

  my @i3qdwb =  split /\s+/, <<END;                                             # Triple operand instructions which have qdwb versions
pinsr pextr
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
sub PeekR($);                                                                   # Peek at the register on top of the stack
sub PopR(@);                                                                    # Pop a list of registers off the stack
sub PrintOutMemory;                                                             # Print the memory addressed by rax for a length of rdi
sub PrintOutRegisterInHex(@);                                                   # Print any register as a hex string
sub PushR(@);
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

my @syscallSequence = qw(rax rdi rsi rdx r10 r8 r9);                            # The parameter list sequence for system calls

sub SaveFirstFour()                                                             # Save the first 4 parameter registers
 {my $N = 4;
  Push $_ for @syscallSequence[0..$N-1];
  $N * &RegisterSize(rax);                                                      # Space occupied by push
 }

sub RestoreFirstFour()                                                          # Restore the first 4 parameter registers
 {my $N = 4;
  Pop $_ for reverse @syscallSequence[0..$N-1];
 }

sub RestoreFirstFourExceptRax()                                                 # Restore the first 4 parameter registers except rax so it can return its value
 {my $N = 4;
  Pop $_ for reverse @syscallSequence[1..$N-1];
  Add rsp, 1*RegisterSize(rax);
 }

sub RestoreFirstFourExceptRaxAndRdi()                                           # Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values
 {my $N = 4;
  Pop $_ for reverse @syscallSequence[2..$N-1];
  Add rsp, 2*RegisterSize(rax);
 }

sub SaveFirstSeven()                                                            # Save the first 7 parameter registers
 {my $N = 7;
  Push $_ for @syscallSequence[0..$N-1];
  $N * 1*RegisterSize(rax);                                                       # Space occupied by push
 }

sub RestoreFirstSeven()                                                         # Restore the first 7 parameter registers
 {my $N = 7;
  Pop $_ for reverse @syscallSequence[0..$N-1];
 }

sub RestoreFirstSevenExceptRax()                                                # Restore the first 7 parameter registers except rax which is being used to return the result
 {my $N = 7;
  Pop $_ for reverse @syscallSequence[1..$N-1];
  Add rsp, 1*RegisterSize(rax);
 }

sub RestoreFirstSevenExceptRaxAndRdi()                                          # Restore the first 7 parameter registers except rax and rdi which are being used to return the results
 {my $N = 7;
  Pop $_ for reverse @syscallSequence[2..$N-1];
  Add rsp, 2*RegisterSize(rax);                                                 # Skip rdi and rax
 }

sub ReorderSyscallRegisters(@)                                                  # Map the list of registers provided to the 64 bit system call sequence
 {my (@registers) = @_;                                                         # Registers
  Push $_ for @syscallSequence[0..$#registers];
  Push $_ for reverse @registers;
  Pop  $_ for @syscallSequence[0..$#registers];
 }

sub UnReorderSyscallRegisters(@)                                                # Recover the initial values in registers that were reordered
 {my (@registers) = @_;                                                         # Registers
  Pop  $_ for reverse @syscallSequence[0..$#registers];
 }

my @xmmRegisters = map {"xmm$_"} 0..31;                                         # The xmm registers

sub ReorderXmmRegisters(@)                                                      # Map the list of xmm registers provided to 0-31
 {my (@registers) = map {"xmm$_"} @_;                                           # Registers
  my    @r = @xmmRegisters; $#r = $#registers;
  PushR @r, @registers;
  PopR  @r;
 }

sub UnReorderXmmRegisters(@)                                                    # Recover the initial values in the xmm registers that were reordered
 {my (@registers) = @_;                                                         # Registers
  my   @r = @xmmRegisters; $#r = $#registers;
  PopR @r;
 }

sub RegisterSize($)                                                             # Return the size of a register
 {my ($r) = @_;                                                                 # Register

  eval "${r}Size()";
 }

sub ClearRegisters(@)                                                           # Clear registers by setting them to zero
 {my (@registers) = @_;                                                         # Registers
  for my $r(@registers)
   {my $size = RegisterSize $r;
    Xor    $r, $r     if $size == 8 and $r !~ m(\Ak);
    Kxorq  $r, $r, $r if $size == 8 and $r =~ m(\Ak);
    Vpxorq $r, $r     if $size  > 8;
   }
 }

sub SetRegisterToMinusOne($)                                                    # Set the specified register to -1
 {my ($register) = @_;                                                          # Register to set
  @_ == 1 or confess;

  Xor $register, $register;
  Sub $register, 1;
 }

sub SetZF()                                                                     # Set the zero flag
 {Cmp rax, rax;
 }

sub ClearZF()                                                                   # Set the zero flag
 {Push rax;
  Mov rax, 1;
  Cmp rax, 0;
  Pop rax;
 }

sub InsertIntoXyz($$$;$)                                                        # Insert the specified word, double, quad from rax or the contents of xmm0 into the specified xyz register at the specified position shifting data above it to the left.
 {my ($reg, $unit, $pos, $maskRegister) = @_;                                   # Register to insert into, width of insert, position of insert in units from least significant byte starting at 0, optional mask register whose value can be sacrificed

  my $k = $maskRegister || k1;                                                  # Choose a mask register
  PushR k1 unless $maskRegister;                                                # Save mask register
  PushR $reg;                                                                   # Save register to be modified
  Kxnorq $k, $k, $k;                                                            # Mask to all ones
  Kshiftlq $k, $k, $pos * $unit;                                                # Zero mask data we are going to keep in position

  my $a = $unit == 2 ? q(ax) : $unit == 4 ? q(eax): $unit == 8 ? q(rax) : xmm0; # Source of inserted value
  my $u = $unit < 16 ? \&Mov : \&Vmovdqu8;                                      # Move instruction
  &$u("[rsp+$pos*$unit-$unit]", $a);                                            # Insert data into stack
  Vmovdqu8 "${reg}{$k}", "[rsp-$unit]";                                         # Reload data shifted over
  Add rsp, RegisterSize $reg;                                                   # Skip over target register on stack
  PopR $k unless $maskRegister;                                                 # Return mask register to its original state unless it can be sacrificed
 }

#D1 Structured Programming                                                      # Structured programming constructs

sub If(&;&)                                                                     # If
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  @_ >= 1 or confess;
  if (@_ == 1)                                                                  # No else
   {Comment "if then";
    my $end = Label;
    Jz $end;
    &$then;
    SetLabel $end;
   }
  else                                                                          # With else
   {Comment "if then else";
    my $endIf     = Label;
    my $startElse = Label;
    Jz $startElse;
    &$then;
    Jmp $endIf;
    SetLabel $startElse;
    &$else;
    SetLabel  $endIf;
   }
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
  If                                                                            # Non remainder
   {&$last;                                                                     # Process remainder
   }
 }

sub S(&%)                                                                       # Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub
 {my ($body, %options) = @_;                                                    # Body, options.
  @_ >= 1 or confess;
  my $name    = $options{name};                                                 # Optional name for subroutine reuse
  my $comment = $options{comment};                                              # Optional comment
  Comment "Subroutine " .($comment) if $comment;

  if ($name and my $n = $subroutines{$name}) {return $n}                        # Return the label of a pre-existing copy of the code

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

#D1 Print                                                                       # Print

sub PrintOutNL()                                                                # Print a new line to stdout
 {@_ == 0 or confess;
  my $a = Rb(10);
  Comment "Write new line";

  my $s = S                                                                     # Print new line
   {SaveFirstFour;
    Mov rax, 1;
    Mov rdi, 1;
    Mov rsi, $a;
    Mov rdx, 1;
    Syscall;
    RestoreFirstFour()
   } name => q(PrintOutNL);

  Call $s;
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
  Mov rdi, $sysout;
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
   {SaveFirstFour;
    Mov rdx, rax;                                                               # Content to be printed
    Mov rdi, 2;                                                                 # Length of a byte in hex
    for my $i(0..7)
     {my $s = 8*$i;
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

    my $sub = S                                                                 # Reverse rax
     {PrintOutString sprintf("%6s: ", $r);

      my sub printReg(@)                                                        # Print the contents of a register
       {my (@regs) = @_;                                                        # Size in bytes, work registers
        my $s = RegisterSize $r;                                                # Size of the register
        PushR @regs;                                                            # Save work registers
        PushR $r;                                                               # Place register contents on stack
        PopR  @regs;                                                            # Load work registers
        for my $i(keys @regs)                                                   # Print work registers to print input register
         {my $R = $regs[$i];
          if ($R !~ m(\Arax))
           {PrintOutString("  ");
            Mov rax, $R
           }
          PrintOutRaxInHex;                                                     # Print work register
          PrintOutString(" ") unless $i == $#regs;
         }
        PopR @regs;
       };
      if    ($r =~ m(\A[kr])) {printReg qw(rax)}                                # 64 bit register requested
      elsif ($r =~ m(\Ax))    {printReg qw(rax rbx)}                            # xmm*
      elsif ($r =~ m(\Ay))    {printReg qw(rax rbx rcx rdx)}                    # ymm*
      elsif ($r =~ m(\Az))    {printReg qw(rax rbx rcx rdx r8 r9 r10 r11)}      # zmm*

      PrintOutNL;
     } name => "PrintOutRegister${r}InHex";                                     # One routine per register printed

    Call $sub;
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
  If {PrintOutStringNL "ZF=0"} sub {PrintOutStringNL "ZF=1"};
  Popfq;
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
    Mov rax, 39;
    Syscall;
    Mov rdx, rax;                                                               # Content to be printed
    ClearRegisters rax;                                                         # Save a trailing 00 on the stack
    Push ax;
    for my $i(reverse 5..7)
     {my $s = 8*$i;
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

sub PushR(@)                                                                    # Push registers onto the stack
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

sub PopR(@)                                                                     # Pop registers from the stack
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
 {my ($field, $register) = @_;                                                  # Field, optional address register  else rax
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
  my $loc = $variable->loc;                                                     # Location of variable on stack
  "[$loc+rbp]"                                                                  # Address variable
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

  my $sub = S
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

  Call $sub;
 }

sub PrintOutMemoryInHexNL                                                       # Dump memory from the address in rax for the length in rdi and then print a new line
 {@_ == 0 or confess;
  Comment "Print out memory in hex then new line";
  PrintOutMemoryInHex;
  PrintOutNL;
 }

sub PrintOutMemory                                                              # Print the memory addressed by rax for a length of rdi
 {@_ == 0 or confess;

  my $sub = S
   {Comment "Print memory";
    SaveFirstFour;
    Mov rsi, rax;
    Mov rdx, rdi;
    Mov rax, 1;
    Mov rdi, $sysout;
    Syscall;
    RestoreFirstFour();
   } name => "PrintOutMemory";

  Call $sub;
 }

sub PrintOutMemoryNL                                                            # Print the memory addressed by rax for a length of rdi followed by a new line
 {@_ == 0 or confess;
  Comment "Print out memory then new line";
  PrintOutMemory;
  PrintOutNL;
 }

sub AllocateMemory                                                              # Allocate the amount of memory specified in rax via mmap and return the address of the allocated memory in rax
 {@_ == 0 or confess;
  Comment "Allocate memory";

  my $sub = S
   {SaveFirstSeven;
    my $d = extractMacroDefinitionsFromCHeaderFile "linux/mman.h";              # mmap constants
    my $pa = $$d{MAP_PRIVATE} | $$d{MAP_ANONYMOUS};
    my $wr = $$d{PROT_WRITE}  | $$d{PROT_READ};

    Mov rsi, rax;                                                               # Amount of memory
    Mov rax, 9;                                                                 # mmap
    Xor rdi, rdi;                                                               # Anywhere
    Mov rdx, $wr;                                                               # Read write protections
    Mov r10, $pa;                                                               # Private and anonymous map
    Mov r8,  -1;                                                                # File descriptor for file backing memory if any
    Mov r9,  0;                                                                 # Offset into file
    Syscall;
    RestoreFirstSevenExceptRax;
   } name=> "AllocateMemory";

  Call $sub;
 }

sub FreeMemory                                                                  # Free memory via munmap. The address of the memory is in rax, the length to free is in rdi
 {@_ == 0 or confess;
  Comment "Free memory";

  my $sub = S
   {SaveFirstFour;
    Mov rsi, rdi;
    Mov rdi, rax;
    Mov rax, 11;
    Syscall;
    RestoreFirstFourExceptRax;
   } name=> "FreeMemory";

  Call $sub;
 }

sub ClearMemory()                                                               # Clear memory - the address of the memory is in rax, the length in rdi
 {@_ == 0 or confess;
  Comment "Clear memory";

  my $size = RegisterSize zmm0;

  my $sub = S
   {SaveFirstFour;
    PushR zmm0;                                                                   # Pump zeros with this register
    Lea rdi, "[rax+rdi-$size]";                                                   # Address of upper limit of buffer
    ClearRegisters zmm0;                                                          # Clear the register that will be written into memory

    For                                                                           # Clear memory
     {Vmovdqu64 "[rax]", zmm0;
     } rax, rdi, RegisterSize zmm0;

    PopR zmm0;
    RestoreFirstFour;
   } name=> "ClearMemory";

  Call $sub;
 }

sub CopyMemory()                                                                # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
 {@_ == 0 or confess;
  Comment "Copy memory";
  my $source   = rsi;
  my $target   = rax;
  my $length   = rdi;
  my $copied   = rdx;
  my $transfer = r8;
  SaveFirstSeven;
  ClearRegisters $copied;

  For                                                                           # Clear memory
   {Mov "r8b", "[$source+$copied]";
    Mov "[$target+$copied]", "r8b";
   } $copied, $length, 1;

  RestoreFirstSeven;
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
    Mov rdi,16;
    Mov rdi, rax;
    Mov rax, 2;
    Mov rsi, $write;
    ClearRegisters rdx;
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
    SaveFirstFour;
    Mov rdi, rax;                                                               # File name
    Mov rax,4;
    Lea rsi, "[rsp-$Size]";
    Syscall;
    Mov rax, "[$off+rsp-$Size]";                                                # Place size in rax
    RestoreFirstFourExceptRax;
   } name=> "StatSize";

  Call $sub;
 }

sub ReadFile()                                                                  # Read a file whose name is addressed by rax into memory.  The address of the mapped memory and its length are returned in registers rax,rdi
 {@_ == 0 or confess;

  my $sub = S                                                                   # Read file
   {Comment "Read a file into memory";

    SaveFirstSeven;                                                             # Generated code
    my ($local, $file, $addr, $size, $fdes) = AllocateAll8OnStack 4;            # Local data

    Mov $file, rax;                                                             # Save file name

    StatSize;                                                                   # File size
    Mov $size, rax;                                                             # Save file size

    Mov rax, $file;                                                             # File name
    OpenRead;                                                                   # Open file for read
    Mov $fdes, rax;                                                             # Save file descriptor

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
   } name=> "ReadFile";

  Call $sub;
 }

#D1 Short Strings                                                               # Operations on Short Strings

sub LoadShortStringFromMemoryToZmm($)                                           # Load the short string addressed by rax into the zmm register with the specified number
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

sub LengthOfShortString($$)                                                     # Place the length of the short string held in the numbered zmm register into the specified register
 {my ($reg, $zmm) = @_;                                                         # Register to hold length, number of zmm register containing string
  @_ == 2 or confess;
  Pextrb $reg, "xmm${zmm}", 0;                                                  # Length
 }

sub ConcatenateShortStrings($$)                                                 # Concatenate the right hand short string held in the numbered zmm register to the left hand short string held in the numbered zmm register
 {my ($left, $right) = @_;                                                      # Target zmm register to load, left hand short string, right short string
  @_ == 2 or confess;

  my $sub = S                                                                   # Read file
   {Comment "Concatenate the short string in zmm$right to the short string in zmm$left";
    LengthOfShortString r15, $right;                                            # Right length
    Mov   r14, -1;                                                              # Expand mask
    Bzhi  r14, r14, r15;                                                        # Skip bits for left
    LengthOfShortString rcx, $left;                                             # Left length
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
   } name=> "ConcatenateShortStrings${left}and${right}";

  Call $sub;
 }

#D1 Hash functions                                                              # Hash functions

sub Hash()                                                                      # Hash a string addressed by rax with length held in rdi and return the hash code in r15
 {@_ == 0 or confess;

  my $sub = S                                                                   # Read file
   {Comment "Hash";

    PushR my @regs = (rax, rdi, k1, zmm0, zmm1);                                # Save registers
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

      Vcvtudq2pd zmm1, ymm1;                                                    # Convert to float
      Vgetmantps   zmm0, zmm0, 4;                                               # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

      Vmulpd zmm0, zmm1, zmm0;                                                  # Multiply current hash by data
     }, rax, rdi, RegisterSize ymm0;

    Vgetmantps   zmm0, zmm0, 4;                                                 # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

    Mov r15, 0b11110000;                                                        # Top 4 to bottom 4
    Kmovq k1, r15;
    Vpcompressq  "zmm1{k1}", zmm0;
    Vaddpd       ymm0, ymm0, ymm1;                                              # Top 4 plus bottom 4

    Mov r15, 0b1100;                                                            # Top 2 to bottom 2
    Kmovq k1, r15;
    Vpcompressq  "ymm1{k1}", ymm0;
    Vaddpd       xmm0, xmm0, xmm1;                                              # Top 2 plus bottom 2

    Pslldq       xmm0, 2;                                                       # Move centers into double words
    Psrldq       xmm0, 4;
    Mov r15, 0b0101;                                                            # Centers to lower quad
    Kmovq k1, r15;
    Vpcompressd  "xmm0{k1}", xmm0;                                              # Compress to lower quad

    Vmovq r15, xmm0;                                                            # Result in r15

    PopR @regs;
   } name=> "Hash";

  Call $sub;
 }

#D1 Long Strings                                                                # Operations on Long Strings

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
    Mov r15, rcx;
    Not r15;
    Dec r15;
    PopR @regs;
   } name=> "Cstrlen";

  Call $sub;
 }

sub CreateByteString()                                                          # Create an relocatable string of bytes in an arena and returns its address in rax
 {@_ == 0 or confess;
  Comment "Create byte string";
  my $N = 4096;                                                                 # Initial size of string

  my ($string, $size, $used) = All8Structure 2;                                 # String base
  my $data = $string->field(0, "start of data");                                # Start of data

  my $sub  = S                                                                  # Create byte string
   {SaveFirstFour;
    Mov rax, $N;
    AllocateMemory;
    ClearRegisters   rdi;
    Mov $used->addr, rdi;
    Mov rdi, $N;
    Mov $size->addr, rdi;

    RestoreFirstFourExceptRax;
   } name=> "CreateByteString";

  Call $sub;

  genHash("ByteString",                                                         # Definition of byte string
    structure => $string,                                                       # Structure details
    size      => $size,                                                         # Size field details
    used      => $used,                                                         # Used field details
    data      => $data,                                                         # The first 8 bytes of the data
   );
 }

sub ByteString::updateSpace($)                                                  #P Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi
 {my ($byteString) = @_;                                                        # Byte string descriptor
  my $size = $byteString->size->addr;
  my $used = $byteString->used->addr;

  my $sub = S                                                                   # Read file
   {Comment "Allocate more space for a byte string";
    SaveFirstFour;
    Mov rdx, $used;                                                             # Used
    Add rdx, rdi;                                                               # Wanted
    Cmp rdx, $size;                                                             # Space needed versus actual size

    Jle (my $l = Label);
      Mov rsi, rax;                                                             # Old byte string
      Mov rdi, $size;                                                           # Old byte string size
      Mov rax, rdi;                                                             # Old byte string length

      my $double = SetLabel Label;                                              # Keep doubling until we have a string area that is big enough to hold the new data
        Shl rax, 1;                                                             # New byte string size - double the size of the old byte string
        Cmp rax, rdx;                                                           # Big enough ?
      Jl $double;                                                               # Still too low

      Mov rdx, rax;                                                             # New byte string size
      AllocateMemory;                                                           # Create new byte string
      CopyMemory;                                                               # Copy old byte string into new byte string
      Mov $size, rdx;                                                           # rdx can be reused now we have saved the size of the new bye string

      Push rax;                                                                 # Free old byte string
      Mov rax, rsi;                                                             # Old byte string
      FreeMemory;
      Pop rax;
    SetLabel $l;                                                                # Exit

    RestoreFirstFourExceptRax;                                                  # Return new byte string
   } name=> "ByteString::updateSpace";

  Call $sub;
 }

sub ByteString::makeReadOnly($)                                                 # Make a byte string read only
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Read file
   {Comment "Make a byte string readable";
    SaveFirstFour;
    Mov rdi, rax;                                                               # Address of byte string
    Mov rsi, $byteString->size->addr;                                           # Size of byte string
    Mov rdx, 1;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded byte string
   } name=> "ByteString::makeReadOnly";

  Call $sub;
 }

sub ByteString::makeWriteable($)                                                 # Make a byte string writable
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Read file
   {Comment "Make a  byte string writable";
    SaveFirstFour;
    Mov rdi, rax;                                                               # Address of byte string
    Mov rsi, $byteString->size->addr;                                           # Size of byte string
    Mov rdx, 3;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded byte string
   } name=> "ByteString::makeWriteable";

  Call $sub;
 }

sub ByteString::allocate($)                                                     # Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi
 {my ($byteString) = @_;                                                        # Byte string descriptor
  my $used   = rdx;                                                             # Register used to calculate how much of the byte string has been used
  my $offset = rsi;                                                             # Register used to hold current offset

  my $sub = S                                                                   # Read file
   {Comment "Allocate space in a byte string";
    $byteString->updateSpace;                                                   # Update space if needed
    SaveFirstFour;
    Mov $used, $byteString->used->addr;                                         # Currently used
    Mov $offset, $used;                                                         # Current offset
    Add $used, rdi;                                                             # Add the requested length to get the amount now used
    Mov $byteString->used->addr, $used;
    Mov rdi, $offset;
    Add rdi, $byteString->structure->size;                                      # This is the offset from the start of the byte string - which means that it will never be less than 16
    RestoreFirstFourExceptRaxAndRdi;                                            # Return the possibly expanded byte string
   } name=> "ByteString::allocate";

  Call $sub;
 }

sub ByteString::m($)                                                            # Append the content with length rdi addressed by rsi to the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor
  my $used = $byteString->used->addr;
  my $target = rdx;                                                             # Register that addresses target of move
  my $length = rdx;                                                             # Register used to update used field

  my $sub = S                                                                   # Read file
   {Comment "Append memory to a byte string";
    $byteString->updateSpace;                                                   # Update space if needed
    SaveFirstFour;
    Lea $target, $byteString->data->addr;                                       # Address of data field
    Add $target, $used;                                                         # Skip over used data

    PushR rax;                                                                  # Save address of byte string
    Mov rax, $target;                                                           # Address target
    CopyMemory;                                                                 # Move data in
    PopR rax;                                                                   # Restore address of byte string

    Mov $length, $used;                                                         # Update used field
    Add $length, rdi;
    Mov $used,   $length;

    RestoreFirstFourExceptRax;                                                  # Return the possibly expanded byte string
   } name=> "ByteString::m";

  Call $sub;
 }

sub ByteString::q($$)                                                           # Append a quoted string == a constant to the byte string addressed by rax
 {my ($byteString, $const) = @_;                                                # Byte string descriptor, constant
  SaveFirstFour;
  Mov rsi, Rs($const);                                                          # Constant
  Mov rdi, length($const);
  $byteString->m;                                                               # Move data
  RestoreFirstFourExceptRax;                                                    # Return the possibly expanded byte string
 }

sub ByteString::ql($$)                                                          # Append a quoted string containing new line characters to the byte string addressed by rax
 {my ($byteString, $const) = @_;                                                # Byte string descriptor, constant
  my @l = split /\s*\n/, $const;
  for my $l(@l)
   {$byteString->q($l);
    $byteString->nl;
   }
 }

sub ByteString::char($$)                                                        # Append a character expressed as a decimal number to the byte string addressed by rax
 {my ($byteString, $char) = @_;                                                 # Byte string descriptor, decimal number of character to be appended
  SaveFirstFour;
  Mov rdx, $char;                                                               # New line
  Push rdx;                                                                     # Put the character on the stack
  Mov rdi, 1;
  Mov rsi, rsp;
  $byteString->m;                                                               # Move data
  Pop rdx;                                                                      # Skip character on the stack
  RestoreFirstFourExceptRax;                                                    # Return the possibly expanded byte string
 }

sub ByteString::nl($)                                                           # Append a new line to the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor
  $byteString->char(ord("\n"));
 }

sub ByteString::z($)                                                            # Append a trailing zero to the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor
  $byteString->char(0);
 }

sub ByteString::rdiInHex                                                        # Add the content of register rdi in hexadecimal in big endian notation to a byte string
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Address conversion routine
   {Comment "Rdi in hex into byte string";
    my $hexTranslateTable = hexTranslateTable;
    my $value =  r8;
    my $hex   =  r9;
    my $byte  = r10;
    my $size  = RegisterSize rax;

    SaveFirstSeven;
    Mov $value, rdi;                                                            # Content to be printed
    Mov rdi, 2;                                                                 # Length of a byte in hex
    for my $i(0..7)                                                             # Each byte in rdi
     {Mov $byte, $value;
      Shl $byte, 8 *  $i;                                                       # Push selected byte high
      Shr $byte, 8 * ($size - 1);                                               # Push select byte low
      Shl $byte, 1;                                                             # Multiply by two because each entry in the translation table is two bytes long
      Lea rsi, "[$hexTranslateTable+$byte]";
      $byteString->m;
     }
    RestoreFirstSeven;
   } name => "ByteString::rdiInHex";

  Call $sub;
 }

sub ByteString::copy($)                                                         # Append the byte string addressed by rdi to the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Copy byte string
   {Comment "Rdi in hex into byte string";
    SaveFirstFour;
    Mov rdx, rdi;                                                               # Address byte string to be copied
    Mov rdi, $byteString->used->addr(rdx);
    Lea rsi, $byteString->data->addr(rdx);
    $byteString->m;                                                             # Move data
    RestoreFirstFourExceptRax;                                                  # Return the possibly expanded byte string
   } name => "ByteString::rdiInHex";

  Call $sub;
 }

sub ByteString::clear($)                                                        # Clear the byte string addressed by rax
 {my ($byteString) = @_;                                                        # Byte string descriptor

  PushR          rdi;
  ClearRegisters rdi;
  Mov $byteString->used->addr, rdi;
  PopR           rdi;
 }

sub ByteString::write($)                                                        # Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file
 {my ($byteString) = @_;                                                        # Byte string descriptor
  my $FileNameSize = 12;                                                        # Size of the file name

  my $sub = S                                                                   # Copy byte string
   {Comment "Write a byte string to a temporary file";
    SaveFirstSeven;

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
        Mov rax, "0x$x";
        Push ax;
       }
     }

    Mov rax, rsp;                                                               # Address file name
    OpenWrite;                                                                  # Create a temporary file
    Mov $file, rax;                                                             # File descriptor

    Mov rax, 1;                                                                 # Write content to file
    Mov rdi, $file;
    Lea rsi, $byteString->data->addr($string);
    Mov rdx, $byteString->used->addr($string);
    Syscall;
    Mov rax, $string;                                                           # Clear string and add file name
    $byteString->clear;

    Mov rax, $string;                                                           # Put file name in byte string
    Mov rsi, rsp;
    Mov rdi, 1+$FileNameSize;                                                   # File name size plus one trailing zero
    $byteString->m;
    Add rsp, 2+$FileNameSize;                                                   # File name size plus two trailing zeros
    Mov rax, $file;
    CloseFile;
    RestoreFirstSeven;
   } name => "ByteString::write";

  Call $sub;
 }

sub ByteString::read($)                                                         # Read the file named in the byte string (terminated with a zero byte) addressed by rax and place it into the byte string after clearing the byte string to remove the file name contained therein.
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Copy byte string
   {Comment "Read a byte string";
    SaveFirstFour;
    Mov rdx, rax;                                                               # Save address of byte string
    Lea rax, $byteString->data->addr;                                           # Address file name with rax
    ReadFile;                                                                   # Read the file named by rax
    Mov rsi, rax;                                                               # Address of content in rax, length of content in rdi
    Mov rax, rdx;                                                               # Address of byte string
    $byteString->clear;                                                         # Remove file name in byte string
    $byteString->m;                                                             # Move data into byte string
    Push rax;                                                                   # We might have a new byte string by now
    Mov rax, rsi;                                                               # File data
    FreeMemory;                                                                 # Address of allocated memory in rax, length in rdi
    Pop rax;                                                                    # Address byte string
    RestoreFirstFourExceptRax;
   } name => "ByteString::read";

  Call $sub;
 }

sub ByteString::out($)                                                          # Print the specified byte string addressed by rax on sysout
 {my ($byteString) = @_;                                                        # Byte string descriptor
  SaveFirstFour;
  Mov rdi, $byteString->used->addr;                                             # Length to print
  Lea rax, $byteString->data->addr;                                             # Address of data field
  PrintOutMemory;
  RestoreFirstFour;
 }

sub ByteString::bash($)                                                         # Execute the file named in the byte string addressed by rax with bash
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Bash string
   {Comment "Execute a byte string via bash";
    SaveFirstFour;
    Mov rdx, rax;                                                               # Save byte string address
    Fork;                                                                       # Fork

    Test rax,rax;
    If                                                                          # Parent
     {WaitPid;
     }
    sub                                                                         # Child
     {Mov rax, rdx;                                                             # Restore address of byte string
      Lea rdi, $byteString->data->addr;
      Mov rsi, 0;
      Mov rdx, 0;
      Mov rax, 59;
      Syscall;
     };
    RestoreFirstFour;
   } name => "ByteString::bash";

  Call $sub;
 }

sub ByteString::unlink($)                                                       # Unlink the file named in the byte string addressed by rax with bash
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Bash string
   {Comment "Unlink a file named in a byte string";
    SaveFirstFour;
    Lea rdi, $byteString->data->addr;
    Mov rax, 87;
    Syscall;
    RestoreFirstFour;
   } name => "ByteString::unlink";

  Call $sub;
 }

sub ByteString::dump($)                                                         # Dump details of a byte string
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Bash string
   {Comment "Print details of a byte string";
    SaveFirstFour;
    PrintOutStringNL("Byte String");

    Push rax;                                                                   # Print size
    Mov rax, $byteString->size->addr;
    PrintOutString("  Size: ");
    PrintOutRaxInHex;
    PrintOutNL;
    Pop rax;

    Push rax;                                                                   # Print used
    Mov rax, $byteString->used->addr;
    PrintOutString("  Used: ");
    PrintOutRaxInHex;
    PrintOutNL;
    Pop rax;
    RestoreFirstFour;
   } name => "ByteString::dump";

  Call $sub;
 }

sub ByteString::allocBlock($)                                                   # Allocate a block to hold a zmm register in the byte string addressed by rax and return its address in r15.
 {my ($byteString) = @_;                                                        # Byte string descriptor

  my $sub = S                                                                   # Bash string
   {Comment "Allocate a zmm block in a byte string";
    PushR my @regs = (rax, rdi);                                                # Size of block
    Mov rdi, RegisterSize zmm0;                                                 # Size of allocation
    $byteString->allocate;
    Mov r15, rax;                                                               # Return allocation in r15
    PopR @regs;                                                                 # Restore
   } name => "ByteString::allocBlock";

  Call $sub;
 }

sub ByteString::getBlock($$;$)                                                  # Get the block addressed by the address register and load it into the numbered zmm register
 {my ($byteString, $zmm, $addressRegister) = @_;                                # Byte string descriptor, number of zmm register, optional address register - rax by default
  my $r = $addressRegister // q(rax);
  Vmovdqu64 "zmm$zmm", "[rax]";                                                 # Read from memory
 }

sub ByteString::putBlock($$;$)                                                  # Put the contents of the numbered zmm register into the memory addressed by rax
 {my ($byteString, $zmm, $addressRegister) = @_;                                # Byte string descriptor, number of zmm register, optional address register - rax by default
  my $r = $addressRegister // q(rax);
  Vmovdqu64 "[rax]", "zmm$zmm";                                                 # Write into memory
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
  PopR xmm0;                                                                    # Put result in xmm0
  PopR @regs;                                                                   # Restore stack

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
    If {SetZF} sub {ClearZF};
    RestoreFirstFour;
   };

  for my $d(qw(left right))                                                     # Insert left or right
   {my $s = <<'END';
    $arenaTree->insertXXXX = sub                                                # Insert the node addressed by xmm1 left under the node addressed by xmm0
     {@_ == 0 or confess;
      SaveFirstFour;                                                            # A check that we are in the same tree would be a good idea here.
      PushR xmm0;                                                               # Parse xmm0
      PopR rdi, rax;
      PushR xmm1;                                                               # Parse xmm0
      PopR rsi, rdx;
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
 {@bss = @data = @rodata = %rodata = %rodatas = %subroutines = @text = ();
  $Labels = 0;
 }

sub Exit(;$)                                                                    # Exit with the specified return code or zero if no return code supplied.  Assemble() automatically adds a call to Exit(0) if the last operation in the program is not a call to Exit.
 {my ($c) = @_;                                                                 # Return code
  if (@_ == 0 or $c == 0)
   {Comment "Exit code: 0";
    ClearRegisters rdi;
   }
  elsif (@_ == 1)
   {Comment "Exit code: $c";
    Mov rdi, $c;
   }
  Mov rax, 60;
  Syscall;
 }

sub Assemble(%)                                                                 # Assemble the generated code
 {my (%options) = @_;                                                           # Options
  Exit 0 unless @data > 4 and $data[-4] !~ m(Exit Code:);                       # Exit with code 0 if no other exit has been taken

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

  my $cmd  = qq(nasm -f elf64 -g -l $l -o $o $c && ld -o $e $o && chmod 744 $e);
  my $exec = qq($sde -ptr-check -- ./$e 2>&1);
     $cmd .= qq( && $exec) unless $k;

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
#d
#-------------------------------------------------------------------------------
# Export - eeee
#-------------------------------------------------------------------------------

use Exporter qw(import);

use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA          = qw(Exporter);
@EXPORT       = qw();
@EXPORT_OK    = qw(
 );
%EXPORT_TAGS = (all=>[@EXPORT, @EXPORT_OK]);

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

You will need the Intel Software Development Emulator and the Networkwide
Assembler installed on your test system.  For full details of how to do this
see: L<https://github.com/philiprbrenan/NasmX86/blob/main/.github/workflows/main.yml>

=head1 Description

Generate Nasm assembler code


Version "20210419".


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


=head1 Registers

Operations on registers

=head2 SaveFirstFour()

Save the first 4 parameter registers


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


=head2 RestoreFirstFour()

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


=head2 RestoreFirstFourExceptRax()

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


=head2 RestoreFirstFourExceptRaxAndRdi()

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


=head2 SaveFirstSeven()

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


=head2 RestoreFirstSeven()

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


=head2 RestoreFirstSevenExceptRax()

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


=head2 RestoreFirstSevenExceptRaxAndRdi()

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


=head2 ReorderSyscallRegisters(@registers)

Map the list of registers provided to the 64 bit system call sequence

     Parameter   Description
  1  @registers  Registers

B<Example:>


    Mov rax, 1;  Mov rdi, 2;  Mov rsi,  3;  Mov rdx,  4;
    Mov r8,  8;  Mov r9,  9;  Mov r10, 10;  Mov r11, 11;


    ReorderSyscallRegisters   r8,r9;                                              # Reorder the registers fof syscall  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;

    UnReorderSyscallRegisters r8,r9;                                              # Unreorder the registers to recover their original values
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;

    ok Assemble =~ m(rax:.*08.*rdi:.*9.*rax:.*1.*rdi:.*2.*)s;


=head2 UnReorderSyscallRegisters(@registers)

Recover the initial values in registers that were reordered

     Parameter   Description
  1  @registers  Registers

B<Example:>


    Mov rax, 1;  Mov rdi, 2;  Mov rsi,  3;  Mov rdx,  4;
    Mov r8,  8;  Mov r9,  9;  Mov r10, 10;  Mov r11, 11;

    ReorderSyscallRegisters   r8,r9;                                              # Reorder the registers fof syscall
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;


    UnReorderSyscallRegisters r8,r9;                                              # Unreorder the registers to recover their original values  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rdi;

    ok Assemble =~ m(rax:.*08.*rdi:.*9.*rax:.*1.*rdi:.*2.*)s;


=head2 ReorderXmmRegisters(@registers) = map {"xmm$_"} @_;)

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
      If {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushR xmm0;                                                                   # Dump underlying  byte string
    PopR rdi, rax;
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


=head2 UnReorderXmmRegisters(@registers)

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
      If {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushR xmm0;                                                                   # Dump underlying  byte string
    PopR rdi, rax;
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


=head2 RegisterSize($r)

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



=head2 ClearRegisters(@registers)

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


=head2 SetRegisterToMinusOne($register)

Set the specified register to -1

     Parameter  Description
  1  $register  Register to set

B<Example:>



    SetRegisterToMinusOne rax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    ok Assemble =~ m(rax: FFFF FFFF FFFF FFFF);


=head2 SetZF()

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


=head2 ClearZF()

Set the zero flag


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


=head2 InsertIntoXyz($reg, $unit, $pos, $maskRegister)

Insert the specified word, double, quad from rax or the contents of xmm0 into the specified xyz register at the specified position shifting data above it to the left.

     Parameter      Description
  1  $reg           Register to insert into
  2  $unit          Width of insert
  3  $pos           Position of insert in units from least significant byte starting at 0
  4  $maskRegister  Optional mask register whose value can be sacrificed

B<Example:>


    ClearRegisters rax;
    Bts rax, 14;
    Not rax;
    PrintOutRegisterInHex rax;
    PushR rax;
    PopR  k1;
    PrintOutRegisterInHex k1;
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

    my $s    = Rb 0..63;
    Vmovdqu8 xmm0,"[$s]";                                                         # Number each byte
    Vmovdqu8 ymm1,"[$s]";
    Vmovdqu8 zmm2,"[$s]";
    Vmovdqu8 zmm3,"[$s]";

    SetRegisterToMinusOne rax;                                                    # Insert some ones

    InsertIntoXyz(xmm0, 2, 4);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    InsertIntoXyz(ymm1, 4, 5, k1);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    InsertIntoXyz(zmm2, 8, 6);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    PrintOutRegisterInHex xmm0;                                                   # Print the insertions
    PrintOutRegisterInHex ymm1;
    PrintOutRegisterInHex zmm2;

    ClearRegisters xmm0;                                                          # Insert some zeroes

    InsertIntoXyz(zmm3, 16, 2);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex zmm3;

    my $r = Assemble;
    ok $r =~ m(xmm0: 0D0C 0B0A 0908 FFFF   0706 0504 0302 0100);
    ok $r =~ m(ymm1: 1B1A 1918 1716 1514   FFFF FFFF 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);
    ok $r =~ m(zmm2: 3736 3534 3332 3130   FFFF FFFF FFFF FFFF   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);
    ok $r =~ m(zmm3: 2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   0000 0000 0000 0000   0000 0000 0000 0000   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100);


=head1 Structured Programming

Structured programming constructs

=head2 If($then, $else)

If

     Parameter  Description
  1  $then      Then - required
  2  $else      Else - optional

B<Example:>


    Mov rax, 0;
    Test rax,rax;

    If  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {PrintOutRegisterInHex rax;
     } sub
     {PrintOutRegisterInHex rbx;
     };
    Mov rax, 1;
    Test rax,rax;

    If  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {PrintOutRegisterInHex rcx;
     } sub
     {PrintOutRegisterInHex rdx;
     };

    ok Assemble =~ m(rbx.*rcx)s;


=head2 For($body, $register, $limit, $increment)

For

     Parameter   Description
  1  $body       Body
  2  $register   Register
  3  $limit      Limit on loop
  4  $increment  Increment

B<Example:>



    For  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     {PrintOutRegisterInHex rax
     } rax, 16, 1;

    my $r = Assemble;
    ok $r =~ m(( 0000){3} 0000)i;
    ok $r =~ m(( 0000){3} 000F)i;


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
      If {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushR xmm0;                                                                   # Dump underlying  byte string
    PopR rdi, rax;
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

      If {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

     } 1;

    PushR xmm0;                                                                   # Dump underlying  byte string
    PopR rdi, rax;
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
    PrintOutRaxInHex;
    PrintOutNL;

    PrintOutRaxInReverseInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;
    Push rax;
    Mov rax, rsp;
    Mov rdi, 8;
    PrintOutMemoryInHex;
    PrintOutNL;
    Mov rax, 4096;
    Push rax;
    Mov rax, rsp;
    Mov rdi, 8;
    PrintOutMemoryInHex;
    PrintOutNL;

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
    If                                                                            # Parent
     {Mov rbx, rax;
      WaitPid;
      PrintOutRegisterInHex rax;
      PrintOutRegisterInHex rbx;

      GetPid;                                                                     # Pid of parent as seen in parent  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

      Mov rcx,rax;
      PrintOutRegisterInHex rcx;
     }
    sub                                                                           # Child
     {Mov r8,rax;
      PrintOutRegisterInHex r8;

      GetPid;                                                                     # Child pid as seen in child  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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
    If                                                                            # Parent
     {Mov rbx, rax;

      WaitPid;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

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

=head3 PushR(@r)

Push registers onto the stack

     Parameter  Description
  1  @r         Register

B<Example:>


    Mov rax, 0x11111111;
    Mov rbx, 0x22222222;

    PushR rax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Mov rax, 0x33333333;
    PeekR rbx;
    PopR rax;
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;

    ok Assemble =~ m(rax: 0000 0000 1111 1111.*rbx: 0000 0000 1111 1111)s;


=head3 PopR(@r)

Pop registers from the stack

     Parameter  Description
  1  @r         Register

B<Example:>


    Mov rax, 0x11111111;
    Mov rbx, 0x22222222;
    PushR rax;
    Mov rax, 0x33333333;
    PeekR rbx;

    PopR rax;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;

    ok Assemble =~ m(rax: 0000 0000 1111 1111.*rbx: 0000 0000 1111 1111)s;


=head3 PeekR($r)

Peek at register on stack

     Parameter  Description
  1  $r         Register

B<Example:>


    Mov rax, 0x11111111;
    Mov rbx, 0x22222222;
    PushR rax;
    Mov rax, 0x33333333;

    PeekR rbx;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PopR rax;
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;

    ok Assemble =~ m(rax: 0000 0000 1111 1111.*rbx: 0000 0000 1111 1111)s;


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
  2  $register  Optional address register  else rax

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
    PrintOutRaxInHex;
    PrintOutNL;
    PrintOutRaxInReverseInHex;
    PrintOutNL;
    Push rax;
    Mov rax, rsp;
    Mov rdi, 8;

    PrintOutMemoryInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;
    Mov rax, 4096;
    Push rax;
    Mov rax, rsp;
    Mov rdi, 8;

    PrintOutMemoryInHex;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutNL;

    is_deeply Assemble, <<END;
  0765 4321 0765 4321
  2143 6507 2143 6507
  2143 6507 2143 6507
  0010 0000 0000 0000
  END


=head2 PrintOutMemory()

Print the memory addressed by rax for a length of rdi


B<Example:>


    Comment "Print a string from memory";
    my $s = "Hello World";
    Mov rax, Rs($s);
    Mov rdi, length $s;

    PrintOutMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲


    ok Assemble =~ m(Hello World);


=head2 AllocateMemory()

Allocate the amount of memory specified in rax via mmap and return the address of the allocated memory in rax


B<Example:>


    my $N = 2048;
    my $q = Rs('a'..'p');
    Mov rax, $N;

    AllocateMemory;  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    PrintOutRegisterInHex rax;

    Vmovdqu8 xmm0, "[$q]";
    Vmovdqu8 "[rax]", xmm0;
    Mov rdi,16;
    PrintOutMemory;
    PrintOutNL;

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
    Mov rax, $N;
    AllocateMemory;
    PrintOutRegisterInHex rax;

    Vmovdqu8 xmm0, "[$q]";
    Vmovdqu8 "[rax]", xmm0;
    Mov rdi,16;
    PrintOutMemory;
    PrintOutNL;

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

    Mov rax, Rs(my $f = "zzz.txt");                                               # File to write
    OpenWrite;                                                                    # Open file
    CloseFile;                                                                    # Close file
    Exit;                                                                         # Return to operating system

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

    Mov rax, Rs(my $f = "zzz.txt");                                               # File to write

    OpenWrite;                                                                    # Open file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    CloseFile;                                                                    # Close file
    Exit;                                                                         # Return to operating system

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

    Mov rax, Rs(my $f = "zzz.txt");                                               # File to write
    OpenWrite;                                                                    # Open file

    CloseFile;                                                                    # Close file  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲

    Exit;                                                                         # Return to operating system

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


=head1 Strings

Operations on Strings

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
    ok Assemble =~ m($u);


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
    ok Assemble =~ m($u);


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
    ok Assemble =~ m($u);


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
    ok Assemble =~ m($u);


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
    ok Assemble =~ m($u);


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
      If {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushR xmm0;                                                                   # Dump underlying  byte string
    PopR rdi, rax;
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
      If {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
     } 1;

    PushR xmm0;                                                                   # Dump underlying  byte string
    PopR rdi, rax;
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


B<Example:>


    PrintOutString "Hello World";

    ok Assemble =~ m(Hello World);


=head2 Exit($c)

Exit with the specified return code or zero if no return code supplied.  Assemble() automatically adds a call to Exit(0) if the last operation in the program is not a call to Exit.

     Parameter  Description
  1  $c         Return code

B<Example:>


    PrintOutString "Hello World";

    ok Assemble =~ m(Hello World);


=head2 Assemble(%options)

Assemble the generated code

     Parameter  Description
  1  %options   Options

B<Example:>


    PrintOutString "Hello World";


    ok Assemble =~ m(Hello World);  # 𝗘𝘅𝗮𝗺𝗽𝗹𝗲




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


=head1 Index


1 L<All8Structure|/All8Structure> - Create a structure consisting of 8 byte fields

2 L<AllocateAll8OnStack|/AllocateAll8OnStack> - Create a local data descriptor consisting of the specified number of 8 byte local variables and return an array: (local data descriptor,  variable definitions.

3 L<AllocateMemory|/AllocateMemory> - Allocate the amount of memory specified in rax via mmap and return the address of the allocated memory in rax

4 L<Assemble|/Assemble> - Assemble the generated code

5 L<ByteString::allocate|/ByteString::allocate> - Allocate the amount of space indicated in rdi in the byte string addressed by rax and return the offset of the allocation in the arena in rdi

6 L<ByteString::bash|/ByteString::bash> - Execute the file named in the byte string addressed by rax with bash

7 L<ByteString::char|/ByteString::char> - Append a character expressed as a decimal number to the byte string addressed by rax

8 L<ByteString::clear|/ByteString::clear> - Clear the byte string addressed by rax

9 L<ByteString::copy|/ByteString::copy> - Append the byte string addressed by rdi to the byte string addressed by rax

10 L<ByteString::dump|/ByteString::dump> - Dump details of a byte string

11 L<ByteString::m|/ByteString::m> - Append the content with length rdi addressed by rsi to the byte string addressed by rax

12 L<ByteString::makeReadOnly|/ByteString::makeReadOnly> - Make a byte string read only

13 L<ByteString::makeWriteable|/ByteString::makeWriteable> - Make a byte string writable

14 L<ByteString::nl|/ByteString::nl> - Append a new line to the byte string addressed by rax

15 L<ByteString::out|/ByteString::out> - Print the specified byte string addressed by rax on sysout

16 L<ByteString::q|/ByteString::q> - Append a quoted string == a constant to the byte string addressed by rax

17 L<ByteString::ql|/ByteString::ql> - Append a quoted string containing new line characters to the byte string addressed by rax

18 L<ByteString::rdiInHex|/ByteString::rdiInHex> - Add the content of register rdi in hexadecimal in big endian notation to a byte string

19 L<ByteString::read|/ByteString::read> - Read the file named in the byte string (terminated with a zero byte) addressed by rax and place it into the byte string after clearing the byte string to remove the file name contained therein.

20 L<ByteString::unlink|/ByteString::unlink> - Unlink the file named in the byte string addressed by rax with bash

21 L<ByteString::updateSpace|/ByteString::updateSpace> - Make sure that the byte string addressed by rax has enough space to accommodate content of length rdi

22 L<ByteString::write|/ByteString::write> - Write the content in a byte string addressed by rax to a temporary file and replace the byte string content with the name of the  temporary file

23 L<ByteString::z|/ByteString::z> - Append a trailing zero to the byte string addressed by rax

24 L<ClearMemory|/ClearMemory> - Clear memory - the address of the memory is in rax, the length in rdi

25 L<ClearRegisters|/ClearRegisters> - Clear registers by setting them to zero

26 L<ClearZF|/ClearZF> - Set the zero flag

27 L<CloseFile|/CloseFile> - Close the file whose descriptor is in rax

28 L<Comment|/Comment> - Insert a comment into the assembly code

29 L<CopyMemory|/CopyMemory> - Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi

30 L<CreateByteString|/CreateByteString> - Create an relocatable string of bytes in an arena and returns its address in rax

31 L<cxr|/cxr> - Call a subroutine with a reordering of the xmm registers.

32 L<Db|/Db> - Layout bytes in the data segment and return their label

33 L<Dbwdq|/Dbwdq> - Layout data

34 L<Dd|/Dd> - Layout double words in the data segment and return their label

35 L<Dq|/Dq> - Layout quad words in the data segment and return their label

36 L<Ds|/Ds> - Layout bytes in memory and return their label

37 L<Dw|/Dw> - Layout words in the data segment and return their label

38 L<Exit|/Exit> - Exit with the specified return code or zero if no return code supplied.

39 L<For|/For> - For

40 L<Fork|/Fork> - Fork

41 L<FreeMemory|/FreeMemory> - Free memory via munmap.

42 L<GenTree|/GenTree> - Generate a set of routines to manage a tree held in a byte string with key and data fields of specified widths.

43 L<GetPid|/GetPid> - Get process identifier

44 L<GetPidInHex|/GetPidInHex> - Get process identifier in hex as 8 zero terminated bytes in rax

45 L<GetPPid|/GetPPid> - Get parent process identifier

46 L<GetUid|/GetUid> - Get userid of current process

47 L<hexTranslateTable|/hexTranslateTable> - Create/address a hex translate table and return its label

48 L<If|/If> - If

49 L<InsertIntoXyz|/InsertIntoXyz> - Insert the specified word, double, quad from rax or the contents of xmm0 into the specified xyz register at the specified position shifting data above it to the left.

50 L<Label|/Label> - Create a unique label

51 L<LocalData|/LocalData> - Map local data

52 L<LocalData::allocate8|/LocalData::allocate8> - Add some 8 byte local variables and return an array of variable definitions

53 L<LocalData::free|/LocalData::free> - Free a local data area on the stack

54 L<LocalData::start|/LocalData::start> - Start a local data area on the stack

55 L<LocalData::variable|/LocalData::variable> - Add a local variable

56 L<LocalVariable::stack|/LocalVariable::stack> - Address a local variable on the stack

57 L<OpenRead|/OpenRead> - Open a file, whose name is addressed by rax, for read and return the file descriptor in rax

58 L<OpenWrite|/OpenWrite> - Create the file named by the terminated string addressed by rax for write

59 L<PeekR|/PeekR> - Peek at register on stack

60 L<PopR|/PopR> - Pop registers from the stack

61 L<PrintOutMemory|/PrintOutMemory> - Print the memory addressed by rax for a length of rdi

62 L<PrintOutMemoryInHex|/PrintOutMemoryInHex> - Dump memory from the address in rax for the length in rdi

63 L<PrintOutNL|/PrintOutNL> - Print a new line to stdout

64 L<PrintOutRaxInHex|/PrintOutRaxInHex> - Write the content of register rax to stderr in hexadecimal in big endian notation

65 L<PrintOutRaxInReverseInHex|/PrintOutRaxInReverseInHex> - Write the content of register rax to stderr in hexadecimal in little endian notation

66 L<PrintOutRegisterInHex|/PrintOutRegisterInHex> - Print any register as a hex string

67 L<PrintOutRegistersInHex|/PrintOutRegistersInHex> - Print the general purpose registers in hex

68 L<PrintOutRflagsInHex|/PrintOutRflagsInHex> - Print the flags register in hex

69 L<PrintOutRipInHex|/PrintOutRipInHex> - Print the instruction pointer in hex

70 L<PrintOutString|/PrintOutString> - Print a constant string to sysout.

71 L<PrintOutStringNL|/PrintOutStringNL> - Print a constant string to sysout followed by new line

72 L<PrintOutZF|/PrintOutZF> - Print the zero flag without disturbing it

73 L<PushR|/PushR> - Push registers onto the stack

74 L<Rb|/Rb> - Layout bytes in the data segment and return their label

75 L<Rbwdq|/Rbwdq> - Layout data

76 L<Rd|/Rd> - Layout double words in the data segment and return their label

77 L<ReadFile|/ReadFile> - Read a file whose name is addressed by rax into memory.

78 L<ReadTimeStampCounter|/ReadTimeStampCounter> - Read the time stamp counter and return the time in nanoseconds in rax

79 L<RegisterSize|/RegisterSize> - Return the size of a register

80 L<removeNonAsciiChars|/removeNonAsciiChars> - Return a copy of the specified string with all the non ascii characters removed

81 L<ReorderSyscallRegisters|/ReorderSyscallRegisters> - Map the list of registers provided to the 64 bit system call sequence

82 L<ReorderXmmRegisters|/ReorderXmmRegisters> - Map the list of xmm registers provided to 0-31

83 L<RestoreFirstFour|/RestoreFirstFour> - Restore the first 4 parameter registers

84 L<RestoreFirstFourExceptRax|/RestoreFirstFourExceptRax> - Restore the first 4 parameter registers except rax so it can return its value

85 L<RestoreFirstFourExceptRaxAndRdi|/RestoreFirstFourExceptRaxAndRdi> - Restore the first 4 parameter registers except rax  and rdi so we can return a pair of values

86 L<RestoreFirstSeven|/RestoreFirstSeven> - Restore the first 7 parameter registers

87 L<RestoreFirstSevenExceptRax|/RestoreFirstSevenExceptRax> - Restore the first 7 parameter registers except rax which is being used to return the result

88 L<RestoreFirstSevenExceptRaxAndRdi|/RestoreFirstSevenExceptRaxAndRdi> - Restore the first 7 parameter registers except rax and rdi which are being used to return the results

89 L<Rq|/Rq> - Layout quad words in the data segment and return their label

90 L<Rs|/Rs> - Layout bytes in read only memory and return their label

91 L<Rw|/Rw> - Layout words in the data segment and return their label

92 L<S|/S> - Create a sub with optional parameters name=> the name of the subroutine so it can be reused rather than regenerated, comment=> a comment describing the sub

93 L<SaveFirstFour|/SaveFirstFour> - Save the first 4 parameter registers

94 L<SaveFirstSeven|/SaveFirstSeven> - Save the first 7 parameter registers

95 L<SetLabel|/SetLabel> - Set a label in the code section

96 L<SetRegisterToMinusOne|/SetRegisterToMinusOne> - Set the specified register to -1

97 L<SetZF|/SetZF> - Set the zero flag

98 L<Start|/Start> - Initialize the assembler

99 L<StatSize|/StatSize> - Stat a file whose name is addressed by rax to get its size in rax

100 L<Structure|/Structure> - Create a structure addressed by a register

101 L<Structure::field|/Structure::field> - Add a field of the specified length with an optional comment

102 L<StructureField::addr|/StructureField::addr> - Address a field in a structure by either the default register or the named register

103 L<UnReorderSyscallRegisters|/UnReorderSyscallRegisters> - Recover the initial values in registers that were reordered

104 L<UnReorderXmmRegisters|/UnReorderXmmRegisters> - Recover the initial values in the xmm registers that were reordered

105 L<WaitPid|/WaitPid> - Wait for the pid in rax to complete

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
#__DATA__
use Time::HiRes qw(time);
use Test::More;

my $localTest = ((caller(1))[0]//'Nasm::X86') eq "Nasm::X86";                   # Local testing mode

Test::More->builder->output("/dev/null") if $localTest;                         # Reduce number of confirmation messages during testing

$ENV{PATH} = $ENV{PATH}.":/var/isde:sde";                                       # Intel emulator

if ($^O =~ m(bsd|linux)i)                                                       # Supported systems
 {if (confirmHasCommandLineCommand(q(nasm)) and                                 # Network assembler
      confirmHasCommandLineCommand(q(sde64)))                                   # Intel emulator
   {plan tests => 62;
   }
  else
   {plan skip_all =>qq(Nasm or Intel 64 emulator not available);
   }
 }
else
 {plan skip_all =>qq(Not supported on: $^O);
 }

my $start = time;                                                               # Tests

#goto latest;

if (1) {                                                                        #TExit #TPrintOutString #TStart #TAssemble
  PrintOutString "Hello World";

  ok Assemble =~ m(Hello World);
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
  my $q = Rs my $s = join '', ('a'..'p')x4;
  Mov rax, Ds('0'x128);

  Vmovdqu32 zmm0, "[$q]";
  Vprolq    zmm1, zmm0, 32;
  Vmovdqu32 "[rax]", zmm1;

  Mov rdi, length $s;
  PrintOutMemory;

  ok $s       =~ m(abcdefghijklmnopabcdefghijklmnopabcdefghijklmnopabcdefghijklmnop)s;
  ok Assemble =~ m(efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl)s;
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

if (1) {                                                                        #TAllocateMemory #TFreeMemory
  my $N = 2048;
  my $q = Rs('a'..'p');
  Mov rax, $N;
  AllocateMemory;
  PrintOutRegisterInHex rax;

  Vmovdqu8 xmm0, "[$q]";
  Vmovdqu8 "[rax]", xmm0;
  Mov rdi,16;
  PrintOutMemory;
  PrintOutNL;

  Mov rdi, $N;
  FreeMemory;
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(abcdefghijklmnop)s;
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
  If
   {PrintOutRegisterInHex rax;
   } sub
   {PrintOutRegisterInHex rbx;
   };
  Mov rax, 1;
  Test rax,rax;
  If
   {PrintOutRegisterInHex rcx;
   } sub
   {PrintOutRegisterInHex rdx;
   };

  ok Assemble =~ m(rbx.*rcx)s;
 }

if (1) {                                                                        #TFork #TGetPid #TGetPPid #TWaitPid
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

  Mov rax, Rs(my $f = "zzz.txt");                                               # File to write
  OpenWrite;                                                                    # Open file
  CloseFile;                                                                    # Close file
  Exit;                                                                         # Return to operating system

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
  PrintOutRaxInHex;
  PrintOutNL;
  PrintOutRaxInReverseInHex;
  PrintOutNL;
  Push rax;
  Mov rax, rsp;
  Mov rdi, 8;
  PrintOutMemoryInHex;
  PrintOutNL;
  Mov rax, 4096;
  Push rax;
  Mov rax, rsp;
  Mov rdi, 8;
  PrintOutMemoryInHex;
  PrintOutNL;

  is_deeply Assemble, <<END;
0765 4321 0765 4321
2143 6507 2143 6507
2143 6507 2143 6507
0010 0000 0000 0000
END
 }

if (1) {                                                                        #TPushR #TPopR #TPeekR
  Mov rax, 0x11111111;
  Mov rbx, 0x22222222;
  PushR rax;
  Mov rax, 0x33333333;
  PeekR rbx;
  PopR rax;
  PrintOutRegisterInHex rax;
  PrintOutRegisterInHex rbx;

  ok Assemble =~ m(rax: 0000 0000 1111 1111.*rbx: 0000 0000 1111 1111)s;
 }

if (1) {                                                                        #TAllocateMemory #TFreeMemory #TClearMemory
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
  Mov rax, Rs($0);                                                              # File to read
  ReadFile;                                                                     # Read file
  PrintOutMemory;                                                               # Print memory

  my $r = Assemble;                                                             # Assemble and execute
  ok index(removeNonAsciiChars($r), removeNonAsciiChars(readFile $0)) >= 0;     # Output contains this file
 }

if (1) {                                                                        #TCreateByteString #TByteString::clear #TByteString::out #TByteString::copy #TByteString::nl
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

  my $T = "$t\n" x 8;                                                           # Expected response
  ok Assemble =~ m($T)s;                                                        # Assemble and execute
 }

if (1) {                                                                        #TReorderSyscallRegisters #TUnReorderSyscallRegisters
  Mov rax, 1;  Mov rdi, 2;  Mov rsi,  3;  Mov rdx,  4;
  Mov r8,  8;  Mov r9,  9;  Mov r10, 10;  Mov r11, 11;

  ReorderSyscallRegisters   r8,r9;                                              # Reorder the registers fof syscall
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
  Mov   rax, 8;                                                                 # Append a constant to the byte string
  Tzcnt rax, rax;                                                               # New line
  PrintOutRegisterInHex rax;

  ok Assemble =~ m(rax: 0000 0000 0000 003C.*rax: 0000 0000 0000 0003)s;
 }

if (1) {                                                                        # Print this file  #TByteString::read #TByteString::z #TByteString::q
  my $s = CreateByteString;                                                     # Create a string
  $s->q($0);                                                                    # Append a constant to the byte string
  $s->z;                                                                        # New line
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

if (!$develop) {                                                                # Execute the content of a byte string #TByteString::bash #TByteString::write #TByteString::out #TByteString::unlink #TByteString::ql
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
 }
else
 {ok 1;
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

if (1) {                                                                        #TGenTree #TUnReorderXmmRegisters #TReorderXmmRegisters #TPrintOutStringNL #Tcxr #TByteString::dump
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
    If {PrintOutStringNL "root"} sub {PrintOutStringNL "NOT root"};
   } 1;

  PushR xmm0;                                                                   # Dump underlying  byte string
  PopR rdi, rax;
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

if (1) {                                                                        # Variable length shift
  Mov rax, -1;
  Mov cl, 30;
  Shl rax, cl;
  PushR rax;
  PopR  k0;
  PrintOutRegisterInHex k0;

  ok Assemble =~ m(k0: FFFF FFFF C000 0000)s;
 }

if (1) {                                                                        #TInsertIntoXyz
  ClearRegisters rax;
  Bts rax, 14;
  Not rax;
  PrintOutRegisterInHex rax;
  PushR rax;
  PopR  k1;
  PrintOutRegisterInHex k1;
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
  InsertIntoXyz(xmm0, 2, 4);
  InsertIntoXyz(ymm1, 4, 5, k1);
  InsertIntoXyz(zmm2, 8, 6);

  PrintOutRegisterInHex xmm0;                                                   # Print the insertions
  PrintOutRegisterInHex ymm1;
  PrintOutRegisterInHex zmm2;

  ClearRegisters xmm0;                                                          # Insert some zeroes
  InsertIntoXyz(zmm3, 16, 2);
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

  Mov rax, $s;
  LoadShortStringFromMemoryToZmm(0);
  Mov rax, $t;
  LoadShortStringFromMemoryToZmm(1);
  ConcatenateShortStrings(0, 1);
  PrintOutRegisterInHex xmm0;
  PrintOutRegisterInHex xmm1;

  my $r = Assemble;
  ok $r =~ m(xmm0: 0000 0000 000A 0908   0706 0504 0302 010A);
  ok $r =~ m(xmm1: 0000 0000 0000 0000   0A09 0807 0605 0407);
 }

if (1) {                                                                        # Concatenate empty string to itself 4 times
  my $s = Rb(0);
  Mov rax, $s;
  LoadShortStringFromMemoryToZmm(0);
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);
  ConcatenateShortStrings(0, 0);
  PrintOutRegisterInHex xmm0;

  ok Assemble =~ m(xmm0: 0000 0000 0000 0000   0000 0000 0000 0000);
 }

latest:;

if (1) {                                                                        # Concatenate string of length 1 to itself 4 times
  my $s = Rb(4, 1..4);
  Mov rax, $s;
  LoadShortStringFromMemoryToZmm(0);
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

unlink $_ for grep {/\A\.\/atmpa/} findFiles('.');                              # Remove temporary files

lll "Finished:", time - $start,  "bytes assembled:",   $totalBytesAssembled;
