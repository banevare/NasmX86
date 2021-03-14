#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I.
#-------------------------------------------------------------------------------
# Generate Nasm code
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation
package Nasm::X86;
our $VERSION = "20210304";
use warnings FATAL => qw(all);
use strict;
use Carp qw(confess cluck);
use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use feature qw(say current_sub);

my $debug = -e q(/home/phil/);                                                  # Developing
my $sde   = q(/home/phil/Downloads/sde-external-8.63.0-2021-01-18-lin/sde64);   # Intel emulator
   $sde   = q(sde/sde64) unless $debug;

my %rodata;                                                                     # Read only data already written
my %rodatas;                                                                    # Read only string already written
my @rodata;                                                                     # Read only data
my @data;                                                                       # Data
my @bss;                                                                        # Block started by symbol
my @text;                                                                       # Code

BEGIN{
  my %r = (    map {$_=>'8'}    qw(al bl cl dl r8b r9b r10b r11b r12b r13b r14b r15b sil dil spl bpl ah bh ch dh));
     %r = (%r, map {$_=>'s'}    qw(cs ds es fs gs ss));
     %r = (%r, map {$_=>'16'}   qw(ax bx cx dx r8w r9w r10w r11w r12w r13w r14w r15w si di sp bp));
     %r = (%r, map {$_=>'32a'}  qw(eax  ebx ecx edx esi edi esp ebp));
     %r = (%r, map {$_=>'32b'}  qw(r8d r8l r9d r9l r10d r10l r11d r11l r12d r12l r13d r13l r14d r14l r15d r15l));
     %r = (%r, map {$_=>'f'}    qw(st0 st1 st2 st3 st4 st5 st6 st7));
     %r = (%r, map {$_=>'64'}   qw(rax rbx rcx rdx r8 r9 r10 r11 r12 r13 r14 r15 rsi rdi rsp rbp rip));
     %r = (%r, map {$_=>'64m'}  qw(mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7));
     %r = (%r, map {$_=>'128'}  qw(xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm30 xmm31));
     %r = (%r, map {$_=>'256'}  qw(ymm0 ymm1 ymm2 ymm3 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm30 ymm31));
     %r = (%r, map {$_=>'512'}  qw(zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm30 zmm31));
     %r = (%r, map {$_=>'m'}    qw(k0 k1 k2 k3 k4 k5 k6 k7));

  for my $r(sort keys %r)
   {eval "sub $r\{q($r)\}";
    confess $@ if $@;
   }

  my %v = map {$_=>1} values %r;
  for my $v(sort keys %v)                                                       # Types of register
   {my @r = grep {$r{$_} eq $v} sort keys %r;
    eval "sub registers_$v\{".dump(\@r)."}";
    confess $@ if $@;
   }
 }

#D1 Generate Network Assembler Code                                             # Generate assembler code that can be assembled with Nasm

my $labels = 0;
sub label                                                                       # Create a unique label
 {"l".++$labels;                                                                # Generate a label
 }

sub Start()                                                                     # Initialize the assembler
 {@bss = @data = @rodata = %rodata = %rodatas = @text = (); $labels = 0;
 }

sub Ds(@)                                                                       # Layout bytes in memory and return their label
 {my (@d) = @_;                                                                 # Data to be laid out
  my $d = join '', @_;
     $d =~ s(') (\')gs;
  my $l = label;
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
  my $l = label;
  $rodatas{$d} = $l;                                                            # Record label
  push @rodata, <<END;                                                          # Define bytes
  $l: db  '$d';
END
  $l                                                                            # Return label
 }

sub Dbwdq($@)                                                                   # Layout data
 {my ($s, @d) = @_;                                                             # Element size, data to be laid out
  my $d = join ', ', @d;
  my $l = label;
  push @data, <<END;
  $l: d$s $d
END
  $l                                                                            # Return label
 }

sub Db(@) {Dbwdq 'b', @_}                                                       # Layout bytes in the data segment and return their label
sub Dw(@) {Dbwdq 'w', @_}                                                       # Layout words in the data segment and return their label
sub Dd(@) {Dbwdq 'd', @_}                                                       # Layout double words in the data segment and return their label
sub Dq(@) {Dbwdq 'q', @_}                                                       # Layout quad words in the data segment and return their label

sub Rbwdq($@)                                                                   # Layout data
 {my ($s, @d) = @_;                                                             # Element size, data to be laid out
  my $d = join ', ', @d;                                                        # Data to be laid out
  return $_ if $_ = $rodata{$d};                                                # Data already exists so return it
  my $l = label;                                                                # New data - create a label
  push @rodata, <<END;                                                          # Save in read only data
  $l: d$s $d
END
  $rodata{$d} = $l;                                                             # Record label
  $l                                                                            # Return label
 }

sub Rb(@) {Rbwdq 'b', @_}                                                       # Layout bytes in the data segment and return their label
sub Rw(@) {Rbwdq 'w', @_}                                                       # Layout words in the data segment and return their label
sub Rd(@) {Rbwdq 'd', @_}                                                       # Layout double words in the data segment and return their label
sub Rq(@) {Rbwdq 'q', @_}                                                       # Layout quad words in the data segment and return their label

sub Comment(@)                                                                  # Insert a comment into the assembly code
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  push @text, <<END;
; $c
END
 }

sub Exit(;$)                                                                    # Exit with the specified return code or zero if no return code supplied
 {my ($c) = @_;                                                                 # Return code
  if (@_ == 0 or $c == 0)
   {Comment "Exit code: 0";
    push @text, <<END;
  xor rdi, rdi            ; zero
END
   }
  elsif (@_ == 1)
   {Comment "Exit code: $c";
    push @text, <<END;
  mov rdi, $c             ; Constant return code
END
   }
  push @text, <<END;
  mov rax, 60             ; 1 - sys_exit
  syscall                 ; Exit
END
 }

sub SaveFirstFour()                                                             # Save the first 4 parameter registers
 {push @text, <<END;
  push rax
  push rdi
  push rsi
  push rdx
END
 }

sub RestoreFirstFour()                                                          # Restore the first 4 parameter registers
 {push @text, <<END;
  pop rdx
  pop rsi
  pop rdi
  pop rax
END
 }

sub Lea($$)                                                                     # Load effective address
 {my ($target, $source) = @_;                                                   # Target, source
  push @text, <<END;
  lea $target,$source
END
 }

sub Mov($$)                                                                     # Move data
 {my ($target, $source) = @_;                                                   # Target, source
  push @text, <<END;
  mov $target,$source
END
 }

sub PushR(@)                                                                    # Push registers onto the stack
 {my (@r) = @_;                                                                 # Register
  push @text, map {"  push $_\n"} @r;
 }

sub PopR(@)                                                                     # Pop registers in reverse order from the stack so the same parameter list can be shared with pushR
 {my (@r) = @_;                                                                 # Register
  push @text, map {"  pop $_\n"} reverse @r;
 }

sub WriteOutNl()                                                                # Write a new line
 {SaveFirstFour;
  my $a = Rb(10);
  Comment "Write new line";
  push @text, <<END;
  mov rax, 1              ; write
  mov rdi, 1              ; sysout
  mov rsi, $a             ; New line
  mov rdx, 1              ; Length of new line
  syscall
END
  RestoreFirstFour()
 }

sub WriteStringOut($;$)                                                         # One: Write a constant string to sysout. Two write the bytes addressed for the specified length to sysout
 {SaveFirstFour;
  Comment "Write String Out";
  if (@_ == 1)                                                                  # Constant string
   {my ($c) = @_;
    my $l = length($c);
    my $a = Rs($c);
    push @text, <<END;
  mov rax, 1              ; write
  mov rdi, 1              ; sysout
  mov rsi, $a             ; String
  mov rdx, $l             ; Length
  syscall                 ; write $l: $c
END
   }
  elsif (@_ == 2)                                                               # String, length
   {my ($a, $l) = @_;
    push @text, <<END unless $a eq rsi;
  mov rsi, $a             ; String
END
    push @text, <<END unless $l eq rdx;
  mov rdx, $l             ; Length
END
    push @text, <<END;
  mov rax, 1              ; write
  mov rdi, 1              ; sysout
  syscall                 ; Write $l: $a
END
   }
  else
   {confess "Wrong number of parameters";
   }
  RestoreFirstFour()
 }

sub PrintRaxInHex                                                               # Write the content of register rax to stderr in hexadecimal in big endian notation
 {my ($r) = @_;                                                                 # Register
  Comment "Print Rax In Hex";

  my $hexTranslateTable = sub
   {my $h = '0123456789ABCDEF';
    my @t;
    for   my $i(split //, $h)
     {for my $j(split //, $h)
       {push @t, "$i$j";
       }
     }
     Rs @t
   }->();

  my @regs = qw(rax rsi);
  PushR @regs;
  for my $i(0..7)
   {my $s = 8*$i;
    push @text, <<END;
  mov rsi,rax
  shl rsi,$s ; Push selected byte high
  shr rsi,56 ; Push select byte low
  shl rsi,1  ; Multiply by two because each entry in the translation table is two bytes long
  lea rsi,[$hexTranslateTable+rsi]
END
    WriteStringOut &rsi, 2;
    WriteStringOut ' ' if $i % 2;
   }
  PopR @regs;
 }

sub PrintRegisterInHex($)                                                       # Print any register as a hex string
 {my ($r) = @_;                                                                 # Name of the register to print
  Comment "Print register $r in Hex";
  WriteStringOut "$r: ";

  if ($r =~ m(\Ar))                                                             # 64 bit
   {if ($r !~ m(\Arax))
     {push @text, <<END;
  push rax
  mov  rax,$r
END
     }
    PrintRaxInHex;
    if ($r !~ m(\Arax))
     {push @text, <<END;
  pop rax
END
     }
   }
  elsif ($r =~ m(\Ax))                                                          # xmm*
   {my @regs = qw(rax rbx);                                                     # Work registers
    PushR @regs;                                                                # Save work registers
    push @text, <<END;
  sub rsp,16
  movdqu [rsp],$r
END
    PopR @regs;
    PrintRaxInHex;
    WriteStringOut("  ");
    push @text, <<END;
  mov rax, rbx
END
    PrintRaxInHex;
    PopR @regs;
   }
  elsif ($r =~ m(\Ay))                                                          # ymm*
   {my @regs = qw(rax rbx rcx rdx);                                             # Work registers
    PushR @regs;                                                                # Save work registers
    push @text, <<END;
  sub rsp,32
  vmovdqu8 [rsp],$r
END
    PopR @regs;
    for my $R(@regs)
     {if ($R !~ m(\Arax))
       {WriteStringOut("  ");
        push @text, <<END;
  mov rax, $R
END
       }
      PrintRaxInHex;
     }
    PopR @regs;
   }
  elsif ($r =~ m(\Az))                                                          # zmm*
   {my @regs = qw(rax rbx rcx rdx r8 r9 r10 r11);                               # Work registers
    PushR @regs;                                                                # Save work registers
    push @text, <<END;
  sub rsp,64
  vmovdqu8 [rsp],$r
END
    PopR @regs;
    for my $R(@regs)
     {if ($R !~ m(\Arax))
       {WriteStringOut("  ");
        push @text, <<END;
  mov rax, $R
END
       }
      PrintRaxInHex;
     }
    PopR @regs;
   }

  WriteOutNl;
 }

sub PrintRegistersInHex                                                         # Print the general purpose registers in hex
 {my @regs = qw(rax);
  PushR @regs;
  my $l = label;
  push @text, <<END;
$l: lea rax,[$l]
END
  WriteStringOut "rip: ";
  PrintRaxInHex;
  WriteOutNl;

  my $w = registers_64();
  for my $r(sort @$w)
   {next if $r =~ m(rip);
    push @text, <<END if $r eq rax;
  pop rax
  push rax
END
    WriteStringOut reverse(pad(reverse($r), 3)).": ";
    push @text, <<END;
  mov rax,$r
END
    PrintRaxInHex;
    WriteOutNl;
   }
  PopR @regs;
 }

sub Vmovdqu8($$)                                                                # Move memory in 8 bit blocks to an x/y/zmm* register
 {my ($r, $m) = @_;                                                             # Register, memory
  push @text, <<END;
  VMOVDQU8 $r, $m
END
 }

sub Vmovdqu32($$)                                                               # Move memory in 32 bit blocks to an x/y/zmm* register
 {my ($r, $m) = @_;                                                             # Register, memory
  push @text, <<END;
  VMOVDQU32 $r, $m
END
 }

sub Vprolq($$$)                                                                 # Rotate left within quad word indicated number of bits
 {my ($r, $m, $bits) = @_;                                                      # Register, memory, number of bits to rotate
  push @text, <<END;
  VPROLQ $r, $m, $bits
END
 }

sub assemble(%)                                                                 # Assemble the generated code
 {my (%options) = @_;                                                           # Options
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
  my $e    =     q(z);                                                          # Executable file
  my $l    =     q(z.txt);                                                      # Assembler listing
  my $o    =     q(z.o);                                                        # Object file

  my $cmd  = qq(nasm -f elf64 -g -l $l -o $o $c; ld -o $e $o; chmod 744 $e; $sde -- ./$e 2>&1);
  say STDERR qq($cmd);
  my $R    = eval {qx($cmd)};
  say STDERR readFile($l) if $options{list};                                    # Print listing if requested
  say STDERR $R;
  $R                                                                            # Return execution results
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

=head1 Description
 as Perl itself.

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

if ($^O =~ m(bsd|linux)i) {plan tests => 11}                                     # Supported systems
else
 {plan skip_all =>qq(Not supported on: $^O);
 }

my $start = time;                                                               # Tests

if (1) {                                                                        #TExit #TWriteStringOut
  Start;
  WriteStringOut "Hello World To you";
  Exit;
  ok assemble =~ m(Hello World);
 }

if (1) {                                                                        #TMov
  Start;
  my $s = "Hello World";
  my $m = Rs($s);
  Mov rsi, $m;
  WriteStringOut rsi, length($s);
  Exit;
  ok assemble =~ m(Hello World);
 }

if (1) {                                                                        #TPrintRaxInHex
  Start;
  my $q = Rs('abababab');
  Mov(rax, "[$q]");
  WriteStringOut "rax: ";
  PrintRaxInHex;
  WriteOutNl;
  Exit;
  ok assemble() =~ m(rax: 6261 6261 6261 6261)s;
 }

if (1) {                                                                        #TPrintRegistersInHex
  Start;
  my $q = Rs('abababab');
  Mov(rax, 1);
  Mov(rbx, 2);
  Mov(rcx, 3);
  Mov(rdx, 4);
  Mov(r8,  5);
  Mov(r9,  6);
  PrintRegistersInHex;
  Exit;
  ok assemble() =~ m(r8: 0000 0000 0000 0005.*rax: 0000 0000 0000 0001)s;
 }

if (1) {                                                                        #TVmovdqu32 #TVprolq
  Start;
  my $q = Rs('a'..'z');
  my $d = Ds('0'x64);                                                           # Output area
  Vmovdqu32(xmm0, "[$q]");                                                      # Load
  Vprolq   (xmm0,   xmm0, 32);                                                  # Rotate double words in quad words
  Vmovdqu32("[$d]", xmm0);                                                      # Save
  WriteStringOut($d, 16);
  Exit;
  ok assemble() =~ m(efghabcdmnopijkl)s;
 }

if (1) {
  Start;
  my $q = Rs(('a'..'p')x2);
  my $d = Ds('0'x64);
  Vmovdqu32(ymm0, "[$q]");
  Vprolq   (ymm0,   ymm0, 32);
  Vmovdqu32("[$d]", ymm0);
  WriteStringOut($d, 32);
  Exit;
  ok assemble() =~ m(efghabcdmnopijklefghabcdmnopijkl)s;
 }

if (1) {
  Start;
  my $q = Rs(('a'..'p')x4);
  my $d = Ds('0'x128);
  Vmovdqu32(zmm0, "[$q]");
  Vprolq   (zmm0,   zmm0, 32);
  Vmovdqu32("[$d]", zmm0);
  WriteStringOut($d, 64);
  push @text, <<END;
  sub rsp,64
  vmovdqu64 [rsp],zmm0
  pop rax
END
  PrintRaxInHex;
  Exit;
  ok assemble() =~ m(efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl)s;
 }

if (1) {                                                                        #TPrintRegisterInHex
  Start;
  my $q = Rs(('a'..'p')x4);
  Mov r8,"[$q]";
  PrintRegisterInHex r8;
  Exit;
  ok assemble() =~ m(r8: 6867 6665 6463 6261)s;
 }

if (1) {
  Start;
  my $q = Rs('a'..'p');
  Vmovdqu8 xmm0, "[$q]";
  PrintRegisterInHex xmm0;
  Exit;
  ok assemble() =~ m(xmm0: 706F 6E6D 6C6B 6A69   6867 6665 6463 6261)s;
 }

if (1) {
  Start;
  my $q = Rs('a'..'p', 'A'..'P', );
  Vmovdqu8 ymm0, "[$q]";
  PrintRegisterInHex ymm0;
  Exit;
  ok assemble() =~ m(ymm0: 504F 4E4D 4C4B 4A49   4847 4645 4443 4241   706F 6E6D 6C6B 6A69   6867 6665 6463 6261)s;
 }

if (1) {
  Start;
  my $q = Rs(('a'..'p', 'A'..'P') x 2);
  Vmovdqu8 zmm0, "[$q]";
  PrintRegisterInHex zmm0;
  Exit;
  ok assemble() =~ m(zmm0: 504F 4E4D 4C4B 4A49   4847 4645 4443 4241   706F 6E6D 6C6B 6A69   6867 6665 6463 6261   504F 4E4D 4C4B 4A49   4847 4645 4443 4241   706F 6E6D 6C6B 6A69   6867 6665 6463 6261)s;
 }

lll "Finished:", time - $start;
