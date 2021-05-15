#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
#Tin0 2021/05/14
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

my $oa = Vq 'vara', 10;
my $ob = Vq 'varb', 20;
my $oc = Vq 'varc',  0;
my $oi = Vq 'vari',  0;
my $om = Vq 'varm',  0;
my $od = Vq 'vard', 10;

SetLabel 'OP_tests';
$oc  = $oa + $ob;
$oa -= 5;
$ob *= 2;
$od /= 2;
$oi  = $ob - $oa;
$om  = $oa * 2;
KeepFree (rax);
SetLabel 'Addressing_test';

Mov rax, $oc->address;
Mov rbx, $ob->address;
Mov rdx, $oa->address;
Mov rdi, $oi->address;
Mov rsi, $om->address;
Mov r15, $od->address;

PrintOutRegisterInHex rax;
PrintOutRegisterInHex rbx;
PrintOutRegisterInHex rdx;
PrintOutRegisterInHex rdi;
PrintOutRegisterInHex rsi;
PrintOutRegisterInHex r15;

is_deeply Assemble, <<END;
   rax: 0000 0000 0000 001E
   rbx: 0000 0000 0000 0028
   rdx: 0000 0000 0000 0005
   rdi: 0000 0000 0000 0023
   rsi: 0000 0000 0000 000A
   r15: 0000 0000 0000 0005
END
