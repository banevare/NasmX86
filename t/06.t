use strict;
use warnings;
use Test::Most tests => 6;
use Nasm::X86 qw(:all);

my $oa = Vq 'vara', 10;
my $ob = Vq 'varb', 20;
my $oc = Vq 'varc', 0;
my $oi = Vq 'vari', 0;
my $om = Vq 'varm', 0;
my $od = Vq 'vard', 10;
SetLabel 'OP_tests';
$oc = $oa + $ob;
$oa -= 5;
$ob *= 2;
$od /= 2;
$oi = $ob - $oa;
$om = $oa * 2;
KeepFree (rax);
SetLabel 'Addressing_test';
Mov rax,$oc->address;
Mov rbx,$ob->address;
Mov rdx,$oa->address;
Mov rdi,$oi->address;
Mov rsi,$om->address;
Mov r15,$od->address;
PrintOutRegisterInHex rax;
PrintOutRegisterInHex rbx;
PrintOutRegisterInHex rdx;
PrintOutRegisterInHex rdi;
PrintOutRegisterInHex rsi;
PrintOutRegisterInHex r15;
my $r = Assemble;

ok $r =~ m/rax: 0000 0000 0000 001E/;
ok $r =~ m/rdx: 0000 0000 0000 0005/;
ok $r =~ m/rbx: 0000 0000 0000 0028/;
ok $r =~ m/rdi: 0000 0000 0000 0023/;
ok $r =~ m/rsi: 0000 0000 0000 000A/;
ok $r =~ m/r15: 0000 0000 0000 0005/;


