#Tine 2021/05/14
use Test::Most tests => 1;
use Nasm::X86 qw(:all);
use Data::Dump qw(dump);

my $oa = Vq 'vara', 10;
my $ob = Vq 'varb', 20;
my $oc = Vq 'varc',  0;
my $oi = Vq 'vari',  0;
my $om = Vq 'varm',  0;
my $od = Vq 'vard', 10;
say STDERR "AAA1 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
SetLabel 'OP_tests';
say STDERR "AAA2 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
$oc = $oa + $ob;
say STDERR "AAA3 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
$oa -= 5;
say STDERR "AAA4 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
$ob *= 2;
say STDERR "AAA5 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
$od /= 2;
say STDERR "AAA6 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
$oi = $ob - $oa;
say STDERR "AAA7 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
say STDERR "AAA8 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
$om = $oa * 2;
say STDERR "AAA9 ", dump([$oa, $ob, $oc, $oi, $om, $od]);
KeepFree (rax);
SetLabel 'Addressing_test';
say STDERR "BBBB ", dump([$oa, $ob, $oc, $oi, $om, $od]);
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

is_deeply Assemble, <<END;
   rax: 0000 0000 0000 001E
   rbx: 0000 0000 0000 0028
   rdx: 0000 0000 0000 0005
   rdi: 0000 0000 0000 0023
   rsi: 0000 0000 0000 000A
   r15: 0000 0000 0000 0005
END
