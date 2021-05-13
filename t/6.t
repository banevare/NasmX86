use strict;
use warnings;
use Nasm::X86 qw(:all);
use Test::More tests => 5;

my $oa = Vq 'vara', 10;
my $ob = Vq 'varb', 20;
my $oc = Vq 'varc', 0;
my $oi = Vq 'vari', 0;
my $om = Vq 'varm', 0;
my $od = Vq 'vard', 10;
$oc = $oa + $ob;
$oa -= 5;
$ob *= 2;
# $od /= 2; # division generates some error about rax being reset
$oi = $ob - $oa;
$om = $oa * 2;
Mov rax,Variable::address($oc);
Mov rbx,Variable::address($ob);
Mov rdx,Variable::address($oa);
Mov rdi,Variable::address($oi);
Mov rsi,Variable::address($om);
PrintOutRegisterInHex rax;
PrintOutRegisterInHex rbx;
PrintOutRegisterInHex rdx;
PrintOutRegisterInHex rdi;
PrintOutRegisterInHex rsi;
my $r = Assemble;

ok $r =~ m/rax: 0000 0000 0000 001E/;
ok $r =~ m/rdx: 0000 0000 0000 0005/;
ok $r =~ m/rbx: 0000 0000 0000 0028/;
ok $r =~ m/rdi: 0000 0000 0000 0023/;
ok $r =~ m/rsi: 0000 0000 0000 000A/;


