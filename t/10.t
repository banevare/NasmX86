#Simple test and example of division via the function directly.
use strict;
use warnings;
use Test::More tests => 1;
use Nasm::X86 qw(:all);

my $oa = Vq 'mema', 10;
my $ob = Vq 'memb', 2;
my $or = Vq 'memr', 0;
$or = Variable::division('/', $oa, $ob);
KeepFree (rax);
Mov rax, $or->address;
PrintOutRegisterInHex rax;
my $r = Assemble;
ok $r =~ m/rax: 0000 0000 0000 0005/;
