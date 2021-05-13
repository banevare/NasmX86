#Structure allocation test with 2 qword fields
use strict;
use warnings;
use Test::More tests => 1;
use Nasm::X86 qw(:all);
use Data::Dumper;

Mov rax,8*8;
AllocateMemory;
my $st = Structure();
my $stf = $st->field(8, 'uint8');
my $stf2 = $st->field(8, 'uint8');
#print Dumper $st;
#print Dumper $stf;
Mov 'qword' . $stf->addr, 10;
Mov 'qword' . $stf2->addr, 11;
Mov rbx, $stf->addr;
Mov rdx, $stf2->addr;
PrintOutRegisterInHex rbx;
PrintOutRegisterInHex rdx;
FreeMemory;
my $r = Assemble(emulator=>0);
ok $r =~ m/rbx: 0000 0000 0000 000A/;
ok $r =~ m/rdx: 0000 0000 0000 000B/;
