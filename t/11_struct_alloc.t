#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
#Structure allocation test with 2 qword fields
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

my $st   = Structure();
my $stf  = $st->field(8, 'uint8');
my $stf2 = $st->field(8, 'uint8');

AllocateMemory->call(Vq(size, 64), my $address = Vq('address'));
$address->setReg(rax);

Mov 'qword' . $stf ->addr, 10;
Mov 'qword' . $stf2->addr, 11;

Mov rbx, $stf ->addr;
Mov rdx, $stf2->addr;
PrintOutRegisterInHex rbx, rdx;

FreeMemory->call(Vq(size, 64), $address);

my $r = Assemble(emulator=>0);
ok $r =~ m/rbx: 0000 0000 0000 000A/;
ok $r =~ m/rdx: 0000 0000 0000 000B/;
