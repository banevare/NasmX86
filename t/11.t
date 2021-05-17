#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
#Structure allocation test with 2 qword fields
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

if(1){ #TStructure allocation test
   Mov rax,8*8;
   AllocateMemory;
   my $st = Structure();
   my $stf = $st->field(8, 'uint8');
   my $stf2 = $st->field(8, 'uint8');
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
}
