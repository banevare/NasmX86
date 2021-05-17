#Author: tino <gordon.zar@gmail.com>
use strict;
use warnings;
use Test::Most tests => 2;
use Data::Table::Text qw(readFile);
use Nasm::X86 qw(:all);

if(1){ #TLoadZmmFromMemory #TVz initaliztion
  Mov r10,0x0BAD_F00D;

  my $zm0 = Vz 'zmm0var', r10;
  my $zm1 = Vz 'zmm1var', 0x0011_0011;
  Mov rdx, 56;
  Mov rbx, 4;
  Lea rsi, $zm0->address;
  LoadZmmFromMemory 0, rdx, rbx, rsi;
  PrintOutRegisterInHex zmm0;

  KeepFree rdx,rbx,rsi;
  Mov rdx, 36;
  Mov rbx, 4;
  Lea rsi, $zm1->address;
  LoadZmmFromMemory 1, rdx, rbx, rsi;
  PrintOutRegisterInHex zmm1;

  my $r = Assemble;
  like $r, qr/zmm0: 0000 0000 0BAD F00D   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000/m, 'zmm0 initializd from register';
  like $r, qr/zmm1: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0011 0011 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000/m, 'zmm1 initialized from immediate value';
}
#my $a = readFile 'z.asm';
#like $a, qr/mov\s+rbp,rsp\n\s+mov (?:[qd]?word|byte)\s*?\[\w\d+\], 5/m;
