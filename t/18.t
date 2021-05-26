#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
#Author: tino <gordon.zar@gmail.com>
use Test::Most tests => 1;
use Data::Table::Text qw(readFile);
use Nasm::X86 qw(:all);

if (1) {                                                                        #TLoadZmmFromMemory #TVz
  Mov r10, 0x0BAD_F00D;
  my $zm0 = Vz 'zmm0var', r10, r10, r10, r10, r10, r10, r10, r10;

  Mov r11, 0x0011_0011;
  my $zm1 = Vz 'zmm1var', r11, r11, r11, r11, r11, r11, r11, r11;

  Mov rdx, 56;
  Mov rbx, 4;
  Lea rsi, $zm0->address;
  LoadZmmFromMemory 0, rdx, rbx, rsi;
  PrintOutRegisterInHex zmm0;
  KeepFree rdx, rbx, rsi;

  Mov rdx, 36;
  Mov rbx, 4;
  Lea rsi, $zm1->address;
  LoadZmmFromMemory 1, rdx, rbx, rsi;
  PrintOutRegisterInHex zmm1;

  is_deeply Assemble, <<END;
  zmm0: 0000 0000 0BAD F00D   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
  zmm1: 0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0011 0011 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000
END
}
