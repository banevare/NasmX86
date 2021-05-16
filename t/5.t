#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

Mov rcx, 0;
Or  rcx, 1;
PrintOutRegisterInHex rcx;

is_deeply Assemble(emulator => 1), <<END;                                       # rcx does not seem to behave as expected when running without the emulator
   rcx: 0000 0000 0000 0001
END
