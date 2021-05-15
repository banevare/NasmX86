#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/12
use Nasm::X86 qw(:all);
use Test::Most tests => 1;

Mov rax,1;
Mov rbx,9;
Add rax, rbx;
PrintOutRegisterInHex rax;
ok Assemble(emulator=>0) =~ m/rax: 0000 0000 0000 000A/;
