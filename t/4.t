#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
use Test::Most tests => 4;
use Nasm::X86 qw(:all);

Mov rax,0b0001;
Mov rbx,0b0010;
Mov rdx,0;
Mov rcx,0;

Xor rax,0b0001;
And rbx,0b0001;
Or rdx,1;
Or rcx,1;                                                                       # rcx does not seem to behave as expected when running without the emulator
PrintOutRegisterInHex rax;
PrintOutRegisterInHex rbx;
PrintOutRegisterInHex rdx;
PrintOutRegisterInHex rcx;
my $r = Assemble emulator => 1;
ok $r =~ m/rax: 0000 0000 0000 0000/;
ok $r =~ m/rbx: 0000 0000 0000 0000/;
ok $r =~ m/rdx: 0000 0000 0000 0001/;
ok $r =~ m/rcx: 0000 0000 0000 0001/;
