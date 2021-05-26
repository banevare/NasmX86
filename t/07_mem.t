#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
#Simple memory allocation test via nasm syntax
use strict;
use warnings;
use Test::More tests => 5;
use Nasm::X86 qw(:all);

AllocateMemory->call((my $size = Vq(size,32)), my $address = Vq(address));
$address->setReg(rax);
Mov 'qword [rax]', 10;
Mov rcx,11;
Mov 'qword [rax+0x08]', rcx;
Mov 'qword [rax+0x10]', 12;
Inc rcx;
Inc rcx;
Mov 'qword [rax+0x18]', rcx;
Mov rbx, 'qword [rax]';
Mov rdi, 'qword [rax+0x08]';
Mov rsi, 'qword [rax+0x10]';
Mov rdx, 'qword [rax+0x18]';
Mov 'dword [rax+1024]', 0xbadbeef;
Mov 'dword [rax+1020]', 0xbadbeef;
Mov r10, 'qword [rax+1020]';
FreeMemory->call($size, $address);
PrintOutRegisterInHex rbx;
PrintOutRegisterInHex rdi;
PrintOutRegisterInHex rdx;
PrintOutRegisterInHex rsi;
PrintOutRegisterInHex r10;
my $r = Assemble;
ok $r =~ m/rbx: 0000 0000 0000 000A/;
ok $r =~ m/rdi: 0000 0000 0000 000B/;
ok $r =~ m/rdx: 0000 0000 0000 000D/;
ok $r =~ m/rsi: 0000 0000 0000 000C/;
ok $r =~ m/r10: 0BAD BEEF 0BAD BEEF/;
