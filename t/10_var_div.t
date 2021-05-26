#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/15
# Simple test and example of division.
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

my $oa = Vq 'mema', 10;
my $ob = Vq 'memb', 2;

my $or = $oa / $ob;
my $om = $oa % 3;

Mov rax, $or->address;
Mov rbx, $om->address;

PrintOutRegisterInHex rax;
PrintOutRegisterInHex rbx;

is_deeply Assemble, <<END;
   rax: 0000 0000 0000 0005
   rbx: 0000 0000 0000 0001
END
