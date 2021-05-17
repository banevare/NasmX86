#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
#Simple test to check if informing the module about freeing the register for further use works as expected
use strict;
use warnings;
use Test::More tests => 2;
use Nasm::X86 qw(:all);

if(1){ #TKeepFree reg test
   Mov rax,0x0A;
   Mov rbx,0x0C;
   KeepFree (rax, rbx);
   Mov rax,0x0B;
   Mov rbx,0x0D;
   PrintOutRegisterInHex rax;
   PrintOutRegisterInHex rbx;
   my $r = Assemble;
   ok $r =~ m/rax: 0000 0000 0000 000B/;
   ok $r =~ m/rbx: 0000 0000 0000 000D/;
}
