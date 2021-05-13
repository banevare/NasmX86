#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I/home/phil/perl/cpan/NasmX86/lib/ -I.
#-------------------------------------------------------------------------------
# Test Nasm X86
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
use strict;
use warnings;
use Nasm::X86 qw(:all);
use Test::More tests => 1;

Mov rax, 2;
PrintOutRegisterInHex rax;
ok Assemble(emulator=>0) =~ m(rax: 0000 0000 0000 0002);
