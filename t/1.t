#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I/home/phil/perl/cpan/NasmX86/lib/ -I.
#-------------------------------------------------------------------------------
# Test Nasm X86
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
#use warnings FATAL => qw(all);
#use strict;
use feature qw(say current_sub);
use Nasm::X86 qw(:all);
use Test::More tests=>1;

Mov rax, 2;
PrintOutRegisterInHex rax;
ok Assemble =~ m(rax: 0000 0000 0000 0002);
