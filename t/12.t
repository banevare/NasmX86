#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
use strict;
use warnings;
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

my $fun = Nasm::X86::Subroutine {
  my $l1 = Label;
  my $l2 = Label;
  SetLabel $l1;
  SaveFirstSeven;
  Mov rax,rdi;
  Xor rdi,rdi;
  Inc rdi;
  PrintOutRegisterInHex rax;
  RestoreFirstSeven;
  SetLabel $l2;
} name => 'testroutine';
Mov rdi,10;
Call $fun->start;
PrintOutRegisterInHex rdi;
my $r = Assemble;
ok $r =~ m/rax: 0000 0000 0000 000A/;
ok $r =~ m/rdi: 0000 0000 0000 000A/;
done_testing();
