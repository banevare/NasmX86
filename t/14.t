#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/15
#Testing of call frames and local variable assignment
# 2012/05/22
#   added a check for new calling convention
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

my $sub = Nasm::X86::Subroutine
 {my $vars = LocalData;
  my $a = $vars->variable(8, 'a');
  my $b = $vars->variable(8, 'b');

  $vars->start;
  Mov $b->stack,  4;
  $vars->free;
 } name => 'testroutine', in => {testparam => 3};

can_ok($sub, 'call', 'start');
Call $sub->start;
my $var = Vq 'x',10;
$sub->call(testparam => $var);

is_deeply Assemble, '';
