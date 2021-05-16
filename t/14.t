#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/15
#Testing of call frames and local variable assignment
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

if(1){ #TStack-frame corruption test via LocalData
   my $sub = S
   {my $vars = LocalData;
      my $a = $vars->variable(8, 'a');
      my $b = $vars->variable(8, 'b');

      $vars->start;
      Mov $b->stack,  4;
      $vars->free;
   };

   Call $sub;

   is_deeply Assemble, '';
}
