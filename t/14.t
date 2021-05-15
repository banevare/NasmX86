#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/15
#Testing of call frames and local variable assignment
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

my $vars = LocalData;
my $a = $vars->variable(8, 'a');
my $b = $vars->variable(8, 'b');

$vars->start;

Mov $a->stack, 10;
Mov $b->stack,  4;
Mov rbx, $a->stack;

Mov  r9, $b->stack;
Add rbx, r9;

PrintOutRegisterInHex r9;
PrintOutRegisterInHex rbx;

$vars->free;

is_deeply Assemble, <<END;
    r9: 0000 0000 0000 0004
   rbx: 0000 0000 0000 000E
END
