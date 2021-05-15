#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/14
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

my $oa = Vq 'vara', 10;
my $ob = Vq 'varb', 20;

SetLabel 'OP_tests';
my $oc = $oa + $ob;
$oc->dump;

is_deeply Assemble, <<END;
(vara add varb): 0000 0000 0000 001E
END
