#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/15
# Bitwise operator feature implementation test
use Test::Most tests => 6;
use Nasm::X86 qw(:all);

my $ox1 = Vq 'varx1', 0b01;
my $ox2 = Vq 'varx2', 0b11;
my $o_and1 = Vq 'varand1', 0b01;
my $o_and2 = Vq 'varand2', 0b10;
my $oor1 = Vq 'varor1', 0;
my $oor2 = Vq 'varor2', 1;

ok eval {
   my $oxr = $ox1 ^ $ox2;
   $oxr->dump;
   ok Assemble =~ m/\(varx1 xor varx2\): 0000 0000 0000 0002/;
}, 'bitwise xor operator feature test'; 
ok eval {
   my $o_andr = $o_and1 & $o_and2;
   $o_andr->dump;
   ok Assemble =~ m/\(varand1 and varand2\): 0000 0000 0000 0000/;
}, 'bitwise and operator feature test';
ok eval {
   my $oorr = $oor1 | $oor2;
   $oorr->dump;
   ok Assemble =~ m/\(varor1 or varor2\): 0000 0000 0000 0001/;
}, 'bitwise or operator feature test';
done_testing;
