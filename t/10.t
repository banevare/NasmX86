#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
#Simple test and example of division via the function directly.
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

my $oa = Vq 'mema', 10;
my $ob = Vq 'memb', 2;
my $or = Variable::divide($oa, $ob);
my $om = Variable::mod($oa, 3);
KeepFree (rax);
Mov rax, $or->address;
Mov rbx, $om->address;
PrintOutRegisterInHex rax;
PrintOutRegisterInHex rbx;

my $r = Assemble;
ok $r =~ m/rax: 0000 0000 0000 0005/;
ok $r =~ m/rbx: 0000 0000 0000 0001/;
