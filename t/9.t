#Simple branching loop test
use strict;
use warnings;
use Test::More tests => 1;
use Nasm::X86 qw(:all);

my $l = Label;
Mov rcx,10;
Mov rax,0;
SetLabel $l;
Add rax,2;
Dec rcx;
Cmp rcx,0;
Jnz $l;
PrintOutRegisterInHex rax;
my $r = Assemble;
ok $r =~ m/rax: 0000 0000 0000 0014/;
