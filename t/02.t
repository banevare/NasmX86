use strict;
use warnings;
use Test::More tests => 1;
use Nasm::X86 qw(:all);

Mov rax,1;
Mov rbx,9;
Add rax, rbx;
PrintOutRegisterInHex rax;
ok Assemble(emulator=>0) =~ m/rax: 0000 0000 0000 000A/;
