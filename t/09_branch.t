#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
#Simple branching loop test
use Test::More tests => 1;
use Nasm::X86 qw(:all);

if(1){ #TBranching loop test
   my $l = Label;
   Mov rcx,10;
   Mov rax,0;
   SetLabel $l;
   PrintOutRegisterInHex rax;
   Add rax,2;
   Dec rcx;
   Cmp rcx,0;
   Jnz $l;
   my $r = Assemble;
   is_deeply $r, <<END;
   rax: 0000 0000 0000 0000
   rax: 0000 0000 0000 0002
   rax: 0000 0000 0000 0004
   rax: 0000 0000 0000 0006
   rax: 0000 0000 0000 0008
   rax: 0000 0000 0000 000A
   rax: 0000 0000 0000 000C
   rax: 0000 0000 0000 000E
   rax: 0000 0000 0000 0010
   rax: 0000 0000 0000 0012
END
}
