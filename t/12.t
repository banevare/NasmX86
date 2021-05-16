#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/13
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

if(1){ #TTest for register preservation after CALL instruction
   my $fun = S{
      SetLabel 'testfun_start';
      SaveFirstSeven;
      Mov rax,rdi;
      Xor rdi,rdi;
      Inc rdi;
      PrintOutRegisterInHex rax;
      RestoreFirstSeven;
      SetLabel 'testfun_end';
   };
   Mov rdi,10;
   Call $fun;
   PrintOutRegisterInHex rdi;
   my $r = Assemble;
   ok $r =~ m/rax: 0000 0000 0000 000A/;
   ok $r =~ m/rdi: 0000 0000 0000 000A/;
   done_testing();
}
