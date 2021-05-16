#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
#Tin0 2021/05/14
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

if(1){ #TArithmetic operations test on qword variables
   my $oa = Vq 'vara', 10;
   my $ob = Vq 'varb', 20;
   my $oc = Vq 'varc',  0;
   my $oi = Vq 'vari',  0;
   my $om = Vq 'varm',  0;
   my $od = Vq 'vard', 10;

   SetLabel 'OP_tests';
   $oc  = $oa + $ob;
   $oa -= 5;
   $ob *= 2;
   $od /= 2;
   $oi  = $ob - $oa;
   $om  = $oa * 2;
   KeepFree (rax);
   SetLabel 'Addressing_test';
   
   $oc->dump;                                # Print variable contents to stdout along with operations performed on them
   $oa->dump;
   $ob->dump;
   $od->dump;
   $oi->dump;
   $om->dump;

   is_deeply Assemble, <<END;
(vara add varb): 0000 0000 0000 001E
vara: 0000 0000 0000 0005
(varb times 2): 0000 0000 0000 0028
(vard / ): 0000 0000 0000 0005
((varb times 2) sub vara): 0000 0000 0000 0023
(vara times 2): 0000 0000 0000 000A
END
}
