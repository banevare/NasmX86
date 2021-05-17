#Author: Tino <gordon.zar@gmai.com>
#Descripton: Simple for loop iteration test
use strict;
use warnings;
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

if(1){                                 #TFor loop construct test
   Start;
   Mov rcx,5;                          # Start iteration from 5
      For{
         PrintOutRegisterInHex rcx;    # Print out register rcx
      } rcx, 10, 1;                    # Up to (not including) 10 with an incement of 1
   Xor rdx,rdx;
   For{
      PrintOutRegisterInHex rdx;
   } rdx, 10, 2;                       # Same but step is now 2
   is_deeply Assemble, <<END;
   rcx: 0000 0000 0000 0005
   rcx: 0000 0000 0000 0006
   rcx: 0000 0000 0000 0007
   rcx: 0000 0000 0000 0008
   rcx: 0000 0000 0000 0009
   rdx: 0000 0000 0000 0000
   rdx: 0000 0000 0000 0002
   rdx: 0000 0000 0000 0004
   rdx: 0000 0000 0000 0006
   rdx: 0000 0000 0000 0008
END
   done_testing;
}
