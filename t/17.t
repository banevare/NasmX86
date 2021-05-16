#Author: tino <gordon.zar@gmail.com>
use strict;
use warnings;
use Test::Most tests => 8;
use Nasm::X86 qw(:all);


if(1){ #TMethod presence in variable objects
   my $b1 = Vb 'bvar', 0xff;
   my $w1 = Vw 'wvar', 0xaabb;
   my $d1 = Vd 'dvar', 0xaabbccdd;
   my $q1 = Vq 'qvar', 0xaaaa_bbbb_cccc_dddd;
   my $z1 = Vz 'zvar', 0x00000001;
   my $z2 = Vz 'zvar2', 0x0000002;
   my $y1 = Vy 'yvar', 0x00000002;
   my $x1 = Vx 'xvar', 0x00000003;
   my @methods = qw(address copy equals assign plusAssign minusAssign arithmetic add sub times division divide boolean
         eq ne ge gt le lt print dump print debug setReg getReg incDec inc dec str min max and or setMask setZmm
         getZmm putZmm putBwdqIntoZmm putBIntoZmm putWIntoZmm putDIntoZmm putQIntoZmm confirmIsMemory clearMemory
         copyMemoryFrom printOutMemoryInHex freeMemory for);
   can_ok($b1, @methods);
   can_ok($w1, @methods);
   can_ok($d1, @methods);
   can_ok($q1, @methods);
   can_ok($z1, @methods);
   can_ok($z1, @methods);
   can_ok($x1, @methods);
TODO: {
         local $TODO = 'not yet implemented';
         eval {
            my $zr = $z1 + $z2;
         };
         ok not $@;
         note $@ if $@;
      }
      Assemble;
}
