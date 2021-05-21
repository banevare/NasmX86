#Author: tino <gordon.zar@gmail.com>
use strict;
use warnings;
use Test::Most tests => 15;
use Nasm::X86 qw(:all);

if(1){ #TMethod presence in variable objects #TVariale allocation test
  my $b1 = Vb 'bvar',      0xff;
  my $w1 = Vw 'wvar',      0xaabb;
  my $d1 = Vd 'dvar',      0xaabbccdd;
  my $q1 = Vq 'qvar',      0xaaaa_bbbb_cccc_dddd;
  my $z1 = Vz 'zvar',      0x1;
  my $z2 = Vz 'zvar2',     0x00000002;
  my $y1 = Vy 'yvar',      0x00000003;
  my $x1 = Vx 'xvar',      0x04;
#  my $xm1 = Nasm::X86::Vxq 'xmmvar',  'qword 0x05', rsi;
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
        ok not $@, 'Addition implementation for Vz variables';
        note $@ if $@;
      }

  $b1->dump;
  $w1->dump;
  $d1->dump;
  $q1->dump;
  $z1->dump;
  $y1->dump;
  $x1->dump;
#    $xm1->dump;
  my $r = Assemble;
  TODO:{
    local $TODO = 'Not yet fully impemented';
    like $r, qr/bvar: FF/, 'Presence of bvar in output';
    like $r, qr/wvar: AABB/, 'Presence of wvar in output';
    like $r, qr/dvar: AABB CCDD/, 'Presence of dvar in output';
    like $r, qr/zvar/, 'Presence of zvar in output';
    like $r, qr/yvar/, 'Presence of yvar in output';
  }
  like $r, qr/qvar: AAAA BBBB CCCC DDDD/, 'Presence of qvar in output with correct value';
  like $r, qr/xvar: 0000 0000 0000 0004  0000 0000 0000 0000/, 'Presence of xvar in output with correct value';
#    like $r, qr/xmmvar/;
}
done_testing;
