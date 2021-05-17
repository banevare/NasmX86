
#Author: tino <gordon.zar@gmail.com>
use strict;
use warnings;
use Test::Most tests => 1;
use Data::Table::Text qw(readFile);
use Nasm::X86 qw(:all);

if(1){ #TMissing size operand after assembly
  TODO:{
    local $TODO = 'Possibly desired feature';
    can_ok('Nasm::X86', qw(Vxq));
   # no strict 'refs';
   # my $s = 'Nasm::X86::Vxq';
   # my $zm = Nasm::X86::Vxq 'xmm0', 5, rsi;
   # Assemble;
   # my $a = readFile 'z.asm';
   # like $a, qr/mov\s+rbp,rsp\n\s+mov (?:[qd]?word|byte)\s*?\[\w\d+\], 5/m;
    }
}
done_testing;
