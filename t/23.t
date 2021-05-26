#Author: tino <gordon.zar@gmail.com>
#Testing proper argument passing to custom defined functions
use strict;
use warnings;
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

my $fun = Subroutine {
  PrintOutRegisterInHex rdi, rsi, rdx, rcx, r8, r9;
} name => 'argtest';

CallWithArgsX $fun, 1, 2, 3, 4;
CallWithArgsX $fun->start, 1, 2, 3, 4; # $fun->start returns a string with the symbol defining the function
is_deeply Assemble, <<END;
   rdi: 0000 0000 0000 0001
   rsi: 0000 0000 0000 0002
   rdx: 0000 0000 0000 0003
   rcx: 0000 0000 0000 0004
    r8: 0000 0000 0000 0000
    r9: 0000 0000 0000 0000
   rdi: 0000 0000 0000 0001
   rsi: 0000 0000 0000 0002
   rdx: 0000 0000 0000 0003
   rcx: 0000 0000 0000 0004
    r8: 0000 0000 0000 0000
    r9: 0000 0000 0000 0000
END
