use strict;
use warnings;
use Test::More tests => 1;
use Nasm::X86 qw(:all);

Mov rcx,0;
Or rcx,1; #rcx does not seem to behave as expected when running without the emulator
PrintOutRegisterInHex rcx;
my $r = Assemble emulator => 0;
ok $r =~ m/rcx: 0000 0000 0000 0001/;
