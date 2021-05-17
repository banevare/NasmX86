#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/16
# Description: rcx register gets clobbered without running on the emulator.
# checks are needed if this is a software bug. (possible hardware bug???)
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

if(1){ #TRCX emulator-less clobber test
EMU: {
Start;
Mov rcx, 0;
PrintOutRegisterInHex rcx;

is_deeply Assemble(emulator => 1), <<END;
   rcx: 0000 0000 0000 0000
END
}
TODO: {
local $TODO = 'Exact problem not yet fully identified';
Start;
Mov rcx, 0;
PrintOutRegisterInHex rcx;

is_deeply Assemble(emulator => 0), <<END;
   rcx: 0000 0000 0000 0000
END
}
}
done_testing;
