#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
# Tino 2021/05/15
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

WITH_EMU:{
   Mov rcx, 0;
   Or  rcx, 1;
   PrintOutRegisterInHex rcx;

   is_deeply Assemble(emulator => 1), <<END;
   rcx: 0000 0000 0000 0001
END
}
WITHOUT_EMU:{
   Mov rcx, 0;
   Or  rcx, 1;
   PrintOutRegisterInHex rcx;

   is_deeply Assemble(emulator => 0), <<END;
   rcx: 0000 0000 0000 0001
END
}
done_testing;
