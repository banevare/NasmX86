use Test::Most tests => 1;
use Nasm::X86 qw(:all);

Mov rcx, 0;
Or  rcx, 1;
PrintOutRegisterInHex rcx;

is_deeply Assemble(emulator => 0), <<END;      # rcx does not seem to behave as expected when running without the emulator
   rcx: 0000 0000 0000 0001
END
