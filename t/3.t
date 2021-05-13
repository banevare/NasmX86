# Tino 2021/05/13
use strict;
use warnings;
use Nasm::X86 qw(:all);
use Test::More tests => 3;

#our macro for example
my $s = join '', ('a' .. 'p')x4;

sub test_macro{
        my $q = Rs $s;
        Mov rax, Ds('0'x128);
        Vmovdqu64 zmm0, "[$q]";
        Vprolq zmm1, zmm0, 32;
        Vmovdqu64 "[rax]", zmm1;
        Mov rdi, length $s;
        PrintOutMemoryNL;
}
test_macro;
is_deeply "$s\n", <<END;
abcdefghijklmnopabcdefghijklmnopabcdefghijklmnopabcdefghijklmnop
END

is_deeply Assemble(emulator => 1), <<END;
efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl
END

test_macro;
is_deeply Assemble(emulator => 0), <<END;
efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl
END
