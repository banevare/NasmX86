use strict;
use warnings;
use Nasm::X86 qw(:all);
use Test::More tests => 2;

my $q = Rs my $s = join '', ('a' .. 'p')x4;

#our macro for example
sub test_macro{
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

is_deeply Assemble, <<END;
efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl
END
