# Tino 2021/05/13
use strict;
use warnings;
use Nasm::X86 qw(:all);
use Data::Dump qw(dump);
use Test::More tests => 3;

my $s = join '', ('a' .. 'p')x4;

sub test_macro{                                                                 # Our macro for example

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
my $r = eval {Assemble(emulator => 0)};                                                 # Outcome depends on which  machine we run on at GitHub, some have avx some do not!
say STDERR "AAAA ", dump([$@, $r]);

ok $r =~ m(efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl) ||
   $@ =~ m(Illegal instruction);
