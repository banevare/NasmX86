use strict;
use warnings;
use Test::Most tests => 2;
use Nasm::X86 qw(:all);


my $fun = S{
	SetLabel 'testfun_start';
	SaveFirstSeven;
	Mov rax,rdi;
	Xor rdi,rdi;
	Inc rdi;
	PrintOutRegisterInHex rax;
	RestoreFirstSeven;
	SetLabel 'testfun_end';
};
Mov rdi,10;
Call $fun;
PrintOutRegisterInHex rdi;
my $r = Assemble;
ok $r =~ m/rax: 0000 0000 0000 000A/;
ok $r =~ m/rdi: 0000 0000 0000 000A/;
done_testing();
