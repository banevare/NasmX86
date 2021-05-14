#Testing of local data variables
use strict;
use warnings;
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

sub add_5{
	my $vars = LocalData;
	my $v = $vars->variable(8,'local_5');
	$vars->start;
	Mov 'qword' . $v->stack, 5;
	Add rdi, $v->stack;
	Mov rax,rdi;
	$vars->free;
}

sub add_2_locals{
	my $vars = LocalData;
	my $a = $vars->variable(8,'a');
	my $b = $vars->variable(16,'b');
	$vars->start;
	explain $a;
	KeepFree(rax);
	Mov 'qword' . $a->stack, 10; #Movq and variants might be useful
	Mov 'qword' . $b->stack, 4; #NOTE: stack was broken here
	Mov rbx, $a->stack;
	Mov r9, $b->stack;
	Add rbx, r9;
	Mov rax, rbx;
	$vars->free;
}

my $locrut = S{add_2_locals;};
KeepFree(rbp, rsp, rax);
my $routine = S{add_5;};
Mov rdi,10;
Call $routine;
PrintOutRegisterInHex rax;
Call $locrut;
Mov rdx, rax;
PrintOutRegisterInHex rdx;
my $r = Assemble;
ok $r =~ m/rax: 0000 0000 0000 000F/;
ok $r =~ m/rdx: 0000 0000 0000 000E/;
done_testing;
