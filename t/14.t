#Author: Tino <gordon.zar@gmail.com>
#Description: Testing of call frames and local variable assignment
use strict;
use warnings;
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

sub add_5{
	my $vars = LocalData;
	my $v = $vars->variable(8,'local_5');
	$vars->start;
	Mov $v->stack, 5;
	Add rdi, $v->stack;
	Mov rax,rdi;
	$vars->free;
}

sub add_2_locals{
	my $vars = LocalData;
	my $a = $vars->variable(8,'a');
	my $b = $vars->variable(8,'b');
	$vars->start;
	KeepFree(rax);
	Mov $a->stack, 10;
	Mov $b->stack, 4; #FIXME: call stack gets overwritten here
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
Exit 0; #generates duplicate code because the exit is automaticly generated
Assemble keep => 't14_tmp';
my $t14_out = qx(./t14_tmp);
isnt $?, 11, 'Segfault test';
print $? . "\n";
is_deeply $t14_out,<<END;
   rax: 0000 0000 0000 000F
   rdx: 0000 0000 0000 000E
END
unlink 't14_tmp';


done_testing;
