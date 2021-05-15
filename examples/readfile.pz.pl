use strict;
use warnings;
use Nasm::X86 qw(:all);

Pop rax; #0000 0000 0000 0000
Pop rdx; #argc
Pop rax; #address to string of program being run
Pop rbx; #address of first argument to the program
Cmp rdx, 2;
IfEq{
	Mov rax, rbx;
	ReadFile; #rax = addr, rdi = length
	PrintOutMemory;
} sub {
	KeepFree rax, rdi;
	my $string = "'Supply a filename to display',10,0";
	Mov rax, Db $string;
	Mov rdi, length($string)-4;
	PrintOutMemory;	
};
Assemble keep => 'readfile';

