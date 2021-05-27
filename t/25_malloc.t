#Author: tino <gordon.zar@gmail.com
#Allocate, write, read, and free memory with the help of malloc
use strict;
use warnings FATAL => qw(all);
use Test::Most tests => 2;
use Nasm::X86 qw(:all Extern);

Extern 'printf', 'malloc', 'exit', 'free';
Link 'c';

my $format_string = Rs "New memory block: %p\n";
my $value_check_f = Rs "Value in memory: 0x%x\n";

CallC 'malloc', 64;
Mov r12, rax;
CallC 'printf', $format_string, rax;
Mov 'qword['.r12.']', 0xabcdef;
Mov rdx, 'qword['.r12.']';
CallC 'printf', $value_check_f, rdx;
CallC 'free', r12;
CallC 'exit', 0;
my $r = Assemble;
like $r, qr/New memory block: 0x[a-f0-9]+/;
like $r, qr/Value in memory: 0xabcdef/;
