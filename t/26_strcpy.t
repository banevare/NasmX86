use strict;
use warnings FATAL => qw(all);
use Test::Most tests => 4;
use Nasm::X86 qw(:all);

my $format = Rs "Hello %s\n";
my $data   = Rs "World";

note "Export Checks\n";
can_ok('main', 'Mov');
can_ok('main', qw(CallC Extern Link));
Nasm::X86::Extern qw(printf exit malloc strcpy); Nasm::X86::Link 'c';

Nasm::X86::CallC 'malloc', length($format)+1;
Mov r15, rax;
Nasm::X86::CallC 'strcpy', r15, $format;
Nasm::X86::CallC 'printf', r15, $data;
Nasm::X86::CallC 'exit', 0;

ok Assemble(eq => <<END);
Hello World
END
