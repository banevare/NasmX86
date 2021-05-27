#Author: tino <gordon.zar@gmail.com>
#Test calling of external C functions from the standard library
use strict;
use warnings;
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

my $format_string = Rs "Printf call: %s\n";
my $printf_argument = Rs 'Success';

Extern 'printf', 'exit';
Link 'c';

# according to the ABI docs, stack must be 16 byte aligned
# before calling a function
CallC 'printf', $format_string, $printf_argument;
CallC 'exit', 0;
is_deeply Assemble(keep=>'z'), "Printf call: Success", "Assemble output test";
my $r = qx(./z);
is $r, "Printf call: Success\n", "Output test";
# cleanup
unlink './z';
