#Author: tino <gordon.zar@gmail.com>
use strict;
use warnings;
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

my $str = CreateByteString;
$str->q('Simple string');
$str->nl;
$str->out;
ok Assemble =~ m/Simple string\n/;
#NOTE: I will expand on these tests later
