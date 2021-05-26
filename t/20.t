#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
#Author: tino <gordon.zar@gmail.com>
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

my $str = CreateByteString;
$str->q('Simple string');
$str->nl;
$str->out;

is_deeply Assemble, <<END;
Simple string
END
