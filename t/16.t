#Author: Tino <gordon.zar@gmail.com>
#Description: According to the docs, only 1 exit call should be present in the generated assembly code
#so we run a check because exit 0 is automatically added when not present
use strict;
use warnings;
use Test::Most tests => 2;
use Data::Table::Text qw(readFile);
use Nasm::X86 qw(:all);

if(1){ #TExit call duplication test
   Start;
   Mov rax,0;
   Exit 1;
   Assemble;
   my $assembly = readFile 'z.asm';
   note $assembly;
   ok $assembly =~ m/Exit code: 1/, 'Exit code 1 present';
   ok not($assembly =~ m/Exit code: 0/), "Exit code 0 must not be present when an Exit call exists already";
}
