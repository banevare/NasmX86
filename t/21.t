#Author: tino <gordon.zar@gmail.com>

use strict;
use warnings;
use Test::Most tests => 2;
use Nasm::X86 qw(:all);

if(1){                                                                         #TLocalData simple addition operator overloading test
  my $l = LocalData;
  my $a = $l->variable(8, 'a');                                                # Declare variables 
  my $b = $l->variable(8, 'b');
  my $c = $l->variable(8, 'c');
  $l->start;                                                                   # Emit stack variable constrution instructions
  Mov rax,-1;                                                                  # Initialize rax
  Mov $a->stack, 10;                                                           # Initialize variables
  Mov $b->stack, 1;
  $c = $a + $b;                                                                # Perform operator overload addition test
  if(can_ok($c,'stack')){                                                      # Check if $c has the 'stack' method
    KeepFree rax;
    Mov rax, $c->stack;                                                        # If so, load result into rax
  }else{
    diag "\$c result variable contains strange result: $c";                    # Else report issue
  }
  PrintOutRegisterInHex rax;                                                   # If test was successfull, rax will contain 0x0B
  is_deeply Assemble, <<END;
   rax: 0000 0000 0000 000B
END
  done_testing;
}
