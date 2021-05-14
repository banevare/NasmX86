#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib/
#Testing of local data variables on the stack
# Tino 2021/05/14
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

if (1) {                                                                        #TLocalData #TLocalData::variable #TLocalData::free #TLocalData::start
  my $vars = LocalData;
  my $a = $vars->variable( 8,'a');                                              # Create an 8 byte variable 'a'
  my $b = $vars->variable( 1,'b');                                              # Create a 16 byte variable 'b'
  $vars->start;                                                                 # Allocate space on the stack for the variables
  Mov $a->stack, 10;                                                            # Initialize a
  Mov $b->stack,  4;                                                            # Initialize b
  Mov rax, $a->stack;                                                           # Get a
  Add  al, $b->stack;                                                           # Add b
  $vars->free;                                                                  # Free stack
  PrintOutRegisterInHex rax;                                                    # Print result

  is_deeply Assemble, <<END;                                                    # Assemble and run
   rax: 0000 0000 0000 000E
END
}
