#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib/
#Testing of local data variables on the stack
# Tino 2021/05/14
use Test::Most tests => 1;
use Nasm::X86 qw(:all);

if (1) {                                                                        #TLocalData #TLocalData::variable #TLocalData::free #TLocalData::start
  my $vars = LocalData;
  my $a = $vars->variable( 8,'a');                                              # Create an 8 byte variable 'a'
  my $b = $vars->variable( 1,'b');                                              # Create an 1 byte variable 'b'
  my $c = $vars->variable( 2,'c');                                              # Create an 2 byte variable 'c' 
  my $d = $vars->variable( 4,'c');                                              # Create an 4 byte variable 'd' 
  $vars->start;                                                                 # Allocate space on the stack for the variables
  Mov $a->stack, 10;                                                            # Initialize a
  Mov $b->stack,  4;                                                            # Initialize b
  Mov $c->stack,  0x1E;                                                         # Initialize c
  Mov $d->stack,  0x02;                                                         # Initialize d
  Mov rax, $a->stack;                                                           # Get a
  Add al, $b->stack;                                                            # Add b
  Mov bx, $c->stack;                                                            # Get c 
  Add ebx, $d->stack;                                                           # Add d 
  $vars->free;                                                                  # Free stack
  PrintOutRegisterInHex rax;                                                    # Print rax result
  PrintOutRegisterInHex rbx;                                                    # Print rbx result

  is_deeply Assemble, <<END;                                                    # Assemble and run
   rax: 0000 0000 0000 000E
   rbx: 0000 0000 0000 0020
END
}
