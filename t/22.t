#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
#Author: tino <gordon.zar@gmail.com>
#NOTE: This will be a large test. I will finish it when I get to it
#I keep some lines commented to remember what I tried
#Tino-TODO-<number> denotes a note to myself to remember to make a test case
use Test::Most tests => 5; #future plan is around 7-10 tests
use Nasm::X86 qw(:all);

if(1){                                                                         #TByteString reallocation test
SKIP:{
  skip 'bad test for interface change', 5;
  my $byte_str_addr = Vq 'bsa', 0;
  my $str = CreateByteString;                                                  # Create ByteString
#  my $dbg = CreateByteString;
#  $dbg->q('Before segfault');
#  $dbg->nl;
  $str->q('Simple string');
  $str->nl;                                                                    # Append new line
  Mov rbx,rax;                                                                 # New address of ByteString struct is in RAX, we move it to RBX for later
  Lea rsi, $str->data->addr;                                                   # Load address of string into RSI, should equal RBX
  #Mov rsi, $str->used->addr;                                                   # Load address of string into RSI, should equal RBX
  #Mov r11, $str->structure->variables->[0]->structure->variables->[2]->addr;
  #Lea r11, $str->structure->variables->[0]->structure->variables->[2]->addr;
  #Lea r11, $str->data->addr;
  explain $str;
#  explain $str->structure->variables->[0]->structure;
# Sub rsi,8;                                                                   #fixes address (commented out because this shouldn't be done here)
  Mov $byte_str_addr->address, rsi;                                            # Store address of RSI into memory
  Add rbx, 0x10;                                                               # Align pointer in rbx to address in rsi
  Cmp rbx, rsi;
  my $goodlabel = Label 'good_address';
  Jz $goodlabel;
  #=== bad address ===
  KeepFree rax;
  Mov rdx, $byte_str_addr->address;
  PrintOutRegisterInHex rbx, rsi, rdx;
  Mov rax, my $err = Db "'Bad address for byte string',10,0";
  Mov rdi, 29;
  PrintOutMemory;
  #=== good address ===
  SetLabel $goodlabel;
  KeepFree rax,rsi,rdi;                                                        # Free up registers up for use
  Mov rdi, 16;
# Uncomment to print 'Simple string\n'
#  Add rbx, 0x10;
#  Mov rax, rbx;
#  PrintOutMemory;
  Mov rax, $byte_str_addr->address;
  PrintOutMemory;
  $str->q('Appended text');                                                    # Append more text
  $str->nl;                                                                    # Append another new line
  $str->q('Even more text');                                                   # Append even more text
  $str->nl;                                                                    # Append another new line
# Tino-TODO-1: check if $str->used->addr contains the proper size
#  Mov $str->used->addr, rax;                                                  # Move the newly allocated address into the structure
  Add rax,0x10;                                                                # RAX contains begining of structure, adding 16 bytes points to the string
  KeepFree rax,rsi,rdi;                                                        # Free up registers up for use
  Mov rdi, 64;                                                                 # Move size into RDI
# Tino-TODO-2: check if new address is correct
#  Mov rax, $str->used->addr;                                                  # Move the new address into rax
  PrintOutMemory;                                                              # Print out string
  KeepFree rax;                                                                # Free up registers up for use
#  $dbg->out;
  Mov rax, $str->used->addr;                                                   #FIXME: This instruction causes a segfault when Tino-TODO-2 is uncommented
  Mov r10, $byte_str_addr->address;                                            # Move previous address into R10
  PrintOutRegisterInHex rax, r10;
  Cmp r10, rax;                                                                # Compare previous address with the new address
  my $failure = Label;                                                         # Create unique label
  Jz $failure;                                                                 # Jump if they are equal (address didnt change)
  KeepFree rax,rdi;                                                            # Free up registers
  Mov rax, my $s = Db "'Success',10,0";                                        # Allocate string with new line
  Mov rdi, 9;
  PrintOutMemory;                                                              # Print the string
  Exit 0;                                                                      # Successfull exit code
  SetLabel $failure;                                                           # Set failure label for branch
  KeepFree rax,rdi;                                                            # Free up registers again
  Mov rax, $s = Db "'Failure',10,0";                                           # Create another string
  Mov rdi, 9;
  PrintOutMemory;                                                              # Print string
  Exit 1;                                                                      # Failure exit code
  my $R = Assemble emulator => 0;
  ok $R =~ m/Success\n/, 'Reallocation address';                                                       # Assemble and check for success string
  ok $R =~ m/Simple string\n/, 'Output check with returned address';
  ok $R =~ m/Even more text\n/, 'Another output check after appending more text';
  ok $R !~ m/BAD MEMORY POINTER|Segmentation fault/, 'Check for a bad memory pointer dereference';
  ok $R !~ m/Bad address/, 'Check if rbx equals rsi where rsi is loaded with the interface method and rbx aligned from return value';
}
}

