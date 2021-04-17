# Generate and run [x64](https://en.wikipedia.org/wiki/X86-64) [Advanced Vector Extensions](https://en.wikipedia.org/wiki/AVX-512) assembler programs from [Perl](http://www.perl.org/) 

![Test](https://github.com/philiprbrenan/Nasmx86/workflows/Test/badge.svg)


This [Perl](http://www.perl.org/) [module](https://en.wikipedia.org/wiki/Modular_programming) generates and runs [x64](https://en.wikipedia.org/wiki/X86-64) [Advanced Vector Extensions](https://en.wikipedia.org/wiki/AVX-512) assembler programs using [Perl](http://www.perl.org/) as
a powerful macro assembler. It contains methods to perform useful macro
functions such as dumping x/y/zmm* registers to facilitate the debugging of the
generated programs or interacting with the operating system.


The [GitHub Action](https://docs.github.com/en/free-pro-team@latest/actions/quickstart) in this repo shows how to [install](https://en.wikipedia.org/wiki/Installation_(computer_programs)) [nasm](https://github.com/netwide-assembler/nasm) and the [Intel Software Development Emulator](https://software.intel.com/content/www/us/en/develop/articles/intel-software-development-emulator.html) used
to assemble and then run the programs generated by this [module](https://en.wikipedia.org/wiki/Modular_programming). 

Test cases can be seen at the end of [file](https://en.wikipedia.org/wiki/Computer_file) **lib/Nasm/X86.pm**.  The [test](https://en.wikipedia.org/wiki/Software_testing) cases
are run by the [GitHub Action](https://docs.github.com/en/free-pro-team@latest/actions/quickstart). 

This [module](https://en.wikipedia.org/wiki/Modular_programming) is part of the Perl Zero project: using Perl 5 to create a minimal,
modern version of Perl which generates x86 assembler [code](https://en.wikipedia.org/wiki/Computer_program) directly. Perl Zero
is [process](https://en.wikipedia.org/wiki/Process_management_(computing)) friendly: every data structure used is completely [relocatable](https://en.wikipedia.org/wiki/Relocation_%28computing%29) and so
can be moved directly between different processes via a [file](https://en.wikipedia.org/wiki/Computer_file) or a socket. A
Perl Zero [program](https://en.wikipedia.org/wiki/Computer_program) is a single expression with no key words: only [user](https://en.wikipedia.org/wiki/User_(computing)) defined
infix operators and expressions are used to construct programs. Perl Zero
leverages Perl 5 as its macro assembler and CPAN as its [module](https://en.wikipedia.org/wiki/Modular_programming) repository.
Please feel free to join in.

# Useful links

- [Avx512 SIMD x86 instructions](https://www.officedaytime.com/simd512e/)

- [Linux system calls](https://filippo.io/linux-syscall-table/)

- [Linux error codes](https://www-numi.fnal.gov/offline_software/srt_public_context/WebDocs/Errors/unix_system_errors.html)

- [Network wide assembler](https://www.nasm.us/xdoc/2.15.05/html/nasmdoc0.html)

- [Intel emulator](https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2)

- [Ascii table](https://www.asciitable.com/)


# Avx512 instructions


Use [Advanced Vector Extensions](https://en.wikipedia.org/wiki/AVX-512) instructions to reorder data using 512 bit zmm registers:


```
  Start;
  my $q = Rs my $s = join '', ('a'..'p')x4;
  Mov rax, Ds('0'x128);

  Vmovdqu32 zmm0, "[$q]";
  Vprolq    zmm1, zmm0, 32;
  Vmovdqu32 "[rax]", zmm1;

  Mov rdi, length $s;
  PrintOutMemory;
  Exit;

  ok $s       =~ m(abcdefghijklmnopabcdefghijklmnopabcdefghijklmnopabcdefghijklmnop)s;
  ok Assemble =~ m(efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl)s;
```


# Dynamic string held in an [arena](https://en.wikipedia.org/wiki/Region-based_memory_management) 

Create a dynamic byte string, add some content to it, write the byte string to
a [file](https://en.wikipedia.org/wiki/Computer_file) and then execute it:

```
  Start;
  my $s = CreateByteString;                                                     # Create a string
  $s->ql(<<END);                                                                # Write [code](https://en.wikipedia.org/wiki/Computer_program) to execute
#!/usr/bin/bash
whoami
ls -la
pwd
END

  $s->write;                                                                    # Write [code](https://en.wikipedia.org/wiki/Computer_program) to a temporary [file](https://en.wikipedia.org/wiki/Computer_file) 
  $s->bash;                                                                     # Execute the temporary [file](https://en.wikipedia.org/wiki/Computer_file) 
  $s->unlink;                                                                   # Execute the temporary [file](https://en.wikipedia.org/wiki/Computer_file)   Exit;                                                                         # Return to operating system

  my $u = qx(whoami); chomp($u);
  ok Assemble =~ m($u);
```


# Process management


Start a child [process](https://en.wikipedia.org/wiki/Process_management_(computing)) and wait for it, printing out the [process](https://en.wikipedia.org/wiki/Process_management_(computing)) identifiers of
each [process](https://en.wikipedia.org/wiki/Process_management_(computing)) involved:


  ```
  Start;                                                                        # Start the [program](https://en.wikipedia.org/wiki/Computer_program)   Fork;                                                                         # Fork

  Test rax,rax;
  If                                                                            # Parent
   {Mov rbx, rax;
    WaitPid;
    PrintOutRegisterInHex rax;
    PrintOutRegisterInHex rbx;
    GetPid;                                                                     # Pid of parent as seen in parent
    Mov rcx,rax;
    PrintOutRegisterInHex rcx;
   }
  [sub](https://perldoc.perl.org/perlsub.html)                                                                           # Child
   {Mov r8,rax;
    PrintOutRegisterInHex r8;
    GetPid;                                                                     # Child pid as seen in child
    Mov r9,rax;
    PrintOutRegisterInHex r9;
    GetPPid;                                                                    # Parent pid as seen in child
    Mov r10,rax;
    PrintOutRegisterInHex r10;
   };

  Exit;                                                                         # Return to operating system

  my $r = Assemble;

  #    r8: 0000 0000 0000 0000   #1 Return from [fork](https://en.wikipedia.org/wiki/Fork_(system_call)) as seen by child
  #    r9: 0000 0000 0003 0C63   #2 Pid of child
  #   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
  #   rax: 0000 0000 0003 0C63   #4 Return from [fork](https://en.wikipedia.org/wiki/Fork_(system_call)) as seen by parent
  #   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
  #   rcx: 0000 0000 0003 0C60   #6 Pid of parent
  ```


# Read a [file](https://en.wikipedia.org/wiki/Computer_file) and print it out


Read this file and print it out:

  ```
  Start;                                                                        # Start the [program](https://en.wikipedia.org/wiki/Computer_program)   Mov rax, Rs($0);                                                              # File to read
  ReadFile;                                                                     # Read [file](https://en.wikipedia.org/wiki/Computer_file) 
  PrintOutMemory;                                                               # Print memory
  Exit;                                                                         # Return to operating system

  my $r = Assemble;                                                             # Assemble and execute
  ok index($r, readFile($0)) > -1;                                              # Output contains this [file](https://en.wikipedia.org/wiki/Computer_file)   ```
