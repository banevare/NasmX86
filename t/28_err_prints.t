use strict;
use warnings FATAL => qw(all);
use Nasm::X86 qw(:all);
use Test::Most tests => 3;
use Data::Table::Text qw(readFile);

if(1){                                                                              #TPrintErr* function tests
  my $errm = Rs my $errstr = "Memory error string";
  my $errm2 = Rs my $errstr2 = "Mer2";
  my $rm = Db 11;
  my $rm2 = Db 12;
  Mov rax, 0x0a;
  PushRR rax;
  KeepFree rax;
  Mov rax,0x0b;
  PopRR rax;
  PrintErrRaxInHex;
  PrintErrNL;
  PrintErrString 'Error string';
  KeepFree rax;
  Comment 'FIXME: Printing memory string to stderr';
  Mov rax, $errm;
  Mov rdi, length($errstr);
  PrintErrMemory;
  KeepFree rax, rdi
  PrintErrNL;
  Mov rax, $errm2;
  Mov rdi, length($errstr2);
  PrintErrMemoryNL;
  KeepFree rdi, rax;
  Mov rax, $rm;
  Mov rdi, 1;
  PrintErrMemoryInHex;
  KeepFree rdi, rax;
  Mov rax, $rm;
  Mov rdi, 1;
  PrintErrMemoryInHexNL;
  PrintErrRegisterInHex rdi;
  Assemble;
  my $erf = readFile('zzzErr.txt');
  like $erf, qr/000A\n/, 'Register value in stderr';
  like $erf, qr/Error string/, 'Error string in stderr';
  my $t3 = like $erf, qr/Memory error string\n/, 'Memory error string';
  !$t3 && diag "\n===\nWrong channel for memory error string\n===\n";
  like $erf, qr/000B0000[\d\s]*?000C/, 'Memory 15 in hex';
  like $erf, qr/\n\s+rdi: 0000 0000 0000 0001/, 'rdi stderr check';
  like $erf, qr/Mer2\n/, 'Memory error string 2';
}
