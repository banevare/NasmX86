#Author: tino <gordon.zar@gmail.com>
#Test for defining custom calling convetion to, for example, enable interfacing with C library functions or other .asm files.
use strict;
use warnings;
use Nasm::X86 qw(:all);
use Test::Most tests => 1;

=pod

=head2 Test function macro for linux calling convention

=over

=item B<CallWithArgsX([$function_struct | 'label_string'], @arguments)>

  Call a function declared with 'Subroutine' or a function in the global namespace with linux x86_64 calling order convention

  my $function = Subroutine { ... } name => 'funname';
  CallWithArgsX $function, 1, 2, 3, 4;

  CallWithArgsX 'printf', < ... args ... >;


=back

=cut

sub CallWithArgsX($;@){
 my $sub = shift;
 my @order = (rdi, rsi, rcx, rdx, r8, r9);
 KeepFree @order;
 foreach(@_){
  Mov((shift @order), $_);
 }
 if(ref($sub)){
  Call $sub->start;
 }else{
  Call $sub; #should be subroutine name
 }
}

my $fun = Nasm::X86::Subroutine {
  PrintOutRegisterInHex rdi, rsi, rcx, rdx, r8, r9;
} name => 'argtest';

CallWithArgsX $fun, 1, 2, 3, 4;
CallWithArgsX $fun->start, 1, 2, 3, 4; # $fun->start returns a string with the symbol defining the function
is_deeply Assemble, <<END;
   rdi: 0000 0000 0000 0001
   rsi: 0000 0000 0000 0002
   rcx: 0000 0000 0000 0003
   rdx: 0000 0000 0000 0004
    r8: 0000 0000 0000 0000
    r9: 0000 0000 0000 0000
   rdi: 0000 0000 0000 0001
   rsi: 0000 0000 0000 0002
   rcx: 0000 0000 0000 0003
   rdx: 0000 0000 0000 0004
    r8: 0000 0000 0000 0000
    r9: 0000 0000 0000 0000
END
