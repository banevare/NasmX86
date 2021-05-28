#Author: tino <gordon.zar@gmail.com>
use strict;
use warnings FATAL => qw(all);
use Nasm::X86 qw(:all);
use Test::Most tests => 1;

my $bytestr = CreateByteString;
my $blockstr = $bytestr->CreateBlockString;
my $blockarr = CreateBlockArray $bytestr;
note "Block array method check";
can_ok($blockarr, qw(address allocBlock dump get pop push put));
note "Block string method check";
can_ok($blockstr, qw(
address allocBlock append clear concatenate deleteChar dump getBlock
getBlockLengthInZmm getCharacter getNextAndPrevBlockOffsetFromZmm
insertChar len putBlock putNextandPrevBlockOffsetIntoZmm
setBlockLengthInZmm));
note "Byte string method check";
can_ok($bytestr, qw(
allocate append blockSize char clear dump getBlock length m makeReadOnly
makeWriteable nl out putBlock q ql rdiInHex read write z));
$bytestr->q('string');

my $v = Vq v, 2;

eval {$blockarr->push($bytestr->bs->name, $v)};
ok not($@), 'Block array push';
diag $@ if $@;
$blockarr->dump;
like Assemble, qr/Block Array/, 'Block array output';
