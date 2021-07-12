#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/
#-------------------------------------------------------------------------------
# Find all 13 Unicode Mathematical Alphabets as used by Perl Zero.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
use warnings FATAL => qw(all);
use strict;
use Carp;
use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use Test::More qw(no_plan);
use Tree::Term;
use feature qw(say state current_sub);
use utf8;

my $home    = currentDirectory;                                                 # Home folder
my $unicode = q(https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt); # Unicode specification
my $data    = fpe $home, qw(unicode txt);                                       # Local copy of unicode
my $lexicalsFile = fpe $home, qw(lex data);                                     # Dump of lexicals

=pod

Space processing - remove leading and trailing spaces
New line as semi colon when new line occurs after a variable
Alphabet compression so we can make better use of Tree:Multi
Text generation routine let us write some pretend code to parse

=cut

my $bracketBase = 0x10;                                                         # Start numbering brackets from here

sub LexicalConstant($$;$)                                                       # Lexical constants as opposed to derived values
 {my ($name, $number, $letter, $like) = @_;                                     # Name of the lexical item, numeric code as used in Nida, character code as used Tree::Term, a specialized instance of this Tree::Term which is never the less lexically identical to the Tree::Term
  genHash("Nida::Lexical::Constant",                                            # Description of a lexical item connecting the definition in Tree::Term with that in Nida::Lexicals
    name   => $name,                                                            #I Name of the lexical item
    number => $number,                                                          #I Numeric code for lexical item
    letter => $letter,                                                          #I Alphabetic name for lexical item
   );
 }

my $Lexicals = genHash("Nida::Lexicals",                                        # Lexical items
  OpenBracket      => LexicalConstant("OpenBracket",       0, 'b'),             # The lowest bit of an open bracket code is zero
  CloseBracket     => LexicalConstant("CloseBracket",      1, 'B'),             # The lowest bit of a close bracket code is one
  Ascii            => LexicalConstant("Ascii",             2, 'v'),             # Ascii characters
  NewLine          => LexicalConstant("NewLine",           3, 'v'),             # New line character
  dyad             => LexicalConstant("dyad",              4, 'd'),             # Infix operator with left to right binding at priority 3
  prefix           => LexicalConstant("prefix",            5, 'p'),             # Prefix operator - it applies only to the following variable
  assign           => LexicalConstant("assign",            6, 'a'),             # Assign infix operator with right to left binding at priority 2.
  variable         => LexicalConstant("variable",          7, 'v'),             # Variable although it could also be an ascii string or regular expression
  suffix           => LexicalConstant("suffix",            8, 'q'),             # Suffix operator - it applies only to the preceding variable
  semiColon        => LexicalConstant("semiColon",         9, 's'),             # Infix operator with left to right binding at priority 1
  NewLineSemiColon => LexicalConstant("NewLineSemiColon", 10),                  # A new line character that is also acting as a semi colon
  WhiteSpace       => LexicalConstant("WhiteSpace",       11),                  # White space between non ascii items
  Term             => LexicalConstant("Term",             12),                  # Term in the parse tree
 );

my $TreeTermLexicals = genHash("Nida::TreeTermLexicals",                        # Tree Term Lexical items embodied as Nida lexical items
  a => "assign",
  d => "dyad",
  b => "OpenBracket",
  B => "CloseBracket",
  p => "prefix",
  s => "semiColon",
  q => "suffix",
  v => "variable",
 );

my $Tables = genHash("Nida::Lexical::Tables",                                   # Tables used to parse lexical items
  alphabets        => undef,                                                    # Alphabets selected from uncode database
  alphabetRanges   => undef,                                                    # Number of alphabet ranges
  brackets         => undef,                                                    # Number of brackets
  bracketsHigh     => undef,                                                    # High zmm for closing brackets
  bracketsLow      => undef,                                                    # Low  zmm for opening brackets
  bracketsOpen     => undef,                                                    # Open brackets
  bracketsClose    => undef,                                                    # Close brackets
  lexicalAlpha     => undef,                                                    # The alphabets assigned to each lexical item
  lexicalHigh      => undef,                                                    # High zmm for lexical items
  lexicalLow       => undef,                                                    # Low  zmm for lexical items
  lexicals         => $Lexicals,                                                # The lexical items
  sampleText       => undef,                                                    # A sample Nida program
  transitions      => undef,                                                    # Zmm of transition possibilities
  treeTermLexicals => $TreeTermLexicals,                                        # Tree term lexicals
 );

if (!-e $data)                                                                  # Download specification
 {say STDERR qx(curl -o $data $unicode);
 }

sub convert($)                                                                  # Convert a character from hex to actual
 {my ($c) = @_;                                                                 # Parameters
  eval "chr(0x$c)";                                                             # Character
 }

sub alphabets                                                                   # Locate the mathematical alphabets
 {my @s = readFile $data;

  my %alpha;                                                                    # Alphabet names

  for my $s(@s)                                                                 # Select the brackets we want
   {my @w = split /;/, $s;

# 1D49C;MATHEMATICAL SCRIPT CAPITAL A;Lu;0;L;<font> 0041;;;;N;;;;;
# 1D72D;MATHEMATICAL BOLD ITALIC CAPITAL THETA SYMBOL;Lu;0;L;<font> 03F4;;;;N;;;;;
# 1D70D;MATHEMATICAL ITALIC SMALL FINAL SIGMA;Ll;0;L;<font> 03C2;;;;N;;;;;

    my ($c, $d, $t) = @w;                                                       # Parse unicode specification
    my $C = convert $c;                                                         # Character

    next if     $d =~ m(DIGAMMA)i;                                              # Select family of letters
    next unless $d =~ m(\A(Mathematical|Squared|Circled|Negative))i;            # Select family of letters
    next unless $t =~ m(\A(L|So|Sm));                                           # Letter or other symbol

    my $D = $d;
       $D =~ s(PARTIAL DIFFERENTIAL) ( )igs;
       $D =~ s(NABLA)                ( )igs;
       $D =~ s(\w+ SYMBOL\Z)         ( )ig;
       $D =~ s(FINAL \w+\Z)          ( )ig;
       $D =~ s(\w+\Z)                ( )gs;
       $D =~ s(Capital)              ( )igs;
       $D =~ s(Small)                ( )igs;
       $D =~ s(\s+)                  ( )igs;

    $alpha{$D}{$c} = $C;                                                        # Place into alphabets
   }

  my %selected;                                                                 # Selected alphabets
     $selected{semiColon} = q(⟢);                                               # We cannot use semi colon as it is an ascii character, so we use this character instead  U+27E2

  for my $a(sort keys %alpha)
   {next unless $a =~ m((CIRCLED LATIN LETTER|MATHEMATICAL BOLD|MATHEMATICAL BOLD FRAKTUR|MATHEMATICAL BOLD ITALIC|MATHEMATICAL BOLD SCRIPT|MATHEMATICAL DOUBLE-STRUCK|MATHEMATICAL FRAKTUR|MATHEMATICAL ITALIC|MATHEMATICAL MONOSPACE|MATHEMATICAL SANS-SERIF|MATHEMATICAL SANS-SERIF BOLD|MATHEMATICAL SANS-SERIF|BOLD ITALIC|MATHEMATICAL SANS-SERIF ITALIC|MATHEMATICAL SCRIPT|NEGATIVE|CIRCLED LATIN LETTER|NEGATIVE SQUARED LATIN LETTER|SQUARED LATIN LETTER))i;
                                                                                # Selected alphabets
    my @l;
    for my $l(sort keys $alpha{$a}->%*)                                         # Sort alphabet by point
     {push @l, $alpha{$a}{$l};
     }
    my $l = join '', sort @l;                                                   # Alphabet

    next unless length($l) > 5;                                                 # Ignore short sets which are probably not alphabets
    my $A = lcfirst join '', map {ucfirst} split /\s+/, lc $a;
    $selected{$A} = $l;                                                         # Selected alphabets
   }

  #lll "AAAA", dump(\%alpha);                                                   # Alphabets discovered

  my @range;  my @zmm;                                                          # Ranges of characters

  for my $a(sort keys %selected)                                                # Print selected alphabets in ranges
   {my $z = '';
       $z = q(variable) if $a =~ m/mathematicalSans-serifBold\Z/;
       $z = q(dyad)     if $a =~ m/mathematicalBold\Z/;
       $z = q(prefix)   if $a =~ m/mathematicalBoldItalic\Z/;
       $z = q(assign)   if $a =~ m/mathematicalItalic\Z/;
       $z = q(suffix)   if $a =~ m/mathematicalSans-serifBoldItalic\Z/;
       $z = q(Ascii)    if $a =~ m/negativeCircledLatinLetter\Z/;               # Control characters as used in regular expressions and quoted strings

    push $Tables->lexicalAlpha->{$z}->@*, $a;                                   # Alphabets assigned to each lexical item

    my $Z = $z ? pad(" = $z", 16) : '';
    if ($z)                                                                     # Alphabet we are going to use for a lexical item
     {say STDERR '-' x 44;
      say STDERR pad("$a$Z", 42), " : ", $selected{$a};
      say STDERR '-' x 44;
     }
    else
     {say STDERR pad("$a$Z", 42), " : ", $selected{$a};
     }

    my @c = split //, $selected{$a};                                            # Divide selected alphabets into contiguous ranges
    push my @r, [shift @c];

    for my $c(@c)
     {my $b = ord($r[-1][-1]);
      if (ord($c) == $b + ($b == 0x1d454 ? 2 : 1))
       {push $r[-1]->@*, $c;
       }
      else
       {push @r, [$c];
       }
     }

    if ($z)                                                                     # Write ranges ready to load into zmm registers
     {for my $i(keys @r)
       {my $r = $r[$i];
        my $j = $i + 1;
        my $s = ord($$r[0]);                                                    # Start of range
        my $l = ord($$r[-1]);                                                   # End of range
        say STDERR "Range $j: ",
          sprintf("0x%x to 0x%x length: %2d", $s, $l, $l - $s + 1);
        push @range, [$z,  $s, $l];
        push @zmm,   [$z, $$Lexicals{$z}->number, $s, $l];
       }
     }
   }
#             0               1                                     2       3
  push @zmm, ["NewLine",      $Lexicals->NewLine  ->number,        10,     10]; # Add other stuff to look for while we are making the pass through the source as we have 16 slots in the zmm
  push @zmm, ["Ascii",        $Lexicals->Ascii    ->number,         0,    127];
  push @zmm, ["semiColon",    $Lexicals->semiColon->number,    0x27E2, 0x27E2];
  @zmm = sort {$$a[3] <=> $$b[3]} @zmm;

  $Tables->alphabetRanges = scalar(@zmm);                                       # Alphabet ranges
  lll "Alphabet Ranges: ",  scalar(@zmm);
  say STDERR dump(\@zmm);

  if (1)                                                                        # Write zmm load sequence
   {my @l; my @h; my %r;                                                        # Low, high, current start within range
    for my $r(@zmm)
     {my $l = $r{$$r[0]}//0;                                                    # Current start of range

      push @l, (($$r[1]<<24) + $$r[2]);                                         # Start of range in high and lexical item in low at byte 3 allows us to replace the utf32 code with XX....YY where XX is the lexical item type and YY is the position in the range of that lexical item freeing the two central bytes for other purposes
      push @h, (($l    <<24) + $$r[3]);
      $r{$$r[0]} += ($$r[3] - $$r[2]) + 1;                                      # Extend the base of the current range
     }

    push @l, 0 while @l < 16;                                                   # Clear remaining ranges
    push @h, 0 while @h < 16;
    my $l = join ', ', map {sprintf("0x%08x", $_)} @l;                          # Format zmm load sequence
    my $h = join ', ', map {sprintf("0x%08x", $_)} @h;
    say STDERR "Lexical Low / Lexical High:\n$l\n$h";
    $Tables->lexicalLow  = [@l];
    $Tables->lexicalHigh = [@h];
   }

  $Tables->alphabets = \%selected;
 }

sub brackets                                                                    # Write brackets
 {my @S;

  my @s = readFile $data;

  for my $s(@s)                                                                 # Select the brackets we want
   {next unless $s =~ m(;P[s|e];)i;                                             # Select brackets
    my @w = split m/;/, $s;

    my ($point, $name) = @w;
    my $u = eval "0x$point";
    $@ and confess "$s\n$@\n";

    next if $u <= 0x208e;
    next if $u >=  9121 and  $u <=  9137;
    next if $u >= 11778 and  $u <= 11815;
    next if $u >= 12300 and  $u <= 12303;
    next if $u >= 65047 and  $u <= 65118 ;
    next if $u >= 65378;

    next if $u >= 0x27C5 and $u <= 0x27C6;                                      # Bag
    next if $u >= 0x29D8 and $u <= 0x29D9;                                      # Wiggly fence
    next if $u >= 0x29DA and $u <= 0x29Db;                                      # Double Wiggly fence
    next if $u == 0x2E42;                                                       # Double Low-Reversed-9 Quotation Mark[1]
    next if $u >= 0x301D and $u <= 0x3020;                                      # Quotation marks

    push @S, [$u, $name, $s];
   }

  @S % 2 and confess "Mismatched bracket pairs";
  lll "Bracket Pairs: ", scalar(@S) / 2;

  my ($T, @T) = @S;                                                             # Divide into ranges
  push my @t, [$T];
  for my $t(@T)
   {my ($u, $point, $name) = @$t;
    if ($$T[0] + 1 == $u)
     {push $t[-1]->@*, $T = $t;
      next;
     }
    push @t, [$T = $t];
   }

  @t = grep {@$_ > 1} @t;                                                       # Remove small blocks so we can fit into one zmm

  if (1)                                                                        # Bracket strings
   {my @o; my @c;
    my $i = 0;
    for   my $r(@t)
     {for my $t(@$r)
       {push @o, chr $$t[0] unless $i % 2;
        push @c, chr $$t[0] if     $i % 2;
        ++$i;
       }
     }

    if (0)                                                                      # Print every bracket pair
     {for my $i(keys @o)
       {lll "Bracket pair $i", $o[$i], $c[$i], ord($o[$i]), ord($c[$i]);
       }
     }

    $Tables->bracketsOpen  = [@o];                                              # Brackets list
    $Tables->bracketsClose = [@c];
   }

  my @l; my @h;
  my $index = $bracketBase;
  for my $t(@t)                                                                 # Load zmm0, zmm1
   {if (@$t > 1)
     {push @l, sprintf("0x%08x", $$t[0] [0] + ($index<<24));
      $index += scalar(@$t) - 1;
      push @h, sprintf("0x%08x", $$t[-1][0] + ($index<<24));
     }
    elsif ($$t[-1][-1] =~ m(LEFT))                                              # Single range left
     {++$index if $index % 2;
      push @l, sprintf("0x%08x", $$t[0] [0] + ($index<<24));
      push @h, sprintf("0x%08x", $$t[0] [0] + ($index<<24));
     }
    else                                                                        # Single range right
     {++$index unless $index % 2;
      push @l, sprintf("0x%08x", $$t[0] [0] + ($index<<24));
      push @h, sprintf("0x%08x", $$t[0] [0] + ($index<<24));
     }
    $index += 1;
   }
  push @l, 0 while @l < 16;
  push @h, 0 while @h < 16;
  $Tables->brackets = @l;                                                       # Number of brackets
  lll "Bracket ranges: ", scalar(@l);

  my $L = join '', join(', ',  @l);
  my $H = join '', join(', ',  @h);
  say STDERR "$L\n$H";

  $Tables->bracketsLow  = [@l];
  $Tables->bracketsHigh = [@h];
 }

sub transitions                                                                 # Write transitions table
 {my @l;
  for my $l(sort keys $Lexicals->%*)                                            # Each lexical item that could appear in a transition becuase it is like a Tree::Term
   {my $L = $$Lexicals{$l};
    next unless $L->letter;
    push @l, $L;
   }

  my $next = Tree::Term::LexicalStructure()->next;                              # The permitted transitions as letters

  my %t;
  for my $l1(@l)                                                                # Transitions on numbers
   {my $a = $l1->letter;
    my $A = $$next{$a};
    for my $l2(@l)
     {my $b = $l2->letter;
      next unless index($A, $b) > -1;
      $t{$l1->number}{$l2->number} = "$a$b";
     }
   }

  if (1)                                                                        # Load transitions
   {my $n = 0;                                                                  # Number of transitions
    my @t;                                                                      # Transitions
    for   my $t1(keys %t)
     {for my $t2(keys $t{$t1}->%*)
       {++$n;
        push @t, $t1 + ($t2 << 4);                                              # Encode transitions
       }
     }
    lll "Number of transitions = $n";
    $Tables->transitions = [@t];
    lll join ', ', map{sprintf("0x%02x", $_)} @t;
   }
 }

sub translateSomeText($)                                                        # Translate some text
 {my ($s) = @_;                                                                 # String to translate
  my @w = (substr($s, 0, 1));
  for my $i(1..length($s))                                                      # Parse into strings of letters and spaces
   {my $b = join '', sort split //, substr($s, $i - 1, 2) =~ s(\S) (a)gsr  =~ s(\s) ( )gsr;
    my $c = substr($s, $i, 1);
    if ($b ne ' a')
     {$w[-1] .= $c;
     }
    else
     {push @w, $c;
     }
   }

  my %alphabets;                                                                # Alphabets for each lexical

  for my $l(keys $TreeTermLexicals->%*)
   {my $m = $TreeTermLexicals->{$l};
    my $n = $Tables->lexicalAlpha->{$m}[0];
    next unless $n;
    my $a = $Tables->alphabets->{$n};
    next unless $a;
    $alphabets{$l} = [$n, $a];
   }

  my $T = '';
  my $normal = join '', 'A'..'Z', 'a'..'z';                                     # The alphabet we can write lexical items

  my sub translate($)                                                           # Translate a string written in normal into the indicated alphabet
   {my ($lexical) = @_;                                                         # Lexical item to translate

    my $a =  $alphabets{substr($lexical, 0, 1)};                                # Alphabet to translate to
    my @a =   split //, $$a[1];                                                 # Alphabet to translate to
    for my $c(split //, substr($lexical, 1))
     {my $i = index $normal, $c;
      if ($$a[0] =~ m(\AmathematicalItalic\Z))
       {$c eq 'h' and confess "Cannot translate 'h' to $$a[0]";
        --$i if $c ge 'h';
       }
      $T .= $a[$i];
     }
   }

  for my $w(@w)
   {my $t = substr($w, 0, 1); my $r = substr($w, 1);
    if ($t =~ m(\A(a|d|v)\Z)) {translate $w}
    elsif ($t eq 's')         {$T .= $Tables->alphabets->{semiColon}}
    elsif ($t eq 'b')         {$T .= $Tables->bracketsOpen ->[$r]}
    elsif ($t eq 'B')         {$T .= $Tables->bracketsClose->[$r]}
    elsif ($t =~ m(\s))       {$T .= $w}
    elsif ($t eq 'A')         {$T .= substr($w, 1) =~ s(-) (\n)gsr}
    else {confess "Invalid lexical item $s"}
   }

  lll "Sample text length in chars:", sprintf("0x%x", length($T));

  if (0)                                                                        # Print source code as utf8
   {my @T = split //, $T;
    for my $i(keys @T)
     {my $c = $T[$i];
      say STDERR "$i   $c ", sprintf("%08x   %08x", ord($c), convertUtf32ToUtf8(ord($c)));
     }
   }

  lll "Sample text:\n$T";
  $Tables->sampleText = $T;
 }

alphabets;                                                                      # Locate alphabets
brackets;                                                                       # Locate brackets
transitions;                                                                    # Transitions table
translateSomeText <<END;                                                        # Translate some text into Nida
va aassign b1 b2 b3 vbp B3 B2  dplus b4 vsc B4 B1 s
vaa
  aassign
  Asome--ascii--text
  dplus
  vcc s
END

dumpFile($lexicalsFile, $Tables);                                               # Write lexical tables

__DATA__
CIRCLED LATIN LETTER  : ⒶⒷⒸⒹⒺⒻⒼⒽⒾⒿⓀⓁⓂⓃⓄⓅⓆⓇⓈⓉⓊⓋⓌⓍⓎⓏⓐⓑⓒⓓⓔⓕⓖⓗⓘⓙⓚⓛⓜⓝⓞⓟⓠⓡⓢⓣⓤⓥⓦⓧⓨⓩ
MATHEMATICAL BOLD  : 𝐀𝐁𝐂𝐃𝐄𝐅𝐆𝐇𝐈𝐉𝐊𝐋𝐌𝐍𝐎𝐏𝐐𝐑𝐒𝐓𝐔𝐕𝐖𝐗𝐘𝐙𝐚𝐛𝐜𝐝𝐞𝐟𝐠𝐡𝐢𝐣𝐤𝐥𝐦𝐧𝐨𝐩𝐪𝐫𝐬𝐭𝐮𝐯𝐰𝐱𝐲𝐳𝚨𝚩𝚪𝚫𝚬𝚭𝚮𝚯𝚰𝚱𝚲𝚳𝚴𝚵𝚶𝚷𝚸𝚺𝚻𝚼𝚽𝚾𝚿𝛀𝛂𝛃𝛄𝛅𝛆𝛇𝛈𝛉𝛊𝛋𝛌𝛍𝛎𝛏𝛐𝛑𝛒𝛔𝛕𝛖𝛗𝛘𝛙𝛚𝟊𝟋
MATHEMATICAL BOLD FRAKTUR  : 𝕬𝕭𝕮𝕯𝕰𝕱𝕲𝕳𝕴𝕵𝕶𝕷𝕸𝕹𝕺𝕻𝕼𝕽𝕾𝕿𝖀𝖁𝖂𝖃𝖄𝖅𝖆𝖇𝖈𝖉𝖊𝖋𝖌𝖍𝖎𝖏𝖐𝖑𝖒𝖓𝖔𝖕𝖖𝖗𝖘𝖙𝖚𝖛𝖜𝖝𝖞𝖟
MATHEMATICAL BOLD ITALIC  : 𝑨𝑩𝑪𝑫𝑬𝑭𝑮𝑯𝑰𝑱𝑲𝑳𝑴𝑵𝑶𝑷𝑸𝑹𝑺𝑻𝑼𝑽𝑾𝑿𝒀𝒁𝒂𝒃𝒄𝒅𝒆𝒇𝒈𝒉𝒊𝒋𝒌𝒍𝒎𝒏𝒐𝒑𝒒𝒓𝒔𝒕𝒖𝒗𝒘𝒙𝒚𝒛𝜜𝜝𝜞𝜟𝜠𝜡𝜢𝜣𝜤𝜥𝜦𝜧𝜨𝜩𝜪𝜫𝜬𝜮𝜯𝜰𝜱𝜲𝜳𝜴𝜶𝜷𝜸𝜹𝜺𝜻𝜼𝜽𝜾𝜿𝝀𝝁𝝂𝝃𝝄𝝅𝝆𝝈𝝉𝝊𝝋𝝌𝝍𝝎
MATHEMATICAL BOLD SCRIPT  : 𝓐𝓑𝓒𝓓𝓔𝓕𝓖𝓗𝓘𝓙𝓚𝓛𝓜𝓝𝓞𝓟𝓠𝓡𝓢𝓣𝓤𝓥𝓦𝓧𝓨𝓩𝓪𝓫𝓬𝓭𝓮𝓯𝓰𝓱𝓲𝓳𝓴𝓵𝓶𝓷𝓸𝓹𝓺𝓻𝓼𝓽𝓾𝓿𝔀𝔁𝔂𝔃
MATHEMATICAL DOUBLE-STRUCK  : 𝔸𝔹𝔻𝔼𝔽𝔾𝕀𝕁𝕂𝕃𝕄𝕆𝕊𝕋𝕌𝕍𝕎𝕏𝕐𝕒𝕓𝕔𝕕𝕖𝕗𝕘𝕙𝕚𝕛𝕜𝕝𝕞𝕟𝕠𝕡𝕢𝕣𝕤𝕥𝕦𝕧𝕨𝕩𝕪𝕫
MATHEMATICAL FRAKTUR  : 𝔄𝔅𝔇𝔈𝔉𝔊𝔍𝔎𝔏𝔐𝔑𝔒𝔓𝔔𝔖𝔗𝔘𝔙𝔚𝔛𝔜𝔞𝔟𝔠𝔡𝔢𝔣𝔤𝔥𝔦𝔧𝔨𝔩𝔪𝔫𝔬𝔭𝔮𝔯𝔰𝔱𝔲𝔳𝔴𝔵𝔶𝔷
MATHEMATICAL ITALIC  : 𝐴𝐵𝐶𝐷𝐸𝐹𝐺𝐻𝐼𝐽𝐾𝐿𝑀𝑁𝑂𝑃𝑄𝑅𝑆𝑇𝑈𝑉𝑊𝑋𝑌𝑍𝑎𝑏𝑐𝑑𝑒𝑓𝑔𝑖𝑗𝑘𝑙𝑚𝑛𝑜𝑝𝑞𝑟𝑠𝑡𝑢𝑣𝑤𝑥𝑦𝑧𝛢𝛣𝛤𝛥𝛦𝛧𝛨𝛩𝛪𝛫𝛬𝛭𝛮𝛯𝛰𝛱𝛲𝛴𝛵𝛶𝛷𝛸𝛹𝛺𝛼𝛽𝛾𝛿𝜀𝜁𝜂𝜃𝜄𝜅𝜆𝜇𝜈𝜉𝜊𝜋𝜌𝜎𝜏𝜐𝜑𝜒𝜓𝜔
MATHEMATICAL MONOSPACE  : 𝙰𝙱𝙲𝙳𝙴𝙵𝙶𝙷𝙸𝙹𝙺𝙻𝙼𝙽𝙾𝙿𝚀𝚁𝚂𝚃𝚄𝚅𝚆𝚇𝚈𝚉𝚊𝚋𝚌𝚍𝚎𝚏𝚐𝚑𝚒𝚓𝚔𝚕𝚖𝚗𝚘𝚙𝚚𝚛𝚜𝚝𝚞𝚟𝚠𝚡𝚢𝚣
MATHEMATICAL SANS-SERIF  : 𝖠𝖡𝖢𝖣𝖤𝖥𝖦𝖧𝖨𝖩𝖪𝖫𝖬𝖭𝖮𝖯𝖰𝖱𝖲𝖳𝖴𝖵𝖶𝖷𝖸𝖹𝖺𝖻𝖼𝖽𝖾𝖿𝗀𝗁𝗂𝗃𝗄𝗅𝗆𝗇𝗈𝗉𝗊𝗋𝗌𝗍𝗎𝗏𝗐𝗑𝗒𝗓
MATHEMATICAL SANS-SERIF BOLD  : 𝗔𝗕𝗖𝗗𝗘𝗙𝗚𝗛𝗜𝗝𝗞𝗟𝗠𝗡𝗢𝗣𝗤𝗥𝗦𝗧𝗨𝗩𝗪𝗫𝗬𝗭𝗮𝗯𝗰𝗱𝗲𝗳𝗴𝗵𝗶𝗷𝗸𝗹𝗺𝗻𝗼𝗽𝗾𝗿𝘀𝘁𝘂𝘃𝘄𝘅𝘆𝘇𝝖𝝗𝝘𝝙𝝚𝝛𝝜𝝝𝝞𝝟𝝠𝝡𝝢𝝣𝝤𝝥𝝦𝝨𝝩𝝪𝝫𝝬𝝭𝝮𝝰𝝱𝝲𝝳𝝴𝝵𝝶𝝷𝝸𝝹𝝺𝝻𝝼𝝽𝝾𝝿𝞀𝞂𝞃𝞄𝞅𝞆𝞇𝞈
MATHEMATICAL SANS-SERIF BOLD ITALIC  : 𝘼𝘽𝘾𝘿𝙀𝙁𝙂𝙃𝙄𝙅𝙆𝙇𝙈𝙉𝙊𝙋𝙌𝙍𝙎𝙏𝙐𝙑𝙒𝙓𝙔𝙕𝙖𝙗𝙘𝙙𝙚𝙛𝙜𝙝𝙞𝙟𝙠𝙡𝙢𝙣𝙤𝙥𝙦𝙧𝙨𝙩𝙪𝙫𝙬𝙭𝙮𝙯𝞐𝞑𝞒𝞓𝞔𝞕𝞖𝞗𝞘𝞙𝞚𝞛𝞜𝞝𝞞𝞟𝞠𝞢𝞣𝞤𝞥𝞦𝞧𝞨𝞪𝞫𝞬𝞭𝞮𝞯𝞰𝞱𝞲𝞳𝞴𝞵𝞶𝞷𝞸𝞹𝞺𝞼𝞽𝞾𝞿𝟀𝟁𝟂
MATHEMATICAL SANS-SERIF ITALIC  : 𝘈𝘉𝘊𝘋𝘌𝘍𝘎𝘏𝘐𝘑𝘒𝘓𝘔𝘕𝘖𝘗𝘘𝘙𝘚𝘛𝘜𝘝𝘞𝘟𝘠𝘡𝘢𝘣𝘤𝘥𝘦𝘧𝘨𝘩𝘪𝘫𝘬𝘭𝘮𝘯𝘰𝘱𝘲𝘳𝘴𝘵𝘶𝘷𝘸𝘹𝘺𝘻
MATHEMATICAL SCRIPT  : 𝒜𝒞𝒟𝒢𝒥𝒦𝒩𝒪𝒫𝒬𝒮𝒯𝒰𝒱𝒲𝒳𝒴𝒵𝒶𝒷𝒸𝒹𝒻𝒽𝒾𝒿𝓀𝓁𝓂𝓃𝓅𝓆𝓇𝓈𝓉𝓊𝓋𝓌𝓍𝓎𝓏
NEGATIVE CIRCLED LATIN LETTER  : 🅐🅑🅒🅓🅔🅕🅖🅗🅘🅙🅚🅛🅜🅝🅞🅟🅠🅡🅢🅣🅤🅥🅦🅧🅨🅩
NEGATIVE SQUARED LATIN LETTER  : 🅰🅱🅲🅳🅴🅵🅶🅷🅸🅹🅺🅻🅼🅽🅾🅿🆀🆁🆂🆃🆄🆅🆆🆇🆈🆉
SQUARED LATIN LETTER  : 🄰🄱🄲🄳🄴🄵🄶🄷🄸🄹🄺🄻🄼🄽🄾🄿🅀🅁🅂🅃🅄🅅🅆🅇🅈🅉🆥
