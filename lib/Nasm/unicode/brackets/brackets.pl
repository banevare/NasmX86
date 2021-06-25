#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/
#-------------------------------------------------------------------------------
# Find all unicode brackets
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
use warnings FATAL => qw(all);
use strict;
use Carp;
use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use Test::More qw(no_plan);
use feature qw(say state current_sub);

my $bracketBase = 0x10;                                                         # Start numbering brackets from here


my $home     = currentDirectory;                                                # Home folder
my $unicode  = q(https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt);# Unicode specification
my $data     = fpe $home, qw(unicode txt);                                      # Local copy of unicode
my $brackets = fpe $home, qw(brackets txt);                                     # Brackets

if (!-e $data)                                                                  # Download specification
 {say STDERR qx(curl -o $data $unicode);
 }

my @s = readFile $data;

if (1)                                                                          # Write brackets
 {my @S;

  for my $s(@s)                                                                 # Select the brackets we want
   {next unless $s =~ m(BRACKET);
    next unless $s =~ m(LEFT) or $s =~ m(RIGHT);
    my @w = split m/;/, $s;
    my ($point, $name) = @w;
    my $u = eval "0x$point";
    $@ and confess "$s\n$@\n";

    next if $u <=   125;
    next if $u >=  9121 and  $u <=  9137;
    next if $u >= 11778 and  $u <= 11815;
    next if $u >= 12300 and  $u <= 12303;
    next if $u >= 65047 and  $u <= 65118 ;
    next if $u >= 65378;
    push @S, [$u, $name, $s];
   }

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

  if (0)                                                                        # Check sizes of the ranges
   {for my $t(@t)
     {lll "AAAA ", scalar(@$t);
     }
    lll "BBBB ", scalar(@t);
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
  say STDERR "my \$bl = Rd(", join(', ',  @l), ");";
  say STDERR "my \$bh = Rd(", join(', ',  @h), ");";
# lll "BBBB", dump([@t]);
#  my $t = join "", @t;
#  owf($brackets, $t);
 }
#lll "AAAA", dump(\@S);
