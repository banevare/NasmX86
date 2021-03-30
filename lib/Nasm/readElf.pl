#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/
#-------------------------------------------------------------------------------
# Extract macro values and structure details from C programs.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
use warnings FATAL => qw(all);
use strict;
use Carp;
#use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use Test::More tests => 16;
use feature qw(say current_sub);

my %extractCStructure;                                                          # Structured extracted from C files

sub extractCStructure($)                                                        # Extract the details of a structure
 {my ($input) = @_;                                                             # Input C file - a temporary one is ok

  return $extractCStructure{$input} if exists $extractCStructure{$input};       # Return cached value if it exists
  return undef unless confirmHasCommandLineCommand(q(gcc));                     # Check that we have gcc

  my @e = qx(gcc -x c -gdwarf $input; readelf -w a.out; rm a.out);              # Structure details via dwarf debugging info
  my @s;                                                                        # Structure

  for my $e(@e)                                                                 # Each line of dwarf
   {if ($e =~ m(<(\w+)><(\w+)>: Abbrev Number:\s+(\w+)\s+(.*)))
     {push @s, [[$1, $2, $3, $4]];
     }
    if ($e =~ m(<(\w+)>\s+(\w+)\s*:\s(.*)))
     {push $s[-1]->@*, [$1, $2, $3];
     }
   }

  my %s; my %b;                                                                 # Structure details, base details
  for my $i(keys @s)                                                            # Each dwarf
   {if             ($s[$i][0][3] =~ m(DW_TAG_structure_type))                   # Structure followed by fields
     {my $name    = $s[$i][1][2];
      my $size    = $s[$i][2][2];
      $s{$name}   = genHash('structure', size=>$size, fields=>{});
      for(my $j   = $i + 1; $j < @s; ++$j)                                      # Following tag fields
       {last unless  $s[$j][0][3] =~ m(DW_TAG_member);
        my $field =  $s[$j][1][2];
        my $type  =  $s[$j][5][2];
        my $loc   =  $s[$j][6][2];
        $type =~ s(<0x|>) ()gs;
        $s{$name}->fields->{$field} = genHash('field',
          field=>$field, type=>$type, loc=>$loc, size=>undef);
       }
     }
    if (            $s[$i][0][3] =~ m(DW_TAG_base_type))                        # Base types
     {my $offset  = $s[$i][0][1];
      my $size    = $s[$i][1][2];
      my $type    = $s[$i][3][2];
      $b{$offset} = genHash('base', size=>$size, type=>$type);
     }
   }

  for my $s(keys %s)                                                            # Fix references to base types
   {my $fields = $s{$s}->fields;
    for my $f(sort keys %$fields)
     {my $type  = $$fields{$f}->type;
      if (my $b = $b{$type})
       {$$fields{$f}->size = $b->size;
        $$fields{$f}->type = $b->type;
       }
      else
       {say STDERR "No base for offset: $b";
       }
     }
   }

  $extractCStructure{$input} = \%s                                              # Structure details
 } # extractCStructure

sub extractCField($$$)                                                          # Extract the details of a field in a structure in a C file
 {my ($input, $structure, $field) = @_;                                         # Input file, structure name,  field within structure
  if     (my $s = extractCStructure $input)                                     # Structures in file
   {if   (my $S = $$s{$structure})                                              # Found structure
     {if (my $F = $S->fields)                                                   # Structure has fields
       {return $$F{$field};                                                     # Field detail
       }
     }
   }
  undef                                                                         # Parse failed or no such structure
 } # extractCField

sub extractCFieldLoc($$$)                                                       # Extract the offset to the location of a field in a structure in a C file
 {my ($input, $structure, $field) = @_;                                         # Input file, structure name,  field within structure
  if (my $f = extractCField($input, $structure, $field))                        # Structures in file
   {return $f->loc;                                                             # Offset to field location
   }
  undef                                                                         # Parse failed or no such structure or no such field
 } # extractCFieldLoc

sub extractCFieldSize($$$)                                                      # Extract the size of a field in a structure in a C file
 {my ($input, $structure, $field) = @_;                                         # Input file, structure name,  field within structure
  if (my $f = extractCField($input, $structure, $field))                        # Structures in file
   {return $f->size;                                                            # Size of field
   }
  undef                                                                         # Parse failed or no such structure or no such field
 } # extractCFieldSize

sub extractCFieldType($$$)                                                      # Extract the type of a field in a structure in a C file
 {my ($input, $structure, $field) = @_;                                         # Input file, structure name,  field within structure
  if (my $f = extractCField($input, $structure, $field))                        # Structures in file
   {return $f->type;                                                            # Type of field
   }
  undef                                                                         # Parse failed or no such structure or no such field
 } # extractCFieldType

sub extractCStructureFields($$)                                                 # Extract the names of the fields in a C structure
 {my ($input, $structure) = @_;                                                 # Input file, structure name
  if (my $s = extractCStructure $input)                                         # Structures in file
   {if (my $S = $$s{$structure})                                                # Found structure
     {if (my $F = $S->fields)                                                   # Structure has fields
       {return sort keys %$F;                                                   # Return names of fields in structure in ascending order
       }
     }
   }
  ()                                                                            # Parse failed or no such structure
 } # extractCStructureSize

sub extractCStructureSize($$)                                                   # Extract the size of a C structure
 {my ($input, $structure) = @_;                                                 # Input file, structure name
  if (my $s = extractCStructure $input)                                         # Structures in file
   {if (my $S = $$s{$structure})                                                # Found structure
     {return $S->size;                                                         # Return structure size
     }
   }
  undef                                                                         # Parse failed or no such structure
 } # extractCStructureSize


my %extractMacroDefinitionsFromCHeaderFile;                                     # Cache macro definitions

sub extractMacroDefinitionsFromCHeaderFile($)                                   # Extract the macro definitions found in a C header file using gcc
 {my ($includeFile) = @_;                                                       # C Header file name as it would be entered in a C program
  my $d = $extractMacroDefinitionsFromCHeaderFile{$includeFile};                # Cached macro definitions
  return $d if $d;                                                              # Return cached value

  confirmHasCommandLineCommand("gcc");                                          # Check gcc
  my @l = qx(gcc -E -dM -include "$includeFile" - < /dev/null);                 # Use gcc to extract macro definitions

  my %d;
  for my $l(@l)                                                                 # Extract macro definitions
   {if ($l =~ m(\A#define\s+(\S+)\s+(\S+)(.*)))
     {$d{$1} = $2;
     }
   }

  $extractMacroDefinitionsFromCHeaderFile{$includeFile} = \%d;                  # Return definitions
 }

sub extractMacroDefinitionFromCHeaderFile($$)                                   # Extract a macro definitions found in a C header file using gcc
 {my ($includeFile, $macro) = @_;                                               # C Header file name as it would be entered in a C program, macro name
  if (my $d = extractMacroDefinitionsFromCHeaderFile($includeFile))             # Get macro definitrions
   {return $$d{$macro};
   }
  undef
 }

if (1)                                                                          #TextractCField #TextractCStructureFields #TextractCStructureSize  #TextractCFieldLoc #TextractCFieldSize #TextractCFieldType
 {my $input = writeTempFile <<END;
struct S
 {int a;
  int b;
  int c;
 } s;
void main() {}
END

  is_deeply extractCField($input, q(S), q(a)),
    bless({ field => "a", loc => 0, size => 4, type => "int" }, "field");

  is_deeply extractCField($input, q(S), q(b)),
    bless({ field => "b", loc => 4, size => 4, type => "int" }, "field");

  is_deeply extractCField($input, q(S), q(c)),
    bless({ field => "c", loc => 8, size => 4, type => "int" }, "field");

  is_deeply [extractCStructureFields($input, q(S))], [qw(a b c)];

  is_deeply extractCStructureSize($input, q(S)), 12;

  is_deeply extractCFieldLoc($input,  q(S), q(a)), 0;
  is_deeply extractCFieldLoc($input,  q(S), q(b)), 4;
  is_deeply extractCFieldLoc($input,  q(S), q(c)), 8;

  is_deeply extractCFieldSize($input, q(S), q(a)), 4;
  is_deeply extractCFieldSize($input, q(S), q(b)), 4;
  is_deeply extractCFieldSize($input, q(S), q(c)), 4;

  is_deeply extractCFieldType($input, q(S), q(a)), q(int);
  is_deeply extractCFieldType($input, q(S), q(b)), q(int);
  is_deeply extractCFieldType($input, q(S), q(c)), q(int);
 }

if (1)                                                                          #TextractMacroDefinitionsFromIncludeFile
 {my $h = "linux/mman.h";
  ok extractMacroDefinitionFromCHeaderFile("linux/mman.h", q(MAP_ANONYMOUS)) eq "0x20";
  ok extractMacroDefinitionFromCHeaderFile("linux/mman.h", q(PROT_WRITE))    eq "0x2";
 }

