# ############################################################################ Otakar Smrz, 2003/01/23
#
# Mapper Engine Class ##################################################################### 2003/06/19

# $Id: Mapper.pm,v 1.10 2003/08/04 12:07:40 smrz Exp $

package Encode::Mapper;

use 5.008;

use strict;
use warnings;

use Carp;

our $VERSION = do { my @r = q$Revision: 1.10 $ =~ /\d+/g; sprintf "%d." . "%02d" x $#r, @r };


use bytes;                  # ensures splitting into one-byte tokens .. lexically scoped


*new = *compile{'CODE'};    # provides the 'new' constructor .. the 'compile' method
                            # *new = \&compile;     # might be known at compile-time


sub compile ($@) {          # returns Mapper .. modified Aho-Corasick and Boyer-Moore search engine
    my $cls = shift @_;
    my (@tree, @bell, @skip, @queue, @stack);
    my ($q, $r, $s, $t, $i, $token, $trick);

    my ($null_list, $null_hash) = ([], {});     # references to empties need not consume unique memory

    $skip[0] = undef;       # never ever used .. fix the number of list elements equal
    $bell[0] = $null_list;  # important .. depth-wise inheritation of the lists

    for ($i = 0; $i < @_; $i += 2) {    # generate $tree[$q] transition function and initial $bell[$q]

        unless (defined $_[$i] and $_[$i] ne '') {
            carp "Rule's LHS is empty, rule ignored";
            next;
        }
        unless (defined $_[$i + 1]) {
            carp "Rule's RHS is undefined, rule ignored";
            next;
        }

        if (UNIVERSAL::isa($_[$i + 1], 'ARRAY')) {
            unless (defined $_[$i + 1]->[0]) {
                carp "Rule's RHS is undefined, rule ignored";
                next;
            }
            unless (ref \$_[$i + 1]->[0] eq 'SCALAR' or UNIVERSAL::isa($_[$i + 1]->[0], 'CODE')) {
                carp "Rule's RHS is neither literal nor subroutine reference, rule ignored";
                next;
            }
            unless (defined $_[$i + 1]->[1] and length $_[$i + 1]->[1] < length $_[$i]) {
                carp "Rule type '\$A => [\$X, \$Y], length \$A > length \$Y' misused, " .
                     "considering it '\$A => \$X'";
                $_[$i + 1] = $_[$i + 1]->[0];
            }
        }
        elsif (ref \$_[$i + 1] ne 'SCALAR' and not UNIVERSAL::isa($_[$i + 1], 'CODE')) {
            carp "Rule's RHS is neither literal nor subroutine reference, rule ignored";
            next;
        }

        $q = 0;

        foreach $token (split //, $_[$i]) {
            $tree[$q]->{$token} = ++$r unless defined $tree[$q]->{$token};  # increment $r ^^
            $q = $tree[$q]->{$token};
        }

        $tree[$q] = {} unless defined $tree[$q];    # define trees correctly, economize below

        carp "Redefining the mapping for key '$_[$i]'" if defined $bell[$q];
        $bell[$q] = [ $_[$i + 1] ];
    }

    foreach $token (map { chr } 0x00..0xFF) {
        unless (defined $tree[0]->{$token}) { $tree[0]->{$token} = 0; }
        else {
            $skip[$tree[0]->{$token}] = 0;
            unless (defined $bell[$tree[0]->{$token}]) { $bell[$tree[0]->{$token}] = $bell[0]; }

            push @queue, $tree[0]->{$token};
        }
    }

    while (@queue) {                # generate $skip[$q] backward function and complete $bell[$q]
        $q = shift @queue;

        foreach $token (keys %{$tree[$q]}) {
            $t = $tree[$q]->{$token};
            push @queue, $t;

            if (defined $bell[$t]) {
                $skip[$t] = 0;

                if (UNIVERSAL::isa($bell[$t]->[0], 'ARRAY')) {  # shortening property of the rules
                    $s = $skip[$t];

                    foreach $trick (split //, $bell[$t]->[0]->[1]) {
                        until (defined $tree[$s]->{$trick}) {   # loops only if not in the root ^^
                            push @{$bell[$t]}, @{$bell[$s]};
                            $s = $skip[$s];
                        }
                        $s = $tree[$s]->{$trick};
                    }

                    $skip[$t] = $s;
                    $bell[$t]->[0] = $bell[$t]->[0]->[0];
                }
            }
            else {
                $s = $skip[$q];
                $bell[$t] = [ @{$bell[$q]} ];   # unique reference quite important ^^

                until (defined $tree[$s]->{$token}) {   # extremely tricky ...
                    push @{$bell[$t]}, @{$bell[$s]};
                    $s = $skip[$s];
                }

                $skip[$t] = $tree[$s]->{$token};
            }
        }

        $tree[$q] = $null_hash unless keys %{$tree[$q]};    # economize with memory
    }

    return bless {
                    "current" => 0,
                    "tree" => \@tree,
                    "bell" => \@bell,
                    "skip" => \@skip,
                    "null" => { 'list' => $null_list, 'hash' => $null_hash },
        }, $cls;
}


sub process ($@) {          # returns the list of search results performed by Mapper
    my $obj = shift @_;
    my (@returns, $phrase, $token, $q);

    $q = $obj->{'current'};

    foreach $phrase (@_) {
        foreach $token (split //, $phrase) {
            until (defined $obj->{'tree'}[$q]->{$token}) {
                push @returns, @{$obj->{'bell'}[$q]};
                $q = $obj->{'skip'}[$q];
            }
            $q = $obj->{'tree'}[$q]->{$token};
        }
    }

    $obj->{'current'} = $q;

    return @returns;
}


sub recover ($;$$) {        # returns the 'in-progress' search result and resets Mapper
    my ($obj, $r, $q) = @_;
    my (@returns);

    $q = $obj->{'current'} unless defined $q;

    until ($q == 0) {
        push @returns, @{$obj->{'bell'}[$q]};
        $q = $obj->{'skip'}[$q];
    }

    $obj->{'current'} = defined $r ? $r : 0;

    return @returns;
}


sub compute ($@) {
    my $obj = shift @_;
    my (@returns, $phrase, $token, $q);

    $obj->recover();

    foreach $phrase (@_) {
        foreach $token (split //, $phrase) {
            push @returns, [$token, $obj->{'current'}];
            push @{$returns[-1]}, [$obj->process($token)];
            $q = $obj->{'current'};
            push @{$returns[-1]}, $q, $obj->{'bell'}[$q], $obj->{'skip'}[$q];
        }
    }

    push @returns, ['recover', $obj->{'current'}];
    push @{$returns[-1]}, [$obj->recover()];
    $q = $obj->{'current'};
    push @{$returns[-1]}, $q, $obj->{'bell'}[$q], ($q == 0 ? 'undef' : $obj->{'skip'}[$q]);

    return @returns;
}


sub dumper ($;$) {
    my ($obj, $ref) = @_;

    $ref = ['L', 'H', 'mapper'] unless defined $ref;

    require Data::Dumper;

    return Data::Dumper->new([$obj->{'null'}{'list'}, $obj->{'null'}{'hash'}, $obj], $ref);
}


sub encode ($$$;$) {
    my ($cls, $text, $encoder, $enc) = @_;

    require Encode;

    unless (Encode::is_utf8($text)) {
        carp "The input text is not in Perl's internal utf8 .. note only, may be OK";
    }

    if ($enc) {
        unless (Encode::resolve_alias($enc)) {
            carp "Cannot resolve the proposed '$enc' encoding";
            return undef;
        }

        $text = Encode::encode($enc, $text);
    }

    if (not UNIVERSAL::isa($encoder, 'ARRAY') or grep { not $_->isa($cls) } @{$encoder}) {
        carp "Expecting a reference to an array of '$cls' objects";
        return undef;
    }

    foreach my $mapper (@{$encoder}) {
        $text = join "", map {
                    UNIVERSAL::isa($_, 'CODE') ? $_->() : $_
                } $mapper->process($text), $mapper->recover();
    }

    return $text;
}


sub decode ($$$;$) {
    my ($cls, $text, $decoder, $enc) = @_;

    require Encode;

    $enc = 'utf8' unless $enc;

    unless (Encode::resolve_alias($enc)) {
        carp "Cannot resolve the proposed '$enc' encoding";
        return undef;
    }

    if (not UNIVERSAL::isa($decoder, 'ARRAY') or grep { not $_->isa($cls) } @{$decoder}) {
        carp "Expecting a reference to an array of $cls objects";
        return undef;
    }

    foreach my $mapper (@{$decoder}) {
        $text = join "", map {
                    UNIVERSAL::isa($_, 'CODE') ? $_->() : $_
                } $mapper->process($text), $mapper->recover();
    }

    return Encode::is_utf8($text) ? $text : Encode::decode($enc, $text);
}


1;

__END__


=head1 NAME

Encode::Mapper - Perl extension for intuitive, yet efficient construction of mappings for Encode

    $Id: Mapper.pm,v 1.10 2003/08/04 12:07:40 smrz Exp $


=head1 SYNOPSIS

    use Encode::Mapper;     ############################################# Enjoy the ride ^^

    ## Types of rules for mapping the data and controlling the engine's configuration #####

    @rules = (
        'x',            'y',            # single 'x' be 'y', unless greediness prefers ..
        'xx',           'Y',            # .. double 'x' be 'Y' or other rules

        'uc(x)x',       sub { 'sorry ;)' },     # if 'x' follows 'uc(x)', be sorry, else ..

        'uc(x)',        [ '', 'X' ],            # .. alias this *engine-initial* string
        'xuc(x)',       [ '', 'xX' ],           # likewise, alias for the 'x' prefix

        'Xxx',          [ sub { $i++; '' }, 'X' ],      # count the still married 'x'
    );


    ## Constructors of the engine, i.e. one Encode::Mapper instance #######################

    $mapper = Encode::Mapper->compile( @rules );        # engine constructor
    $mapper = Encode::Mapper->new( @rules );            # equivalent alias


    ## Elementary performance of the engine ###############################################

    @source = ( 'x', 'xx', 'xxuc(x)', 'xxx', '', 'xx' );    # distribution of the data ..
    $source = join '', @source;                             # .. is ignored in this sense

    @result = ($mapper->process(@source), $mapper->recover());  # the mapping procedure
    @result = ($mapper->process($source), $mapper->recover());  # completely equivalent

    $result = join '', map { ref $_ eq 'CODE' ? $_->() : $_ } @result;

        # maps 'xxxxxuc(x)xxxxx' into ( 'Y', 'Y', '', 'y', CODE(...), CODE(...), 'y' ), ..
        # .. then converts it into 'YYyy', setting $i == 2

    @follow = $mapper->compute(@source);    # follow the engine's computation over @source
    $dumper = $mapper->dumper();            # returns the engine as a Data::Dumper object

    ## Module's higher API implemented for convenience ####################################

    $encoder = [ $mapper, Encode::Mapper->compile( ... ), ... ];    # reference to mappers
    $result = Encode::Mapper->encode($source, $encoder, 'utf8');    # encode down to 'utf8'

    $decoder = [ $mapper, Encode::Mapper->compile( ... ), ... ];    # reference to mappers
    $result = Encode::Mapper->decode($source, $decoder, 'utf8');    # decode up from 'utf8'


=head1 ABSTRACT

    Encode::Mapper serves for intuitive, yet efficient construction of mappings for Encode.
    The module finds direct application in Encode::Arabic and Encode::Korean, providing an
    object-oriented programming interface to convert data consistently, follow the engine's
    computation, dump the engine using Data::Dumper etc.


=head1 DESCRIPTION

It looks like the author of the extension ... ;) prefered giving formal and terse examples to
writing English. Please, see L<Encode::Arabic|Encode::Arabic> and L<Encode::Korean|Encode::Korean>,
where L<Encode::Mapper|Encode::Mapper> is used for solving complex real-world problems.


=head2 INTRO AND RULE TYPES

The module's core is an algoritm which, from the rules given by the user, builds a finite-state
transducer, i.e. an engine performing greedy search in the input stream and producing output
data and side effects relevant to the results of the search. Transducers may be linked one with
another, thus forming multi-level devices suitable for nontrivial encoding/decoding tasks.

The rules declare which input sequences of L<bytes|bytes> to search for, and what to do upon their
occurence. If the left-hand side (LHS) of a rule is the longest left-most string out of those
applicable on the input, the righ-hand side (RHS) of the rule is evaluated. The RHS defines the
corresponding output string, and possibly controls the engine as if the extra text were prepended
before the rest of the input:

    $A => $X            # $A .. literal string
                        # $X .. literal string or subroutine reference
    $A => [$X, $Y]      # $Y .. literal string for which 'length $Y < length $A'

The order of the rules does not matter, except when several rules with the same LHS are stated.
In such a case, redefinition warning is issued before overriding the RHS.


=head2 LOW-LEVEL METHODS


=over


=item compile (I<$class,> @list)

The constructor of an L<Encode::Mapper|Encode::Mapper> instance. The first argument is the name of the
class, the rest is the list of rules ... LHS odd elements, RHS even elements. Redefinition for repeated
LHS is enabled, and warned about.

The compilation algorithm, and the search algorithm itself, were inspired by Aho-Corasick and Boyer-Moore
algorithms, and by the studies of finite automata with the restart operation. The engine is implemented
in the classical sense, using hashes for the transition function for instance. We expect to improve this
to Perl code evaluation, if the speed-up is significant.

It is to explore the way Perl's regular expressions would cope with the task, i.e. verify our initial
doubts which prevented us from trying. Since L<Encode::Mapper|Encode::Mapper>'s functionality is much
richer than pure search, simulating it completely might be resource-expensive and non-elegant. Therefore,
experiment reports are welcome.


=item new (I<$class,> @list)

Name alias to the C<compile> constructor.


=item process (I<$obj,> @list)

Process the input list with the engine. There is no resetting within the call of the method. Internally,
the text in the list is C<split> into L<bytes|bytes>, and there is just no need for the user to C<join>
his/hers strings or lines of data. Note the unveiled properties of the L<Encode::Mapper|Encode::Mapper>
class as well:

    sub process ($@) {          # returns the list of search results performed by Mapper
        my $obj = shift @_;
        my (@returns, $phrase, $token, $q);

        use bytes;              # ensures splitting into one-byte tokens

        $q = $obj->{'current'};

        foreach $phrase (@_) {
            foreach $token (split //, $phrase) {
                until (defined $obj->{'tree'}[$q]->{$token}) {
                    push @returns, @{$obj->{'bell'}[$q]};
                    $q = $obj->{'skip'}[$q];
                }
                $q = $obj->{'tree'}[$q]->{$token};
            }
        }

        $obj->{'current'} = $q;

        return @returns;
    }


=item recover (I<$obj,> $r, $q)

Since the search algorithm is greedy and the engine does not know when the end of the data comes,
there must be a method to tell. Normally, C<recover> is called on the object without the other two
optional parameters setting the initial and the final state, respectively.

    sub recover ($;$$) {        # returns the 'in-progress' search result and resets Mapper
        my ($obj, $r, $q) = @_;
        my (@returns);

        $q = $obj->{'current'} unless defined $q;

        until ($q == 0) {
            push @returns, @{$obj->{'bell'}[$q]};
            $q = $obj->{'skip'}[$q];
        }

        $obj->{'current'} = defined $r ? $r : 0;

        return @returns;
    }


=item compute (I<$obj,> @list)

Tracks down the computation over the list of data, resetting the engine before and after to its
initial state. Developers might like this ;)

    local $\ = "\n";    local $, = ":\t";           # just define the display

    foreach $result ($mapper->compute($source)) {   # follow the computation

        print "Token", $result->[0];
        print "Source", $result->[1];
        print "Output", join " + ", @{$result->[2]};
        print "Target", $result->[3];
        print "Bell", join ", ", @{$result->[4]};
        print "Skip", $result->[5];
    }


=item dumper (I<$obj,> $ref)

The individual instances of L<Encode::Mapper|Encode::Mapper> can be stored as revertible data
structures. For minimalistic reasons, dumping needs to include explicit short-identifier
references to the empty array and the empty hash of the engine. For details, see
L<Data::Dumper|Data::Dumper>.

    sub dumper ($;$) {
        my ($obj, $ref) = @_;

        $ref = ['L', 'H', 'mapper'] unless defined $ref;

        require Data::Dumper;

        return Data::Dumper->new([$obj->{'null'}{'list'}, $obj->{'null'}{'hash'}, $obj], $ref);
    }


=back


=head2 HIGH-LEVEL METHODS

In the L<Encode|Encode> world, one can work with different encodings and is also provided a function
for telling if the data are in Perl's internal utf8 format or not. In the
L<Encode::Mapper|Encode::Mapper> business, one is encouraged to compile different mappers and stack
them on top of each other, getting an easy-to-work-with filtering device.

In combination, this module offers the following C<encode> and C<decode> methods. In their prototypes,
C<$encoder>/C<$decoder> represent merely a reference to an array of mappers, although mathematics might
do more than that in future implementations ;)

Currently, the mappers involved are not reset with C<recover> before the computation:

    foreach $mapper (@{$_[2]}) {    # either $encoder or $decoder
        $text = join "", map {
                    UNIVERSAL::isa($_, 'CODE') ? $_->() : $_
                } $mapper->process($text), $mapper->recover();
    }


=over


=item encode (I<$class,> $text, $encoder, $enc)

If C<$enc> is defined, the C<$text> is encoded into that encoding, using L<Encode|Encode>. Then, the
C<$encoder>'s engines are applied in series on the data. The returned text should have the utf8
flag off.


=item decode (I<$class,> $text, $decoder, $enc)

The C<$text> is run through the sequence of engines in C<$decoder>. If the result does not have the
utf8 flag on, decoding from C<$enc> is further performed by L<Encode|Encode>. If C<$enc> is not defined,
utf8 is assumed.


=back


=head2 EXPORT

This module does not export any symbols.


=head1 SEE ALSO

There are related theoretical studies which the implementation may have touched.
You might be interested in Aho-Corasick and Boyer-Moore algorithms as well as in
finite automata with the restart operation.

L<Encode|Encode>, L<Encode::Arabic|Encode::Arabic>, L<Encode::Korean|Encode::Korean>,
L<Data::Dumper|Data::Dumper>


=head1 AUTHOR

Otakar Smrz, L<http://ckl.mff.cuni.cz/smrz/>

    eval { 'E<lt>' . 'smrz' . "\x40" . (join '.', qw 'ckl mff cuni cz') . 'E<gt>' }

Perl is also designed to make the easy jobs not that easy ;)


=head1 COPYRIGHT AND LICENSE

Copyright 2003 by Otakar Smrz

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.


=cut
