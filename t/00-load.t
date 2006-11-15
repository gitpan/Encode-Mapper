#!perl -T

use Test::More tests => 1;

BEGIN {
	use_ok( 'Encode::Mapper' );
}

diag( "Testing Encode::Mapper $Encode::Mapper::VERSION, Perl $], $^X" );
