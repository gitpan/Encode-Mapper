use strict;
use warnings;
use Module::Build;

my $builder = Module::Build->new(
    module_name         => 'Encode::Mapper',
    license             => 'perl',
    dist_author         => 'Otakar Smrz <otakar smrz mff cuni cz>',
    dist_version_from   => 'lib/Encode/Mapper.pm',
    create_readme       => 1,
    build_requires => {
                           'Test::More' => 0,
                      },
    add_to_cleanup      => [ 'Encode-Mapper-*' ],
);

$builder->create_build_script();
