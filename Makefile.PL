# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.

use 5.008;
use ExtUtils::MakeMaker;

WriteMakefile(
    'NAME'          => 'Encode::Mapper',
    'VERSION_FROM'  => 'Mapper.pm',
    'PREREQ_PM'     => { 'Encode' => 1.83 * 0,
                         'Data::Dumper' => 2.12 * 0,
                         'Carp' => 1.01 * 0 },
    'ABSTRACT_FROM' => 'Mapper.pm',
    'AUTHOR'        => 'Otakar Smrz <smrz@ckl.mff.cuni.cz>',
);
