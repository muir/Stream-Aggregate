
use ExtUtils::MakeMaker;

WriteMakefile( 
	'VERSION_FROM' => 'lib/Stream/Aggregate.pm',
	'NAME' => 'Aggregate',
	($] >= 5.005 ?
	('ABSTRACT' => 'Aggregate a data stream',
	'AUTHOR'   => 'David Muir Sharnoff <muir@idiom.org>') : ()),
	'dist' => { COMPRESS=>"gzip", SUFFIX=>"gz" },
	'PREREQ_PM' => {
		'Hash::Util'	=> 0,
		'B::Deparse'	=> 0,
		'List::Util'	=> 0,
		'Config::Checker' 	=> 0,
		'List::EvenMoreUtils'	=> 0,
		'Config::YAMLMacros'	=> 0,
		'Data::Dumper'		=> 0,
	},
);
