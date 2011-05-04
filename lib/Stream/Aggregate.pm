#
# TODO: what this can't handle right now is things like:
#
#	* how many different URLs were there on a per query basis?
#

package Stream::Aggregate;

use strict;
use warnings;
use Hash::Util qw(lock_keys);
use B::Deparse;
use List::Util qw(min max minstr maxstr);
use Config::Checker;
use Stream::Aggregate::Stats;
use Stream::Aggregate::Random;
use List::EvenMoreUtils qw(list_difference_position);
use Tie::Function::Examples qw(%line_numbers);
use Eval::LineNumbers qw(eval_line_numbers);
use Config::YAMLMacros::YAML;
use Carp qw(confess);

require Exporter;

our @ISA = qw(Exporter);
our @EXPORT = qw(generate_aggregation_func);
our $VERSION = 0.302;

our $suppress_line_numbers = 0;

my $prototype_config = <<'END_PROTOTYPE';
max_stats_to_keep:      '?<4000>Maximum number of stats to keep for mean/stddev etc[INTEGER]'
context:                '?From $log, return an array describing the current context[CODE]'
context_config:         '%optional configuration hash for "context" code'
context2columns:        '?From @current_context, return a hash of columns[CODE]'
context2columns_config: '%optional configuration hash for "context2columns" code'
stringify_context:      '?Turn @currnet_context into an array of strings[CODE]'
stringify_context_config: '%optional configuration hash for "stringify_context" code'
finalize_result:        '?Final opportunity to adjust the return values[CODE]'
finalize_result_config: '%optional configuration has for "finalize_result" code'
filter:                 '?Should this result be saved for statistics and counted for counts?[CODE]'
filter_config:          '%optional configuration hash for "filter" code'
filter_early:           '?<0>Check the filter early (before figuring out contexts)?[BOOLEAN]'
passthrough:            '?Any additional items for the output?[CODE]'
passthrough_config:     '%optional configuration has for "passthrough" code'
ephemeral:              '%ephemeral columns (column -> code)'
ephemeral0:             '%ephemeral columns (column -> code, evaluated before "ephemeral")'
ephemeral2:             '%ephemeral columns (column -> code, evaluated after "ephemeral")'
ephemeral3:             '%ephemeral columns (column -> code, evaluated after crossproduct has set context (after "ephemeral2"))'
output:                 '%generated output columns (column -> code)'
counter:                '%counter columns (column -> code)'
percentage:             '%like a counter, but divided by the number of items'
sum:                    '%summation columns (column -> code)'
dominant:               '%most frequent (mode) value (column -> code)'
mean:                   '%mean value columns (column -> code)'
standard_deviation:     '%standard deviaton value columns (column -> code)'
median:                 '%median value columns (column -> code)'
min:                    '%min value columns (column -> code)'
max:                    '%max value columns (column -> code)'
minstr:                 '%minstr value columns (column -> code)'
maxstr:                 '%maxstr value columns (column -> code)'
keep:                   '%list of values to keep'
stat:                   '%statistical columns (using keep, column -> code)'
debug:                  '?<0>Print out the code for debugging'
preprocess:             '?Code to pre-process the input data[CODE]'
item_name:              '?<$log>Name of the item variable'
new_context:            '?Code that is run when there is a new context[CODE]'
new_context_config:     '%optional configuration hash for "new_context" code'
merge:                  '?Code that is run when merging a subcontext into a parent context[CODE]'
merge_config:           '%optional configuration hash for "merge" code'
reduce:                 '?Code that is run when reducing the saved data to save memory[CODE]'
merge_config:           '%optional configuration hash for "reduce" code'
crossproduct:           '%crossproduct context, keys are existing columns, values are size limits'
simplify:               '%code to choose new simpler values for over-full columns (column -> code)'
END_PROTOTYPE

sub nonblank
{
	my $value = shift;
	return undef unless defined $value;
	return undef if $value eq '';
	return $value;
}

sub resume_line_numbering
{
	my ($pkg, $file, $line) = caller(0);
	return sprintf(qq{#line %d "generated-code-interpoloated-after-%s-%d"\n}, $line, $file, $line);
}

sub generate_aggregation_func
{
	my ($agg_config, $extra, $user_extra) = @_;

	validate_aggregation_config($agg_config);

	my $renumber = ! $agg_config->{debug};

	# input data
	my $itemref;
	my $last_item;

	# 
	# if counting URLs, then the @current_context might be something like:
	#	'com', 'apple', '/movies', '/action'
	# If counting queries it might be something like:
	# 	'homocide',	'movies'
	#
	# @contexts is an array to state variables ($ps) that corrospond to the
	# elements of @current_context.   @context_strings is a string-ified 
	# copy of @current_context to handle contexts which are references.
	#
	# $count_this is return from &$filter_func;
	#
	my @contexts;
	my @context_strings;
	my @current_context;  
	my $ps;
	my $oldps;
	my $count_this = 1;
	my @items_seen = ( 0 );
	my %cross_context;
	my $cross_data = {};
	my @cross_keys;
	my $cross_limit = 1;
	my $cross_count = 0;
	my %cross_key_values;
	my %persist;

	# output
	my $row;
	my $suppress_result;

	# reduce data to limit memory use
	my @keepers;
	my @tossers;
	my $max_stats2keep = $agg_config->{max_stats_to_keep};
	my $do_reduce;

	# closures
	my $get_context_func;
	my $count_func;
	my $initialize_func;
	my $final_values_func;
	my $merge_func;
	my $context_columns_func;
	my $preprocess_func;
	my $filter_func;
	my $stringify_func;
	my $finalize_result_func;
	my $passthrough_func;
	my $user_merge_func;
	my $user_new_context_func;
	my $user_reduce_func;
	my $cross_reduce_func;
	my $new_ps_func;
	my $process_func;
	my $finish_context_func;
	my $finish_cross_func;
	my $add_context_component_func;
	my $cross_key_reduce_func;

	if ($agg_config->{crossproduct} && keys %{$agg_config->{crossproduct}}) {
		@cross_keys = sort keys %{$agg_config->{crossproduct}};
		for my $k (@cross_keys) {
			$cross_limit *= $agg_config->{crossproduct}{$k};
		}
	}

	my $compile_config = sub {
		my %varname;
		my $reduce_func;
		my %s;
		my %var_types;
		my %var_value;

		my $deparse = B::Deparse->new("-p", "-sC");

		#
		# A more sophisticated approach would figure out the dependencies of one value on
		# another and order them appropriately.   What's going on here is kinda hit & miss.
		#
		my $alias_varname = sub {
			my ($cc, $value) = @_;
			$varname{"\$column_$cc"} = $value;
		};
		my $usercode_inner = sub {
			my ($cctype, $cc, $code) = @_;
			return $alias_varname->($cc, $varname{$code}) if $varname{$code};
			my $original = $code;
			return $alias_varname->($cc, $varname{$code}) if $varname{$code};
			$code =~ s/(\$column_\w+)/defined($varname{$1}) ? $varname{$1} : $1/ge;
			if ($code =~ /\breturn\b/) {
				$code =~ s/^/\t\t/mg;
				$s{user}	.= qq{#line 3001 "FAKE-$extra->{name}-$cctype-$cc"\n} if $renumber;
				$s{user}	.= "my \$${cctype}_${cc}_func = sub {\n";
				$s{user}	.= $code;
				$s{user}	.= "};\n\n";
				$s{user}	.= "my \$column_$cc;\n";
				$s{precount}	.= "\tundef \$column_$cc;\n";
				$s{$cctype}	.= "\t\$column_$cc = ";
				$s{$cctype}	.= qq{\$${cctype}_${cc}_func->();\n};
			} elsif ($code =~ /[;\n]/) {
				$code =~ s/^/\t\t/mg;
				$s{user}	.= "my \$column_$cc;\n";
				$s{precount}	.= "\tundef \$column_$cc;\n";
				$s{$cctype}	.= "\t\$column_$cc = ";
				$s{$cctype}	.= "do {\n";
				$s{$cctype}	.= qq{#line 4001 "FAKE-$extra->{name}-$cctype-$cc"\n} if $renumber;
				$s{$cctype}	.= $code;
				$s{$cctype}	.= "\n\t};\n";
			} elsif ($code =~ /\A\$(column_\w+)\Z/) {
				die "value of $code isn't available yet";
			} else {
				$s{$cctype}	.= qq{#line 5001 "FAKE-$extra->{name}-$cctype-$cc"\n} if $renumber;
				$s{precount}	.= "\tundef \$column_$cc;\n";
				$s{user}	.= "my \$column_$cc;\n";
				$s{$cctype}	.= "\t\$column_$cc = $code;\n";
			}
			my $te = eval "no strict; no warnings; sub { $code }";
			die "eval $cctype/$cc: $original ($code): $@" if $@;
			my $body = $deparse->coderef2text($te);
			return $varname{$body} if $varname{$body};
			$varname{$body} = $varname{$code} = $varname{$original} = "\$column_$cc";
			$alias_varname->($cc, $varname{$code});
		};
		my $usercode = sub {
			my ($cctype, $cc, $code) = @_;
			my $value = $usercode_inner->(@_);
			$var_value{$cc} = $value;
			$var_types{$cc} = $cctype;
			return $value;
		};

		my %seen;
		my $cc;

		my @all_data	= qw(ephemeral0 ephemeral ephemeral2 ephemeral3 keep output counter percentage sum mean standard_deviation median dominant min minstr max maxstr stat);
		my @lock_data	= qw(                                           keep output counter percentage sum mean standard_deviation median dominant min minstr max maxstr stat);
		my @output_cols	= qw(                                                output counter percentage sum mean standard_deviation median dominant min minstr max maxstr stat);
		my @kept_cols	= qw(                                           keep                                    standard_deviation median dominant                           );
		my @stats_cols	= qw(                                                                                   standard_deviation median dominant                           );
		my @cross_cols	= qw(ephemeral0 ephemeral ephemeral2                                                                                                                 );
		my %cross_cols;
		@cross_cols{@cross_cols} = @cross_cols;

		#
		# Compile all the user code that for the various columns
		#
		for my $ucc (@all_data) {
			next unless $agg_config->{$ucc};
			for $cc (sort keys %{$agg_config->{$ucc}}) {
				die "column $cc is duplicated" if $seen{$cc}++;
				$usercode->($ucc, $cc, $agg_config->{$ucc}{$cc});
			}
		}

		#
		# 'keep' has to be first because 'stat' can't rewrite names
		#
		my %donekeep;
		my $has_keepers = 0;
		for my $keepers (@kept_cols) {
			for $cc (sort keys %{$agg_config->{$keepers}}) {
				next if $donekeep{$varname{$agg_config->{$keepers}{$cc}}};
				$donekeep{$varname{$agg_config->{$keepers}{$cc}}} = $cc;
				$s{initialize}	.= "\t\$ps->{keep}{$cc} = [];\n";
				$s{keeper2}	.= "\t\tpush(\@{\$ps->{keep}{$cc}}, $varname{$agg_config->{$keepers}{$cc}}) if \$count_this;\n";
				$s{merge}	.= "\tpush(\@{\$ps->{keep}{$cc}}, \@{\$oldps->{keep}{$cc}});\n";
				$s{reduce2}	.= "\t\@{\$ps->{keep}{$cc}} = \@{\$ps->{keep}{$cc}}[\@keepers];\n";
				$has_keepers++;
			}
		}
		if ($has_keepers) {
			$s{initialize}	.= "\t# has keepers\n";
			$s{initialize}  .= "\t\$ps->{numeric} = {};\n";

			$s{fv_setup}	.= "\t# has keepers\n";
			$s{fv_setup}	.= "\tlocal(\$Stream::Aggregate::Stats::ps) = \$ps;\n";

			$s{keeper1}	.= resume_line_numbering;
			$s{keeper1}	.= "\t# has keepers\n";
			$s{keeper1}	.= "\tmy \$random = rand(1);\n";
			$s{keeper1}	.= "\tif (\@{\$ps->{random}} < $max_stats2keep || \$random < \$ps->{random}[0]) {\n";
			$s{keeper1}	.= "\t\tpush(\@{\$ps->{random}}, \$random);\n";

			$s{keeper3}	.= resume_line_numbering;
			$s{keeper3}	.= "\t\t# has keepers\n";
			$s{keeper3}	.= "\t\t&\$reduce_func if \@{\$ps->{random}} > $max_stats2keep * 1.5;\n";
			$s{keeper3}	.= "\t}\n";

			$s{merge}	.= resume_line_numbering;
			$s{merge}	.= "\t# has keepers\n";
			$s{merge}	.= "\tpush(\@{\$ps->{random}}, \@{\$oldps->{random}});\n";

			$s{merge2}	.= resume_line_numbering;
			$s{merge2}	.= "\t# has keepers\n";
			$s{merge2}	.= "\t&\$reduce_func if \@{\$ps->{random}} > $max_stats2keep * 1.5;\n";

			$s{reduce}	.= eval_line_numbers(<<'END_REDUCE');
				# has keepers
				my $random = $ps->{random};
				@keepers = sort { $random->[$a] cmp $random->[$b] } 0..$#$random;
				@tossers = splice(@keepers, $max_stats2keep);
				@$random = @$random[@keepers];
END_REDUCE
			$s{reduce} .= resume_line_numbering;
		}

		for $cc (sort keys %{$agg_config->{output}}) {
			$s{initialize} .= "\t\$ps->{output}{$cc} = 0;\n";
		}

		for $cc (sort keys %{$agg_config->{counter}}) {
			$s{initialize}	.= "\t\$ps->{counter}{$cc} = 0;\n";
			$s{count2}	.= "\t\$ps->{counter}{$cc}++ if $varname{$agg_config->{counter}{$cc}};\n";
			$s{merge}	.= "\t\$ps->{counter}{$cc} += \$oldps->{counter}{$cc};\n";
		}

		for $cc (sort keys %{$agg_config->{percentage}}) {
			$s{initialize}	.= "\t\$ps->{percentage}{$cc} = undef;\n";
			$s{stat}	.= "\t\$ps->{percentage}{$cc} = \$ps->{percentage_counter}{$cc} * 100 / (\$ps->{percentage_total}{$cc} || .001);\n";
			$s{initialize}	.= "\t\$ps->{percentage_counter}{$cc} = 0;\n";
			$s{initialize}	.= "\t\$ps->{percentage_total}{$cc} = 0;\n";
			$s{count2}	.= "\t\$ps->{percentage_counter}{$cc}++ if $varname{$agg_config->{percentage}{$cc}};\n"; 
			$s{count2}	.= "\t\$ps->{percentage_total}{$cc}++ if defined $varname{$agg_config->{percentage}{$cc}};\n"; 
			$s{merge}	.= "\t\$ps->{percentage_counter}{$cc} += \$oldps->{percentage_counter}{$cc};\n";
			$s{merge}	.= "\t\$ps->{percentage_total}{$cc} += \$oldps->{percentage_total}{$cc};\n";
		}

		for $cc (sort keys %{$agg_config->{sum}}) {
			$s{initialize}	.= "\t\$ps->{sum}{$cc} = 0;\n";
			$s{count2}	.= "\t\$ps->{sum}{$cc} += $varname{$agg_config->{sum}{$cc}};\n";
			$s{merge}	.= "\t\$ps->{sum}{$cc} += \$oldps->{sum}{$cc};\n";
		}

		for $cc (sort keys %{$agg_config->{mean}}) {
			$s{initialize}	.= "\t\$ps->{mean}{$cc} = undef;\n";
			$s{stat}	.= "\t\$ps->{mean}{$cc} = \$ps->{mean_sum}{$cc} / (\$ps->{mean_count}{$cc} || 100);\n";
			$s{initialize}	.= "\t\$ps->{mean_sum}{$cc} = 0;\n";
			$s{initialize}	.= "\t\$ps->{mean_count}{$cc} = 0;\n";
			$s{count2}	.= "\tif (defined($varname{$agg_config->{mean}{$cc}})) {\n";
			$s{count2}	.= "\t	\$ps->{mean_sum}{$cc} += $varname{$agg_config->{mean}{$cc}};\n";
			$s{count2}	.= "\t	\$ps->{mean_count}{$cc}++;\n";
			$s{count2}	.= "\t}\n";
			$s{merge}	.= "\t\$ps->{mean_sum}{$cc} += \$oldps->{mean_sum}{$cc};\n";
			$s{merge}	.= "\t\$ps->{mean_count}{$cc} += \$oldps->{mean_count}{$cc};\n";
		}

		for $cc (sort keys %{$agg_config->{min}}) {
			$s{initialize}	.= "\t\$ps->{min}{$cc} = undef;\n";
			$s{count2}	.= "\t\$ps->{min}{$cc} = min grep { defined } \$ps->{min}{$cc}, $varname{$agg_config->{min}{$cc}};\n";
			$s{merge}	.= "\t\$ps->{min}{$cc} = min grep { defined } \$ps->{min}{$cc}, \$oldps->{min}{$cc};\n";
		}

		for $cc (sort keys %{$agg_config->{minstr}}) {
			$s{initialize}	.= "\t\$ps->{minstr}{$cc} = undef;\n";
			$s{count2}	.= "\t\$ps->{minstr}{$cc} = minstr grep { defined } \$ps->{minstr}{$cc}, $varname{$agg_config->{minstr}{$cc}};\n";
			$s{merge}	.= "\t\$ps->{minstr}{$cc} = minstr grep { defined } \$ps->{minstr}{$cc}, \$oldps->{minstr}{$cc};\n";
		}

		for $cc (sort keys %{$agg_config->{max}}) {
			$s{initialize}	.= "\t\$ps->{max}{$cc} = undef;\n";
			$s{count2}	.= "\t\$ps->{max}{$cc} = max grep { defined } \$ps->{max}{$cc}, $varname{$agg_config->{max}{$cc}};\n";
			$s{merge}	.= "\t\$ps->{max}{$cc} = max grep { defined } \$ps->{max}{$cc}, \$oldps->{max}{$cc};\n";
		}

		for $cc (sort keys %{$agg_config->{maxstr}}) {
			$s{initialize}	.= "\t\$ps->{maxstr}{$cc} = undef;\n";
			$s{count2}	.= "\t\$ps->{maxstr}{$cc} = maxstr grep { defined } \$ps->{maxstr}{$cc}, $varname{$agg_config->{maxstr}{$cc}};\n";
			$s{merge}	.= "\t\$ps->{maxstr}{$cc} = maxstr grep { defined } \$ps->{maxstr}{$cc}, \$oldps->{maxstr}{$cc};\n";
		}

		for my $statc (@stats_cols) {
			for $cc (sort keys %{$agg_config->{$statc}}) {
				my $keepcc = $donekeep{$varname{$agg_config->{$statc}{$cc}}} || die;
				$s{initialize}	.= "\t\$ps->{$statc}{$cc} = undef;\n";
				$s{stat}	.= "\t\$ps->{$statc}{$cc} = $statc('$keepcc');\n";
			}
		}

		for $cc (sort keys %{$agg_config->{stat}}) {
			$s{stat}	.= "\t\$ps->{stat}{$cc} = $varname{$agg_config->{stat}{$cc}};\n";
			$s{initialize}	.= "\t\$ps->{stat}{$cc} = undef;\n";
		}

		for my $cc (sort keys %{$agg_config->{output}}) {
			$s{initialize}	.= "\t\$ps->{output}{$cc} = undef;\n";
			$s{stat}	.= "\t\$ps->{output}{$cc} = $varname{$agg_config->{output}{$cc}};\n";
		}

		for my $icol (@lock_data) {
			$s{initialize} .= "\tlock_keys(%{\$ps->{$icol}});\n"
				if keys %{$agg_config->{$icol}};
		}

		for my $ctype (@output_cols) {
			for $cc (sort keys %{$agg_config->{$ctype}}) {
				$s{final_values} .= "\t\$row->{$cc} = \$ps->{$ctype}{$cc};\n";
			}
		}
		$s{final_values} .= "\t&\$finalize_result_func;\n" if $agg_config->{finalize_result};

		my $code = qq{#line 1 "FAKE-all-code-for-$extra->{name}"\n};
		$code .= qq{my $agg_config->{item_name};\n};
		$code .= "{\n";

		$s{reduce} .= "\t&\$user_reduce_func;\n";

		my $assemble_code = sub {
			my ($func, @keys) = @_;
			my $something;
			my $c = "# ---------------------------------------------------------------\n";
			$c .= "\$${func}_func = sub {\n"
				if $func;
			for my $s (@keys) {
				next unless exists $s{$s};
				$c .= qq{\n#line 1001 "FAKEFUNC-$extra->{name}-$func-$s"\n} if $renumber;
				$c .= $s{$s};
				delete $s{$s};
				$something = 1;
			}
			$c .= "\t0\n" 
				if $func && ! $something;
			$c .= "};\n"
				if $func;
			return $c;
		};

		#
		# Cross product aggregation & counts
		#
		if (@cross_keys) {
			my $esub = '';
			my $newsub = '';
			my $oldsub = '';
			my $loop_in = '';
			my $loop_in2 = '';
			my $loop_in3 = '';
			my $loop_in3a = '';
			my $loop_out = '';
			my $loop_out2 = '';
			my $loop_indent = "";
			my $loop_head = '';
			my $loop_mid = '';
			my $loop_mid3 = '';
			my $loop_dbug_old = '';
			my $loop_dbug_new = '';
			for my $cc (@cross_keys) {
				die "Crossproduct column '$cc' doesn't exist" unless $var_types{$cc};
				die "Crossproduct column '$cc' ($var_types{$cc}) isn't a valid type (@cross_cols)" unless $cross_cols{$var_types{$cc}};

				my $code = $agg_config->{simplify}{$cc} || 'return "*";';
				$s{user}	.= "my \$simplify_$cc = sub {\n";
				$s{user}	.= qq{#line 3001 "FAKE-$extra->{name}-simplify-$cc"\n} if $renumber;
				$s{user}	.= "\t".$code;
				$s{user}	.= "\n};\n";

				$loop_head	.= "\tmy %key_count_$cc;\n";

				$loop_mid	.= "\tmy \$key_map_$cc = \$cross_key_reduce_func->('$cc', \\%key_count_$cc, \$simplify_$cc);\n";
				$loop_mid3	.= ", $cc => \$key_$cc";

				$loop_dbug_old	.= " $cc:\$key_$cc";
				$loop_dbug_new	.= " $cc:\$new_$cc";

				$loop_in2	.= "$loop_indent	for my \$key_$cc (keys %{\$cross_data$oldsub}) {\n"; 

				$loop_in	.= "$loop_indent	for my \$key_$cc (keys %{\$cross_data$oldsub}) {\n"; 
				$loop_in	.= "$loop_indent		my \$new_$cc = \$key_$cc;\n";
				$loop_in	.= "$loop_indent		my \$must_inc = 0;\n";
				$loop_in	.= "$loop_indent		if (exists \$key_map_${cc}->{\$key_$cc}) {\n";
				$loop_in	.= "$loop_indent			\$new_$cc = \$key_map_${cc}->{\$key_$cc};\n";
				$loop_in	.= "$loop_indent			\$must_inc = 1;\n";
				$loop_in	.= "$loop_indent			\$must_do++;\n";
				$loop_in	.= "$loop_indent		} else {\n";
				$loop_in	.= "$loop_indent			\$new_$cc = \$key_$cc;\n";
				$loop_in	.= "$loop_indent		}\n";

				$loop_in3a	.= "\$key_count_${cc}{\$key_$cc}++;\n";

				$loop_out	.= "$loop_indent	}\n";
				$loop_out	.= "$loop_indent		\$must_do -= \$must_inc;\n";
				$loop_out2	.= "$loop_indent	}\n";

				$loop_indent	.= "\t";

				$esub		.= "->{$var_value{$cc}}";
				$newsub		.= "->{\$new_$cc}";
				$oldsub		.= "->{\$key_$cc}";
			};
			for my $in3a (split(/\n/, $loop_in3a)) {
				$loop_in3 .= "$loop_indent		$in3a\n";
			}

			$loop_out = join("\n", reverse split(/\n/, $loop_out)) . "\n";
			$loop_out2 = join("\n", reverse split(/\n/, $loop_out2)) . "\n";

			#
			# Reduce the number of contexts
			#

			$cross_key_reduce_func = sub {
				my ($keyname, $valcounts, $simplify_func) = @_;
				my %ret;
				if (keys %$valcounts > $agg_config->{crossproduct}{$keyname}) {
					$do_reduce = 1;
					my $limit = $agg_config->{crossproduct}{$keyname};
					my $current = keys %$valcounts;
					my %seen;
					my %new;
					for my $val (sort { $valcounts->{$a} <=> $valcounts->{$b} } keys %$valcounts) {
						if ($current > $limit) {
							my $new = $simplify_func->($val, $keyname);
							next if $new eq $val;
							if ($seen{$new}++) {
								$current--;
							}
							$new{$new}++;
							if ($new{$val}) {
								# we can't throw this one away since we have new
								# users...  we may not be able to meet our contract.
								$current-- unless --$seen{$new};
								$new{$new}--;
								next;
							} else {
								$ret{$val} = $new;
							}
						}
					}
				}
				print STDERR YAML::Dump("reduce $keyname", \%ret) if $agg_config->{debug} > 2;
				return \%ret;
			};

			my $db1 = '';
			my $db2 = '';
			$db1 = qq{print STDERR "Merging\t$loop_dbug_old (\$cross_data${oldsub}->{item_counter})\tinto\t$loop_dbug_new\t\$cross_count\\n";} if $agg_config->{debug};
			$db2 = qq{print STDERR "Moving\t$loop_dbug_old (\$cross_data${oldsub}->{item_counter})\tto\t$loop_dbug_new\\n";} if $agg_config->{debug};
			$s{cross_reduce} .= resume_line_numbering;

			$s{cross_reduce} .= "\t\$do_reduce = 0;\n";
			$s{cross_reduce} .= "\tmy \$must_do = 0;\n";
			$s{cross_reduce} .= $loop_head;
			$s{cross_reduce} .= $loop_in2;
			$s{cross_reduce} .= $loop_in3;
			$s{cross_reduce} .= $loop_out2;
			$s{cross_reduce} .= $loop_mid;
			$s{cross_reduce} .= $loop_in;
			$s{cross_reduce} .= eval_line_numbers(<<END_CR);
				if (\$must_do) {
					if (\$cross_data$newsub) {
						\$cross_count--;
						$db1
						\$ps = \$cross_data$newsub;
						\$oldps = delete \$cross_data$oldsub;
						#
						# print STDERR "ABOUT TO MERGE: \$key_color \$key_size \$key_style \$oldps\\n";
						# print STDERR YAML::Dump("Pre-mege cross-data", \$cross_data);
						#
						&\$merge_func;
						\$ps = \$contexts[-1];
					} else {
						$db2
						\$cross_data$newsub = delete \$cross_data$oldsub;
					}
				}
END_CR
			$s{cross_reduce} .= resume_line_numbering;
			$s{cross_reduce} .= $loop_out;

			#
			# Add data to the right context
			#
			my $db3 = '';
			$db3 = qq{print STDERR "Cross-count: \$cross_count\\n";} if $agg_config->{debug} > 3;
			$s{crossproduct} .= eval_line_numbers(<<END_CP);
				if (\$cross_count > \$cross_limit * 2) {
					&\$cross_reduce_func;
				}
				if (\$cross_data$esub) {
					\$ps = \$cross_data$esub;
				} else {
					&\$new_ps_func;
					\$cross_data$esub = \$ps;
					\$cross_count++;
					$db3
				}
END_CP
			$s{crossproduct} .= resume_line_numbering;

			#
			# Return the cross product results
			#
			$s{finish_cross} .= qq{print STDERR "Finish cross called\n";} if $agg_config->{debug} > 7;
			$s{finish_cross} .= qq{print STDERR YAML::Dump('cross_data-before',\$cross_data);\n} if $agg_config->{debug} > 8;
			$s{finish_cross} .= "my (\$retref) = shift;\n";
			$s{finish_cross} .= "&\$cross_reduce_func;\n";
			$s{finish_cross} .= qq{print STDERR YAML::Dump('cross_data-after',\$cross_data);\n} if $agg_config->{debug} > 8;
			$s{finish_cross} .= $loop_in2;
			$s{finish_cross} .= eval_line_numbers(<<END_FC);
				local(\$Stream::Aggregate::Stats::ps) 
					= \$ps
					= \$cross_data$oldsub;
				confess unless \$ps;
				\$suppress_result = 0;
				\$row = { &\$context_columns_func $loop_mid3 };
				&\$final_values_func;
				push(@\$retref, \$row) unless \$suppress_result;
				\$oldps = delete \$cross_data$oldsub;
				\$ps = \$contexts[-1];
				&\$merge_func if \$ps;
				\$cross_count--;
				$db3
END_FC
			$s{finish_cross} .= resume_line_numbering;
			$s{finish_cross} .= $loop_out2;
		}

		$code .= eval_line_numbers(<<'END_FIELDS');
			my $compile_user_code = sub {
				my ($c, $field, $config_key, $default) = @_;
				return $default unless defined $c->{$field};
				my $config = $c->{$config_key} || {};   # maybe used by eval
				my $coderef;
				my $code = qq{#line 2001 "FAKE-$extra->{name}-$field"\n sub { $c->{$field} }; };
				my $sub = eval $code;
				die "Cannot compile user code for $extra->{name}/$field: $@\n$code" if $@;
				return $coderef if $coderef;
				return $sub;
			};

			$get_context_func	= $compile_user_code->($agg_config, 'context',			'context_config',		sub { return () });
			$context_columns_func	= $compile_user_code->($agg_config, 'context2columns',		'context2columns_config',	sub { return () });
			$filter_func	        = $compile_user_code->($agg_config, 'filter',			'filter_config',		sub { 1 });
			$preprocess_func	= $compile_user_code->($agg_config, 'preprocess',		'preprocess_config',		sub {});
			$stringify_func		= $compile_user_code->($agg_config, 'stringify_context',	'stringify_context_config',	sub { map { ref($_) ? Dump($_) : $_ } @_ });
			$finalize_result_func	= $compile_user_code->($agg_config, 'finalize_result',		'finalize_result_config',	sub {});
			$passthrough_func	= $compile_user_code->($agg_config, 'passthrough',		'passthrough_config',		sub { return () });
			$user_new_context_func	= $compile_user_code->($agg_config, 'new_context',		'new_context_config',		sub { return () });
			$user_merge_func	= $compile_user_code->($agg_config, 'merge',			'merge_config',			sub { return () });
			$user_reduce_func	= $compile_user_code->($agg_config, 'reduce',			'reduce_config',		sub { return () });
END_FIELDS
		$code .= "\t\$itemref = \\$agg_config->{item_name};\n";
		$code .= "}\n";

		#
		# New context ($ps) allocator 
		#

		$s{new_ps} .= "\t\$ps = {};\n";
		$s{new_ps} .= "\t\$ps->{item_counter} = 0;\n";
		$s{new_ps} .= "\t\$ps->{heap} = {};\n" 
			if Dump($agg_config) =~ /\{heap\}/;
		if ($has_keepers) {
			$s{new_ps} .= "\t\$ps->{random} = [];\n";
			$s{new_ps} .= "\t\$ps->{sidestats} = {};\n"; # for Stream::Aggregate::Stats
		}
		$s{new_ps} .= "\t\$ps->{unfiltered_counter} = 0;\n"		if $agg_config->{filter};
		$s{new_ps} .= "\t&\$initialize_func;\n"				if $s{initialize};
		$s{new_ps} .= "\t&\$user_new_context_func;\n"			if $agg_config->{new_context};
		$s{new_ps} .= "\tlock_keys(%\$ps);\n";

		#
		# main processing loop, generated for execution efficiency
		#

		$s{process} .= "\t\$last_item = \$\$itemref;\n"
			if Dump($agg_config) =~ /\$last_item\b/;
		$s{process} .= eval_line_numbers(<<'END_P0');
			$last_item = $$itemref;
			($$itemref) = @_;
			my @ret;
			unless ($$itemref) {
				$finish_cross_func->(\@ret) if keys %$cross_data;
				$finish_context_func->(\@ret) 
					while @contexts;
				return @ret;
			}
END_P0
		$s{process} .= eval_line_numbers(<<'END_P1') if $agg_config->{preprocess};

			&$preprocess_func;

END_P1
		$s{process} .= eval_line_numbers(<<'END_P2') if $agg_config->{filter};

			$count_this = $agg_config->{filter_early}
				? &$filter_func
				: 1;
END_P2
		$s{process} .= eval_line_numbers(<<'END_P3') if $agg_config->{passthrough};

			push(@ret, &$passthrough_func);

END_P3
		$s{process} .= eval_line_numbers(<<'END_P4') if $agg_config->{filter};

			if ($count_this) {

END_P4
		$s{process} .= eval_line_numbers(<<'END_P5') if $agg_config->{context};

				my @new_context = &$get_context_func;
				my @new_strings = $stringify_func->(@new_context);

				my $diffpos = list_difference_position(@new_strings, @context_strings);

				if (defined $diffpos) {
					$finish_context_func->(\@ret)
						while @current_context >= $diffpos;
				}

				while (@new_context > @current_context) {
					$add_context_component_func->($new_context[@current_context], $new_strings[@current_context]);
				}
END_P5

		$s{process} .= eval_line_numbers(<<'END_P7') if $agg_config->{filter};
			}

			$ps->{unfiltered_counter}++;

			$count_this = &$filter_func if ! $agg_config->{filter_early};

			if ($count_this) {
END_P7
		
		$s{process} .= eval_line_numbers(<<'END_P8');
				&$count_func;
				$ps->{item_counter}++;
END_P8
		$s{process} .= eval_line_numbers(<<'END_P9') if $agg_config->{filter};
			}
END_P9
		$s{process} .= eval_line_numbers(<<'END_P10');
			return @ret;
END_P10
		$s{process} .= resume_line_numbering;

		#
		# Merge contexts func
		#

		$s{merge0} .= "print STDERR YAML::Dump('MERGE', \$ps, \$oldps);\n" if $agg_config->{debug} > 11;
		$s{merge0} .= resume_line_numbering;
		$s{merge0} .= "\t\$ps->{item_counter} += \$oldps->{item_counter};\n";
		$s{merge0} .= "\t\$ps->{unfiltered_counter} += \$oldps->{unfiltered_counter};\n" if $agg_config->{filter};
		$s{merge3} .= resume_line_numbering;
		$s{merge3} .= "\t&\$user_merge_func;\n";

		$s{fv_setup} .= "print STDERR YAML::Dump('final_values', \$ps);\n" if $agg_config->{debug} > 12;

		$code .= $assemble_code->('', qw(user));
		$code .= $assemble_code->('merge', qw(merge0 merge merge2 merge3));
		$code .= $assemble_code->('cross_reduce', qw(cross_reduce));
		$code .= $assemble_code->('finish_cross', qw(finish_cross));
		$code .= $assemble_code->('new_ps', qw(new_ps));
		$code .= $assemble_code->('process', qw(process));
		$code .= $assemble_code->('initialize', qw(initialize));
		$code .= $assemble_code->('final_values', qw(fv_setup output stat final_values));
		$code .= $assemble_code->('count', qw(precount count ephemeral0 ephemeral ephemeral2 crossproduct ephemeral3 keep standard_deviation median dominant counter percentage sum mean median min minstr max maxstr count2 keeper1 keeper2 keeper3 ));
		$code .= $assemble_code->('reduce', qw(reduce reduce2));
		die "INTERNAL ERROR: ".join(' ', keys %s) if keys %s;

		if ($suppress_line_numbers) {
			$code =~ s/^#line \d+ ".*"\s*?\n//mg;
		}

		print STDERR $line_numbers{$code}."\n" if $agg_config->{debug};

		eval $code;
		die "$@\n$line_numbers{$code}" if $@;

	};

	&$compile_config;

	$add_context_component_func = sub {
		my ($component, $component_string) = @_;

		&$new_ps_func;

		# keep @contexts and @current_context together
		push(@current_context, $component);
		push(@context_strings, $component_string);
		push(@contexts, $ps);

		$items_seen[$#contexts] += 1;
		$#items_seen = $#contexts;
		push(@items_seen, 0);
	};

	$finish_context_func = sub {
		my ($retref) = @_;

		die unless @contexts;

		print STDERR "about to call finish cross\n" if $agg_config->{debug} > 5;
		$finish_cross_func->($retref);

		die unless @contexts;

		confess unless ref $ps;

		$suppress_result = 0;
		$row = {
			&$context_columns_func,
		};
		&$final_values_func;

		# keep @contexts and @current_context together
		$oldps = pop(@contexts);
		pop(@current_context);
		pop(@context_strings);

		$ps = $contexts[-1];

		&$merge_func if $ps;

		push (@$retref, $row) unless $suppress_result;
	};

	return $process_func;

}

sub validate_aggregation_config
{
	my ($agg_config) = @_;
	my $checker = eval config_checker_source;
	die $@ if $@;
	$checker->($agg_config, $prototype_config, '- Stream::Aggregate config');
}

1;

__END__

=head1 NAME

 Stream::Aggregate - generate aggregate information from a stream of data

=head1 SYNOPSIS

 use Stream::Aggregate;

 my $af = generate_aggregation_func($agg_config, $extra_parameters, $user_extra_parameters);

 while ($log = ???) {
	@stats = $af->($log);
 }
 @stats = $af->(undef);

=head1 DESCRIPTION

Stream::Aggregate is a general-purpose aggregation module that will aggregate from a 
stream of perl objects.  While it was written specifically for log processing, it can be used
for other things too.  The input records for the aggregator must be sorted in the order
of the contexts you will aggregate over.   If you want to count things by URL, then you
must sort your input by URL.

Aggregation has two key elements: how you group things, and what you aggregate.  This module
understands two different ways to group things: nested and cross-product.

Nested groupings come from processing sorted input: if you have three fields you are 
considering your context, the order in which the data is sorted must match the order in
which these fields make up your context.

Cross-prodcut groupings come from processing unsorted input.  Each combination of values
of the fields that make up your context is another context.  This can lead to memory 
exhaustion so you must specify the maximum number of values for each of the fields.

=head2 Nested groupings

Nested groups are most easily illustrated with a simple example: aggregating by year,
month, and day.  The input data must be sorted by year, month, and day.  A single time
sort will do that, but other combinations aren't so easy.  The current context is
defined by the tiplet: (year, month, day).  That triplet must be returned by the
C<context> code.  It is stored in the C<@current_context> array.  When a context is
finished, it must be converted into a hash by C<context2columns>.

Doing it this way, you can, for example, get the average depth per day, per month, and
per year in one pass though your data.

=head2 Cross-Product grouping

Cross Product grouping does not depend on the sort order of the input and can have
many contexts active at the same time.  

For example, if you're aggregating sales figures for shoes and want statistics for
the combinations of size, width, and color there isn't a sort or nesting order that will
answer your questions.

Use C<crossproduct> to limit yourself to a certain number of values for each variable
(say 10 sizes, 3 widths, and 5 colors).

=head2 API

The configuration for Stream::Aggregate is compiled into a perl function which is
then called once for each input object.  Each time it is called, it may produce one or more
aggregate objects.  When there is no more input data, call the function with C<undef>.

The generate-the-function routine, C<generate_aggregation_func> takes three parameters.  The
first is the configuration object (defined below) that is expected (but not required) to come
from a YAML file.   The second and third provide extra information.  Currently they are only used
to get a description of what this aggregation is trying to do using the C<name> field.  Eg:

 generate_aggregation_func($agg_config, $extra, $user_extra);

 my $code = qq{#line 1 "FAKE-all-code-for-$extra->{name}"\n};

The configuration object for Stream::Aggregate is expected to be read from a YAML
file but it does not have to come in that way.

For some of the code fields (below), marked as B<Closure/Config>, you can
provide a closure instead of code.  To do that, have a C<BEGIN> block set
C<$coderef> to the closure.  If set, code outside the C<BEGIN> block
will only be compiled (never run).  When evalutating the BEGIN block, 
C<$agg_config> will be set to the value of I<key_config> (assuming the field was I<key>).

The behavior of C<generate_aggregation_func> in array connect may change in the future to
provide additional return values. 

=head2 CONTEXT-RELATED CONFIGURATION PARAMETERS

As the aggregator runs over the input, it needs to know the boundries of the contexts 
so that it knows when to generate an aggregation result record.

For nested groupings,
to aggregate over URLs, you need to sort your input by URL and you need to 
define a C<context> that returns the URL:

 context: |
   return ($log->{url})

If you want to aggregate over both the URL and the web host, the C<context> 
must return an array: host & URL:

 context: |
   $log->{url} =~ m{(?:https?|ftp)://([^/:]+)}
   my $host = $1;
   return ($host, $log->{url})

When the context is has multiple levels like that, there will be a resultant
aggregation record for each level.  

=over 23

=item context

B<Code, Optional>.  Given a C<$log> entry, return an array that describes the aggregation context.  For
example, for a URL, this array might be: domain name; host name (if different from domain name);
each component of the path of the URL except the final filename.   As Aggregate runs, it will
generate an aggregation record for each element of the array.

This code will be invoked on every input record.

=item context2columns

B<Code, Optional>.
Given a context, in C<@current_context>, return additional key/value pairs for the resulting 
aggregation record.  This is how the context gets described in the aggregation results
records.

This code will be invoked to generate resultant values just before a context is closed.

If this code sets the variable C<$suppress_result>, then this aggregation result will be
discarded.

=item stringify_context

B<Code, Optional>.

If the new context array returned by the C<context2columns> code
(soon to become C<@current_context>) is not an array of
strings but rather an array of references, it will be turned into strings using
YAML.

If this isn't what you want, use C<stringify_context> to do something different.
Unlike most of the other functions, C<stringify_context> operates on C<@_>.

This will be invoked for every input record.

=item crossproduct

B<Hash, Name-E<gt>Number, Optional>.

For crossproduct groupings, this defines the dimensions.   The keys are the variables.
The values are the maximum number of values for each variable to track.

The keys must be C<ephemeral0>, C<ephemeral>, or C<ephemeral2> column names.

=item simplify

B<Hash, Name-E<gt>Code, Optional>.

When a cross-product key is exceeding its quota of values, the default replacement
value is C<*>.  This hash allows you to override the code that chooses the new
value.

=item finalize_result

B<Code, Optional, Closure/Config>.

This code will be called after the resultant values for a context have been calculated.
It is a last-chance to modify them or to suppress the results.  The values can be found
as a reference to a hash: C<$row>.  To suppress the results, set C<$suppress_results>.

=item new_context

B<Code, Optional, Closure/Config>.

This code will be called each time there is a new context.  At the time it is called, 
C<$ps> is a reference to the new context, but C<@current_context> will not yet have been
updated.

=item merge

B<Code, Optional, Closure/Config>.

When using multiple levels of contexts, data is counted for the top-most context layer
only.  When that top-most layer finishes, the counts are merged into the next more-general
layer. 

During the merge there is both C<$ps> and C<$oldps> available to for code to reference.

=back

=head2 CONTROL FLOW CONFIGURATION

=over 23

=item filter

B<Code, Optional>.
Before any of the columns are calculated or any of the values saved, run this filter
code.  If it returns a true value then proceed as normal.  If it returns a false value,
then do not consider it for any of the statistics values.   The filter code an remember
things in C<$ps->{heap}> that might effect how other things are counted.  Filtered 

In some situations, you many want to throw away most data and count things in the
filter.  When doing that, it may be that all of the columns come from 
C<output>.

B<This may be redesigned, avoid using for the time being>.

=item filter_early

B<Boolean, Optional>, default C<false>.
Check the filter early before figuring out contexts?  If so, and the result is
filtered, don't check to see if the context changed.

=item passthrough

B<Code, Optional>.
Add results to the output of the aggregation.  A value of C<$log> adds the input
data to the output.

=back

=head2 PARAMETERS CONFIGURATION

=over 23

=item max_stats_to_keep

B<Number, Optional>, default: 4000.

When aggregating large amounts of data, limit memory use by throwing away some of the
data.  When data is thrown away, keep this number of samples for statistics functions
that need bulk data like standard_deviation.

=item reduce

B<Code, Optional, Closure/Config>.

When C<max_stats_to_keep> is exceeded, data will be thrown away.  This function
will be called when that has happened.

=item preprocess

B<Code, Optional>.
Code to preprocess the input C<$log> objects.

=item item_name

B<String, Optional>, default: C<$log>.
In the rest of the code, use call the input data something other than C<$log>.   This
anticipates using this module for something other than log data.

=item debug

B<Boolean, Optional>.
Print out some debugging information, including the code that is generated for 
building the columns.

=back

=head2 AGGREGATE OUTPUT COLUMNS CONFIGURATION

Each of these (except C<ephemeral> & C<keep>) defines additional columns of
output that will be included in each aggregation record.   Thse are all optional and
all defined as key/value pairs where the keys are column names and the values are perl
code.  You can refer to previous columns using the variable 
C<$column_I<column_name>> where I<column_name> is the name of one of the other
columns.   When refering to other columns, the order in which columns are processed
matters: C<ephemeral> and C<keep> are processed first and second respecively.
Idential code fragments will be evaluated only once.  Within a group, columns are
evaluated alphabetically.

Some of the columns will have their code evaluated per-item and some are evaluated per-aggregation.

The input data is in C<$log> unless overriden by C<item_name>.

=head3 Per item callbacks

=over 23

=item ephemeral

These columns will not be included in the aggregation data.  Refer to them
as C<$column_I<column_name>>.

=item ephemeral0

Same as C<ephemeral>, will be evaluated before C<ephemeral>.

=item ephemeral2

Same as C<ephemeral>, will be evaluated after C<ephemeral>.

=item counter

Keep a counter.  Add one if the code returns true.

=item percentage

Keep a counter.  Include the percentage of items for which the code returned
true as an output column as opposed to the number of items where the code
return C<0>.  A return value of C<undef> does not count at all.

=item sum

Keep an accumulator.  Add the return values.

=item mean

Keep an accumulator.  Add the return values.
Divide by the number of items before inserting into the results.
Items whose value is C<undef> do not count towards the number of items.

=item standard_deviation

Remeber the return values.  Compute the standard deviation of the
accumulated return values and insert that into the results.
Items whose value is C<undef> are removed before calculating the
standard_deviation.

=item median

Remeber the return values.  Compute the median of the
accumulated return values and insert that into the results.
Items whose value is C<undef> are removed before calculating the
median.

=item dominant

Remeber the return values.  Compute the mode (most frequent) of the
accumulated return values and insert that into the results.
Items whose value is C<undef> are removed before calculating the
mode.

=item min

Keep a minimum value.  
Replace it with the return value if the return value is
less
than the current value.
Items whose value is C<undef> are removed before calculating the min.

=item max

Keep a maximum value.  
Replace it with the return value if the return value is
greater
than the current value.
Items whose value is C<undef> are removed before calculating the max.

=item minstr

Keep a minimum string value.  
Replace it with the return value if the return value is
less
than the current value.
Items whose value is C<undef> are removed before calculating the minstr.

=item maxstr

Keep a maximum string value.  
Replace it with the return value if the return value is
greater
than the current value.
Items whose value is C<undef> are removed before calculating the maxstr.

=item keep

Remember the return values.   The return values are 
available at aggregation time as 
C<@{$ps-E<gt>{keep}{column_name}}>.
Items whose value is C<undef> are kept but they're ignored 
by L<Stream::Aggregate::Stats> functions.

=back

=head3 Per aggregation result record callbacks

For code that is per-aggregation, the saved aggregation state can be found in C<$ps>.  One item that
is probably needed is C<$ps-E<gt>{item_count}>.

=over 23

=item output

Extra columns to include in the output.  This is where to save C<$ps-E<gt>{item_count}>.

=item stat

Use arbitrary perl code to compute statistics on remembered
return values kept with C<keep>.  Write your own function or
use any of the functions in L<Stream::Aggregate::Stats>
(the global variable is pre-loaded).    No, there isn't any
difference between this and C<output>.

=back

=head2 VARIALBES AVAILABLE FOR CODE SNIPPETS TO USE

The following variables are available for the code that generates per-item and 
per-aggregation statistics:

=over 23

=item $log

The current item (unless overridden by C<item_name>)

=item $ps-E<gt>{keep}{column_name}

An array of return values kept by C<keep>.

=item $ps-E<gt>{numeric}{column_name}

If L<Stream::Aggregate::Stats> functions are called, they will grab the 
numeric values from C<$ps-E<gt>{keep}{column_name}> and store them in
C<$ps-E<gt>{numeric}{column_name}>

=item $ps-E<gt>{random}

For each kept item in C<$ps-E<gt>{keep}{column_name}>,
there is a corrosponding item in $ps-E<gt>{random} that is
a random number.  These random numbers are used to determine
which values to keep and which values to toss if there are too
many values to keep them all.

=item $ps-E<gt>{$column_type}{column_name}

For each type of column (output, counter, percentage, sum, min,
standard_deviation, median, stat) the values that will be part
of the final aggregation record.

=item $ps-E<gt>{$tempoary_type}{column_name}

Some columns need temporary storage for their values:
percentage_counter (the counter used by percentage);
percentage_total (the number of total items);
mean_sum (the sum used to compute the mean);
mean_count (the number of items for the mean).

=item $ps-E<gt>{heap}

A hash that can be used by the configured perl code for whatever
it wants.

=item $ps-E<gt>{item_counter}

The count of items.

=item $agg_config

The configuration object for Stream::Aggregate

=item $itemref

A reference to C<$log>.  It's always C<$itemref> even if C<$log> is
something else.

=item @current_context

The current context as returned by C<context>.

=item @context_strings

The string-ified version C<@current_context> as returned by 
C<stringify_context> or L<YAML>.

=item @contexts

The array of context objects.  C<$ps> is always C<$context[-1]>.

=item @items_seen

An array that counts the number of rows of output from this aggregation.
When the context is multi-level, the counter is multi-level.  For example,
if the context is I<domain>, I<host>, and I<URL>; then 
C<$items_seen[0]> is the number of I<domains> (so far), and 
C<$items_seen[1]> is the number of I<hosts> for this I<domain> (so far), 
and C<$items_seen[2]> is the number of I<URLs> for this I<host> (so far).

Passthrough rows do not count.

=item $row

When gather results, the variable that holds them is a reference to
a hash: C<$row>.

=item $suppress_result

After gathering results, the C<$suppress_result> variable is examined.
If it's set the results (in C<$row>) are discards.

To skip results that aren't crossproduct results, 
in C<finalize_result>, set C<$suppress_result> if C<$cross_count> isn't true.

=item $cross_count

The number of currently active crossproduct accumulator contexts.

=item $extra, $user_extra

The additional paramerts (beyond C<$agg_config>) that were passed to 
C<generate_aggregation_func()>.

=item %persist

This hash is not used by Stream::Aggregate.  It's available for
any supplied code to use however it wants.

=item $last_item

A refernece to the previous C<$log> object.  This is valid during 
C<finalize_result> and C<context2columns>.

=back

There are more.  Read the code.

=head2 HELPER FUNCTIONS

The following helper functions are available: 
everything in L<Stream::Aggregate::Stats> and:

=over

=item nonblank($value)

Returns $value if $value is defined and not the empty string.   Returns undef otherwise.

=back

=head1 LICENSE

This package may be used and redistributed under the terms of either
the Artistic 2.0 or LGPL 2.1 license.

