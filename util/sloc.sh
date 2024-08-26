#!/usr/bin/env bash
set -e

# Change to theories directory
cd "$(dirname "$(realpath "$0")")/../theories"

# Accumulate overall totals
total_spec=0
total_proof=0

# Array to hold formatted table rows.
declare -a rows

count_slocs() {
  desc="$1"
  shift
  last_line=$(coqwc "$@" | tail -n1)

  # Get the last line from coqwc output with the totals for the given files.
  spec=$(echo "$last_line" | awk '{print $1}')
  proof=$(echo "$last_line" | awk '{print $2}')
  specproof=$((spec + proof))

  # Update the global totals
  total_spec=$((total_spec + spec))
  total_proof=$((total_proof + proof))

  # Format the table row with the data
  rows+=("$(printf "  & %-25s & %-13s & %-12s \\\\\\ %% %s" "$desc" "$spec" "$proof" "$specproof")")
}

################################################################################
# Generic
################################################################################

count_slocs "Base logic" BaseLogic.v Worlds.v
count_slocs "Infrastructure" Environment.v Instantiation.v Prelude.v Substitution.v Sub/Parallel.v Sub/Prefix.v
count_slocs "Unification" Sub/Triangular.v Unification.v
count_slocs "Monad interface" Monad/Interface.v
count_slocs "Logical relation" Related/Monad/Free.v Related/Monad/Interface.v
count_slocs "Free monad" Monad/Free.v
count_slocs "Monad interface (HOAS)" Shallow/Monad/Interface.v
count_slocs "Open modality" Open.v
count_slocs "Free monad (HOAS)" Shallow/Monad/Free.v
count_slocs "Prenex monad" Monad/Prenex.v
count_slocs "Solved monad" Monad/Solved.v
count_slocs "Prenex conversion" PrenexConversion.v

# Now print the generic table
echo "\\textbf{I} & \\textbf{Generic} & \\textbf{$total_spec} & \\textbf{$total_proof} \\\\[0.3em]"
printf "%s\n" "${rows[@]}"

################################################################################
# Specific
################################################################################

# Reset the variables
total_spec=0
total_proof=0
rows=()

count_slocs "Generators (HOAS)" Shallow/Gen/Bidirectional.v Shallow/Gen/Check.v Shallow/Gen/Synthesise.v
count_slocs "Generator (bidir)" Gen/Bidirectional.v
count_slocs "Relatedness"  Related/Gen/Bidirectional.v Related/Gen/Check.v Related/Gen/Synthesise.v
count_slocs "Generator (check)" Gen/Check.v
count_slocs "Infrastructure" InstantiationStlc*.v SubstitutionStlc*.v
count_slocs "Generator (synth)" Gen/Synthesise.v
count_slocs "Composition" Composition.v
count_slocs "Specification" Spec.v
count_slocs "Unification" UnificationStlc*.v
count_slocs "Extraction" Extraction.v

# Now print the specific table
echo "\\textbf{II} & \\textbf{Specific} & \\textbf{$total_spec} & \\textbf{$total_proof} \\\\[0.3em]"
printf "%s\n" "${rows[@]}"

