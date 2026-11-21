#!/usr/bin/env bash
# Usage: TMPDIR=... cross-check.sh EBMC RESULTS [BASELINE_EBMC]
set -euo pipefail
ulimit -c 0
: "${TMPDIR:?set the temporary directory before running EBMC}"
ebmc=$(realpath "$1")
results=$2
baseline=${3:-}
here=$(dirname "$(realpath "$0")")
mkdir -p "$results"

invoke() {
  local binary=$1 output=$2
  status=0
  timeout 60 "$binary" --systemverilog --top main --bound 1 --property "main.$property" \
    "${flags[@]}" --trace "$here/$design.sv" >"$output" 2>&1 || status=$?
}

# Check the returned coordinates without depending on a preferred model.
check_cells() {
  awk -v test="$design" '
    function number(bits, n, j) {
      n=0
      for (j=1; j<=length(bits); j++) n=2*n+substr(bits,j,1)
      return n
    }
    /main.r =/ { sub(/^.*\047b/,""); sub(/ .*/,""); r=number($0); have_r=1 }
    /main.c =/ { sub(/^.*\047b/,""); sub(/ .*/,""); c=number($0); have_c=1 }
    /main.a =/ { reading=1 }
    reading {
      line=$0
      while (match(line,/4\047b[01][01][01][01]/)) {
        value[count++]=number(substr(line,RSTART+3,4))
        line=substr(line,RSTART+RLENGTH)
      }
      if (count==(test=="coords" ? 8 : 4)) {
        ok=(test=="coords" ? value[0]!=value[4] :
            test=="rows" ? have_r && have_c && value[2*r+c]!=0 :
            have_r && value[r]!=0)
        exit
      }
    }
    END { exit !ok }
  ' "$1"
}

for solver in boolector bitwuzla yices z3 minisat; do
  flags=()
  [[ $solver == minisat ]] || flags+=(--"$solver")
  while read -r design property verdict; do
    expected=0
    [[ $verdict == REFUTED ]] && expected=10
    log="$results/$solver-$design-$property.log"
    invoke "$ebmc" "$log"
    if [[ $status == "$expected" ]] &&
       grep -F "[main.$property] " "$log" | grep -Fq ": $verdict"; then
      if [[ $solver == boolector || $solver == bitwuzla ]]; then
        case "$design/$property" in
          oned/bad|rows/bad|coords/arbitrary) check_cells "$log" ;;
        esac
      fi
      echo "$solver $design.$property $verdict"
      continue
    fi
    # Allow a baseline diagnostic only after reproducing it with the supplied
    # pristine binary. Never count solver failure as a counterexample.
    case "$solver/$design/$property" in
      yices/boolmem/written|yices/boolmem/free) diagnosis='in store: type error' ;;
      yices/coords/arbitrary|yices/rows/bad) diagnosis='quantifiers are not allowed in logic QF_AUFBV' ;;
      *) cat "$log" >&2; exit 1 ;;
    esac
    [[ -n $baseline && $status == 10 ]]
    reference="$results/base-$solver-$design-$property.log"
    invoke "$baseline" "$reference"
    [[ $status == 10 ]]
    for file in "$reference" "$log"; do
      grep -Fq "$diagnosis" "$file"
      grep -F "[main.$property] " "$file" | grep -Fq ': FAILURE'
    done
    diff <(grep -F "$diagnosis" "$reference") <(grep -F "$diagnosis" "$log")
    echo "$solver $design.$property BASELINE-FAILURE ($diagnosis)"
  done <<'CASES'
oned good PROVED up to bound 1
oned bad REFUTED
rows good PROVED up to bound 1
rows bad REFUTED
rowcopy copy PROVED up to bound 1
rowcopy keep PROVED up to bound 1
rowcopy equal_rows PROVED up to bound 1
rowcopy free REFUTED
coords write_word PROVED up to bound 1
coords untouched PROVED up to bound 1
coords arbitrary REFUTED
bounds read_oob PROVED up to bound 1
bounds keep REFUTED
bounds no_wrap PROVED up to bound 1
equal_core entire PROVED up to bound 1
equal_core row PROVED up to bound 1
equal_core unequal REFUTED
boolmem written PROVED up to bound 1
boolmem free REFUTED
CASES
done
