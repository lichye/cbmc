#!/usr/bin/env bash
# Run once per solver inside a dedicated cgroup v2 scope capped at 32 GiB.
# Usage: plena-bound-one.sh EBMC CASE_ROOT boolector|bitwuzla RESULTS
set -euo pipefail
ulimit -c 0
: "${TMPDIR:?set the temporary directory before running EBMC}"
ebmc=$(realpath "$1")
root=$(realpath "$2")
solver=$3
results=$4
case "$solver" in boolector|bitwuzla) ;; *) exit 2 ;; esac
group=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
[[ $(cat "$group/memory.max") == 34359738368 && $(cat "$group/memory.swap.max") == 0 ]]
mkdir -p "$results"
top=plena_csr_reset_spec
flags=(--systemverilog --undriven seq -D SYNTHESIS)
for dir in '' /src/definitions /src/memory/HBM/TileLink_Lib /src/memory/{scalar,vector}_sram/rtl; do
  flags+=(-I "$root/rtl$dir")
done
rc=0
/usr/bin/time -f 'elapsed_s=%e peak_rss_KiB=%M exit=%x' -o "$results/$solver.time" \
  timeout 300 "$ebmc" "${flags[@]}" --top "$top" --reset "$top.rst" --bound 1 \
    --property "$top.csr_c_set_addr_reg_a0" --"$solver" "$root/rtl/plena_unit.sv" \
    "$root/spec/$top.sv" >"$results/$solver.log" 2>&1 || rc=$?
cat "$group/memory.peak" >"$results/$solver.peak"
cat "$results/$solver.time"
grep -F "[$top.csr_c_set_addr_reg_a0]" "$results/$solver.log" || exit 1
case "$rc" in
  0) grep -q ': PROVED up to bound 1$' "$results/$solver.log" ;;
  10) grep -q ': REFUTED$' "$results/$solver.log" ;;
  *) exit "$rc" ;;
esac
