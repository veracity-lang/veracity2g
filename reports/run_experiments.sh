#!/usr/bin/env bash
# Reproduce the paper's results: speedup tables, Fig. 6 and the Tasks / Jobs /
# Avg Job Exec columns of Table 3. See "Reproducing the Paper's Results" in
# README.md.
#
# Usage: ./run_experiments.sh [trials] [--test] [benchmark...]
#   trials     trials per benchmark and N (default 5)
#   --test     run only N = 10^6 in the speedup scripts, as a quick check
#   benchmark  names from the benchmarks list in speedup_dswp.py (e.g. vote
#              erc20); runs only those. Default: the paper's six, listed in
#              DEFAULT_BENCHES below.

set -u
cd "$(dirname "$0")"

DEFAULT_BENCHES=(motivation vote simple-io multi-blocks banking erc20)

TRIALS=5
TEST=""
BENCHES=()
for a in "$@"; do
  case "$a" in
    --test) TEST="--test" ;;
    *[!0-9]*|"") BENCHES+=("$a") ;;
    *) TRIALS=$a ;;
  esac
done
[ ${#BENCHES[@]} -eq 0 ] && BENCHES=("${DEFAULT_BENCHES[@]}")

VCY=../vcy
[ -x "$VCY" ] || { echo "error: $VCY not found, run make in the repository root first" >&2; exit 1; }

# Speedup measurements (seq.csv, par.csv, ratio.csv, ratio_std.csv)
python3 ./speedup_dswp.py      out-ncbpar "$TRIALS" "${BENCHES[@]}" $TEST   # NCBPar.
python3 ./speedup_dswp_nc.py   out-nc     "$TRIALS" "${BENCHES[@]}" $TEST   # False-Comm.
python3 ./speedup_dswp_noNB.py out-noNB   "$TRIALS" "${BENCHES[@]}" $TEST   # No-NCB.

# Fig. 6
python3 ./speedup_plot_compare.py out-ncbpar out-nc out-noNB fig6 --err

# Table 3: Tasks, Jobs and Avg Job Exec at the N used for each row. The
# arguments mirror the benchmarks list in speedup_dswp.py (motivation gets
# N*100, simple-io reads files of N characters).
OUT=table3-jobstats.txt
: > "$OUT"
selected() {
  for b in "${BENCHES[@]}"; do [ "$(basename "$b" .vcy)" = "$1" ] && return 0; done
  return 1
}
job_stats() {
  local name=$1; shift
  selected "$name" || return 0
  echo "== $name" | tee -a "$OUT"
  "$VCY" interp --dswp --synthesize-locks --time --job-stats "$@" 2>&1 | tee -a "$OUT"
}

job_stats motivation   ../benchmarks/ncb/motivation.vcy   5000000000 10
N=1000000
printf A > a.txt
for f in b c d; do head -c "$N" /dev/zero | tr '\0' "$(echo $f | tr a-z A-Z)" > $f.txt; done
job_stats simple-io    ../benchmarks/ncb/simple-io.vcy    a.txt b.txt c.txt d.txt
job_stats multi-blocks ../benchmarks/ncb/multi-blocks.vcy 1000000
job_stats vote         ../benchmarks/ncb/vote.vcy         50000000
job_stats erc20        ../benchmarks/ncb/erc20.vcy        50000000 1 2
job_stats banking      ../benchmarks/ncb/banking.vcy      50000000 1000 1000

echo "Table 3 job statistics written to reports/$OUT"
python3 ./table3_latex.py "$OUT" out-ncbpar table3.tex
