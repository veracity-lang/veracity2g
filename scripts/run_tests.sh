#!/usr/bin/env bash
# scripts/run_tests.sh
#
# Runs each benchmark from reports/speedup_dswp.py once (n=1, sequential
# mode) and each lock_synth benchmark twice (plain + --synthesize-locks),
# comparing the two outputs.
#
# Usage: bash scripts/run_tests.sh
# Usually invoked via:  make test
#
# Exit code: 0 if all tests pass, 1 if any fail.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VCY="$REPO_ROOT/src/vcy.exe"

if [[ ! -x "$VCY" ]]; then
    echo "ERROR: $VCY not found or not executable. Run 'make' first." >&2
    exit 1
fi

# vcy.exe resolves benchmark paths relative to its working directory; all
# benchmark paths below are written as ../benchmarks/... so we cd to src/.
RUNDIR="$REPO_ROOT/src"

# Temp files for benchmarks that take file-path arguments.
TMPF=$(mktemp -d)
# simple-io.vcy hardcodes open_in "a.txt" relative to its working directory
# (mirroring what prep_simpleio does in speedup_dswp.py), so we create a
# copy in RUNDIR and remove it on exit.
SIMPLEIO_A="$RUNDIR/a.txt"
trap 'rm -rf "$TMPF"; rm -f "$SIMPLEIO_A"' EXIT

for letter in a b c d e f; do
    printf '%scontent\n' "$letter" > "$TMPF/${letter}.txt"
done
printf 'acontent\n' > "$SIMPLEIO_A"

PASS=0; FAIL=0

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Record a pass or fail, printing a one-line result.
_record() {
    local status="$1" label="$2" detail="$3"
    if [[ "$status" == "pass" ]]; then
        printf '  PASS  %-28s  %s\n' "$label" "$detail"
        PASS=$((PASS + 1))
    else
        printf '  FAIL  %-28s  %s\n' "$label" "$detail"
        FAIL=$((FAIL + 1))
    fi
}

# run_once LABEL BENCH_PATH [ARGS...]
#   Run the benchmark once; pass if it produces a "Return: N" line.
run_once() {
    local label="$1"; shift
    local out
    out=$(cd "$RUNDIR" && "$VCY" interp "$@" 2>&1) || true
    local ret; ret=$(printf '%s\n' "$out" | grep -o 'Return: [-0-9]*' | tail -1)
    if [[ -n "$ret" ]]; then
        _record pass "$label" "[$ret]"
    else
        local snippet; snippet=$(printf '%s\n' "$out" | head -1 | cut -c1-72)
        _record fail "$label" "[$snippet]"
    fi
}

# run_synth LABEL BENCH_PATH [ARGS...]
#   Run the benchmark twice: once plain, once with --synthesize-locks.
#   Extracts "Return: N" from anywhere in the output so that benchmarks
#   whose print statements lack trailing newlines still work correctly.
run_synth() {
    local label="$1"; shift
    local base synth
    base=$(cd "$RUNDIR" && "$VCY" interp                    "$@" 2>&1 \
          | grep -o 'Return: [-0-9]*' | tail -1) || true
    synth=$(cd "$RUNDIR" && "$VCY" interp --synthesize-locks "$@" 2>&1 \
          | grep -o 'Return: [-0-9]*' | tail -1) || true
    if [[ "$base" == "$synth" ]] && [[ -n "$base" ]]; then
        _record pass "$label" "[$base]"
    else
        _record fail "$label" "[base=$base | synth=$synth]"
    fi
}

# ---------------------------------------------------------------------------
# speedup_dswp benchmarks — run once at n=1 in sequential mode
# ---------------------------------------------------------------------------
echo ""
echo "=== speedup_dswp benchmarks (n=1, sequential) ==="

GC="../benchmarks/global_commutativity"

run_once "sollve_dotprod"       "$GC/sollve_dotprod.vcy"           1
run_once "simple-vector"        "$GC/simple-vector.vcy"            1
run_once "2d-array"             "$GC/2d-array.vcy"                 1
run_once "vote-run"             "$GC/vote-run.vcy"                 1
run_once "commset"              "$GC/commset.vcy" \
    "$TMPF/a.txt" "$TMPF/b.txt" "$TMPF/c.txt" "$TMPF/d.txt"
run_once "multi-blocks"         "$GC/multi-blocks.vcy"             1
run_once "simple-io"            "$GC/simple-io.vcy" \
    "$TMPF/a.txt" "$TMPF/b.txt" "$TMPF/c.txt" "$TMPF/d.txt"
run_once "motivation"           "$GC/motivation.vcy"               100 10
run_once "blockchain-erc20"     "$GC/blockchain-erc20-1dArray.vcy" 1 1 2
run_once "banking"              "$GC/banking.vcy"                  1 100 1000
run_once "commset-potrace"      "$GC/commset-potrace.vcy" \
    1 "$TMPF/a.txt" "$TMPF/b.txt" "$TMPF/c.txt" \
      "$TMPF/d.txt" "$TMPF/e.txt" "$TMPF/f.txt"
run_once "commset-kmeans"       "$GC/commset-kmeans.vcy"           1

# ---------------------------------------------------------------------------
# lock_synth benchmarks — run plain and with --synthesize-locks; compare
# ---------------------------------------------------------------------------
echo ""
echo "=== lock_synth benchmarks (baseline == --synthesize-locks) ==="

LS="../benchmarks/lock_synth"

# No-lock: synthesis should add 0 locks and leave the output unchanged
run_synth "ls_nolock_1"         "$LS/ls_nolock_1.vcy"  8
run_synth "ls_nolock_2"         "$LS/ls_nolock_2.vcy"  4
run_synth "ls_nolock_3"         "$LS/ls_nolock_3.vcy"  4
run_synth "ls_nolock_4"         "$LS/ls_nolock_4.vcy"  8

# NCB: locks synthesized; both runs must still agree on the return value
run_synth "ls_ncb_1"            "$LS/ls_ncb_1.vcy"     8
run_synth "ls_ncb_2"            "$LS/ls_ncb_2.vcy"     8
run_synth "ls_ncb_3"            "$LS/ls_ncb_3.vcy"     4
run_synth "ls_ncb_4"            "$LS/ls_ncb_4.vcy"     4
run_synth "ls_ncb_5"            "$LS/ls_ncb_5.vcy"     6
run_synth "ls_ncb_6"            "$LS/ls_ncb_6.vcy"     8

# New NCB benchmarks demonstrating three distinct lock patterns
run_synth "ncb_histogram"       "$GC/ncb_histogram.vcy"   8
run_synth "ncb_dot_product"     "$GC/ncb_dot_product.vcy" 4
run_synth "ncb_max_reduce"      "$GC/ncb_max_reduce.vcy"  10

# Non-NCB: pre-DSWP synthesis may or may not add locks; output unchanged
run_synth "ls_noncb_1"          "$LS/ls_noncb_1.vcy"   4
run_synth "ls_noncb_2"          "$LS/ls_noncb_2.vcy"   8
run_synth "ls_noncb_3"          "$LS/ls_noncb_3.vcy"   4
run_synth "ls_noncb_4"          "$LS/ls_noncb_4.vcy"   4

# ---------------------------------------------------------------------------
# lock_synth non-NCB benchmarks — post-DSWP synthesis (--dswp --synthesize-locks)
#
# These are the cases the pre-DSWP synthesis cannot handle; the post-DSWP
# path must detect inter-task conflicts and add the missing locks.
# Test: output with --dswp --synthesize-locks equals plain --dswp baseline.
# ---------------------------------------------------------------------------
echo ""
echo "=== lock_synth non-NCB benchmarks (post-DSWP synthesis) ==="

# run_synth_dswp LABEL BENCH_PATH [ARGS...]
#   Run with --dswp baseline and --dswp --synthesize-locks; outputs must match.
run_synth_dswp() {
    local label="$1"; shift
    local base synth
    base=$(cd "$RUNDIR" && "$VCY" interp --dswp                      "$@" 2>&1 | tail -1) || true
    synth=$(cd "$RUNDIR" && "$VCY" interp --dswp --synthesize-locks   "$@" 2>&1 | tail -1) || true
    if [[ "$base" == "$synth" ]] && printf '%s\n' "$base" | grep -q '^Return:'; then
        _record pass "$label" "[$base]"
    else
        _record fail "$label" "[base=$base | synth=$synth]"
    fi
}

# count_locks BENCH_PATH [ARGS...]  — number of mutex_lock calls synthesized
count_locks_dswp() {
    local file="$1"; shift
    cd "$RUNDIR" && "$VCY" parse --synthesize-locks "$file" 2>&1 \
        | grep -o '"mutex_lock"' | wc -l | tr -d ' '
}

# ls_noncb_1 deadlocks in --dswp (backward counter dep creates a scheduler cycle)
run_synth_dswp  "ls_noncb_2 (dswp)"  "$LS/ls_noncb_2.vcy"   8
run_synth_dswp  "ls_noncb_3 (dswp)"  "$LS/ls_noncb_3.vcy"   4
run_synth_dswp  "ls_noncb_4 (dswp)"  "$LS/ls_noncb_4.vcy"   4

# Verify pre-DSWP lock counts.
# ls_noncb_1: counter IS in the NCB conflict_set (incr blocks share it),
#   so pre-DSWP synthesis adds 2 locks — one in each of incr and adjust.
# ls_noncb_2/3/4: the DSWP data-dependency edges already serialise the
#   potentially-conflicting tasks, so no inter-task race exists and the
#   post-DSWP analysis correctly adds 0 locks (DSWP ordering is sufficient).
check_lock_count() {
    local label="$1" file="$2" expected="$3"
    local got
    got=$(cd "$RUNDIR" && "$VCY" parse --synthesize-locks "$file" 2>&1 \
          | grep -o '"mutex_lock"' | wc -l | tr -d ' ')
    if [[ "$got" -eq "$expected" ]]; then
        _record pass "$label (lock count = $expected)" "[got $got]"
    else
        _record fail "$label (lock count = $expected)" "[got $got, want $expected]"
    fi
}

check_lock_count "ls_noncb_1 pre-DSWP locks" "$LS/ls_noncb_1.vcy"  2
check_lock_count "ls_noncb_2 pre-DSWP locks" "$LS/ls_noncb_2.vcy"  0
check_lock_count "ls_noncb_3 pre-DSWP locks" "$LS/ls_noncb_3.vcy"  0
check_lock_count "ls_noncb_4 pre-DSWP locks" "$LS/ls_noncb_4.vcy"  0

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
TOTAL=$((PASS + FAIL))
if [[ "$FAIL" -eq 0 ]]; then
    echo "=== All ${TOTAL} tests passed. ==="
else
    echo "=== ${PASS}/${TOTAL} passed, ${FAIL} FAILED. ==="
fi
echo ""

[[ "$FAIL" -eq 0 ]]
