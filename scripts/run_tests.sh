#!/usr/bin/env bash
# scripts/run_tests.sh
#
# Runs each benchmark from reports/speedup_dswp.py once (n=1, sequential
# mode) and each lock_synth benchmark twice (plain + --synthesize-locks),
# comparing the two outputs.  Then, if cvc5 is installed, runs `vcy verify`
# on the NCB examples.
#
# Usage: bash scripts/run_tests.sh [--all]
# Usually invoked via:  make test   (or make test-all for --all)
# --all also runs the loop-unroll and loop-abstract checks and
# benchmarks/{verify,loops,models,prepost,movers,invariants,inferred}
# (formerly test.sh), which takes minutes.
# Set VCY=/path/to/binary to test a binary other than ./vcy.
#
# Exit code: 0 if all tests pass, 1 if any fail.

set -uo pipefail

ALL=0
case "${1:-}" in
    --all) ALL=1 ;;
    "") ;;
    *) echo "usage: $0 [--all]" >&2; exit 2 ;;
esac

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VCY="${VCY:-$REPO_ROOT/vcy}"

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

PASS=0; FAIL=0; XFAIL=0

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

GC="../benchmarks/ncb"

run_once "sollve_dotprod"       "$GC/other/sollve_dotprod.vcy"     1
run_once "simple-vector"        "$GC/other/simple-vector.vcy"      1
run_once "2d-array"             "$GC/other/2d-array.vcy"           1
run_once "vote"                 "$GC/vote.vcy"                 1
run_once "commset"              "$GC/commset.vcy" \
    "$TMPF/a.txt" "$TMPF/b.txt" "$TMPF/c.txt" "$TMPF/d.txt"
run_once "multi-blocks"         "$GC/multi-blocks.vcy"             1
run_once "simple-io"            "$GC/simple-io.vcy" \
    "$TMPF/a.txt" "$TMPF/b.txt" "$TMPF/c.txt" "$TMPF/d.txt"
run_once "motivation"           "$GC/motivation.vcy"               100 10
run_once "erc20"                "$GC/erc20.vcy" 1 1 2
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
run_synth "ncb_histogram"       "$GC/test/ncb_histogram.vcy"   8
run_synth "ncb_dot_product"     "$GC/test/ncb_dot_product.vcy" 4
run_synth "ncb_max_reduce"      "$GC/other/ncb_max_reduce.vcy" 10

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

# ls_noncb_1 needs its synthesized locks (plain --dswp races), so it is
# checked against the sequential result below instead.
run_synth_dswp  "ls_noncb_2 (dswp)"  "$LS/ls_noncb_2.vcy"   8
run_synth_dswp  "ls_noncb_3 (dswp)"  "$LS/ls_noncb_3.vcy"   4
run_synth_dswp  "ls_noncb_4 (dswp)"  "$LS/ls_noncb_4.vcy"   4

# run_dswp_vs_seq LABEL RUNS BENCH_PATH [ARGS...]
#   --dswp --synthesize-locks must return the sequential result on every one
#   of RUNS runs: a race shows up only on some interleavings.
run_dswp_vs_seq() {
    local label="$1" runs="$2"; shift 2
    local seq par bad=""
    seq=$(cd "$RUNDIR" && "$VCY" interp "$@" 2>&1 | tail -1) || true
    for _ in $(seq 1 "$runs"); do
        par=$(cd "$RUNDIR" && "$VCY" interp --dswp --synthesize-locks "$@" 2>&1 | tail -1) || true
        [[ "$par" == "$seq" ]] || bad="$par"
    done
    if [[ -z "$bad" ]] && printf '%s\n' "$seq" | grep -q '^Return:'; then
        _record pass "$label" "[$seq x$runs]"
    else
        _record fail "$label" "[seq=$seq | dswp=$bad]"
    fi
}

run_dswp_vs_seq "ls_doall_counter (dswp == seq)"     10 "$LS/ls_doall_counter.vcy"     200
run_dswp_vs_seq "ls_ncb_shared_scalar (dswp == seq)" 10 "$LS/ls_ncb_shared_scalar.vcy" 1 10
run_dswp_vs_seq "ls_noncb_1 (dswp == seq)"           5  "$LS/ls_noncb_1.vcy"           8
run_dswp_vs_seq "ls_global_induction (dswp == seq)"  10 "$LS/ls_global_induction.vcy"  20
run_dswp_vs_seq "2d-array (dswp == seq)"             5  "$GC/other/2d-array.vcy"       20

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
# NCB verify — every commutativity condition must verify as correct
# ---------------------------------------------------------------------------
echo ""
echo "=== NCB verify benchmarks (vcy verify --prover cvc5) ==="

# run_verify LABEL BENCH_PATH NCONDS
#   Pass if verify exits 0 and reports exactly NCONDS conditions as correct
#   and none as incorrect.  An incorrect condition does not change the exit
#   code, so the output is what we check.  Pinning NCONDS catches a condition
#   that is silently dropped.
run_verify() {
    local label="$1" file="$2" nconds="$3"
    local out rc ok bad
    out=$(cd "$RUNDIR" && "$VCY" verify "$file" --prover cvc5 2>&1); rc=$?
    ok=$(printf '%s\n' "$out" | grep -c 'verified as correct')
    bad=$(printf '%s\n' "$out" | grep -c 'verified as incorrect')
    if [[ "$rc" -eq 0 && "$bad" -eq 0 && "$ok" -eq "$nconds" ]]; then
        _record pass "$label" "[$ok/$nconds correct]"
    elif [[ "$rc" -ne 0 ]]; then
        local snippet; snippet=$(printf '%s\n' "$out" | grep -v '^\s*$' | tail -1 | cut -c1-72)
        _record fail "$label" "[exit $rc: $snippet]"
    else
        _record fail "$label" "[$ok correct, $bad incorrect, want $nconds correct]"
    fi
}

# known_verify_failure LABEL BENCH_PATH REASON
#   An NCB example that verify cannot handle yet.  Reported but not counted
#   as a failure; if it starts verifying, move it to run_verify.
known_verify_failure() {
    local label="$1" file="$2" reason="$3"
    local out rc
    out=$(cd "$RUNDIR" && "$VCY" verify "$file" --prover cvc5 2>&1); rc=$?
    if [[ "$rc" -eq 0 ]] && ! printf '%s\n' "$out" | grep -q 'verified as incorrect' \
        && printf '%s\n' "$out" | grep -q 'verified as correct'; then
        printf '  XPASS %-28s  %s\n' "$label" "[now verifies: move to run_verify]"
    else
        printf '  XFAIL %-28s  %s\n' "$label" "[$reason]"
    fi
    XFAIL=$((XFAIL + 1))
}

# run_loop_unroll LABEL BENCH_PATH EXPECT
#   EXPECT is correct or incorrect (the first verdict printed), nofire
#   (no loop may be unrolled, and verify must reject the loop), or reject
#   (verify must refuse a declaration that shadows a later use).
run_loop_unroll() {
    local label="$1" file="$2" expect="$3"
    local out verdict ok=0
    out=$(cd "$RUNDIR" && "$VCY" verify "$file" --prover cvc5 2>&1)
    verdict=$(printf '%s\n' "$out" | grep -o 'verified as [a-z]*' | head -1 | cut -d' ' -f3)
    case "$expect" in
        nofire)
            ! printf '%s\n' "$out" | grep -q '^Loop unrolling:' \
                && printf '%s\n' "$out" | grep -q 'cannot translate this loop' && ok=1 ;;
        reject)
            printf '%s\n' "$out" | grep -q 'used after it' && ok=1 ;;
        *)
            [[ "$verdict" == "$expect" ]] && ok=1 ;;
    esac
    if [[ "$ok" -eq 1 ]]; then
        _record pass "$label" "[$expect]"
    else
        _record fail "$label" "[verdict=${verdict:-none}, want $expect]"
    fi
}

# run_loop_abs LABEL BENCH_PATH EXPECT
#   EXPECT is correct or incorrect (the loop abstraction must fire and give
#   that verdict) or nofire (a side condition fails, so it must not fire and
#   the loop must be rejected rather than dropped).
run_loop_abs() {
    local label="$1" file="$2" expect="$3"
    local out fired verdict
    out=$(cd "$RUNDIR" && "$VCY" verify "$file" --prover cvc5 2>&1)
    fired=$(printf '%s\n' "$out" | grep -c '^Loop abstraction:')
    verdict=$(printf '%s\n' "$out" | grep -o 'verified as [a-z]*' | head -1 | cut -d' ' -f3)
    if [[ "$expect" == nofire && "$fired" -eq 0 ]] \
        && printf '%s\n' "$out" | grep -q 'cannot translate this loop' \
        || [[ "$expect" != nofire && "$fired" -eq 1 && "$verdict" == "$expect" ]]; then
        _record pass "$label" "[$expect]"
    else
        _record fail "$label" "[fired=$fired verdict=${verdict:-none}, want $expect]"
    fi
}

# The helpers below run from the repo root, with benchmark paths written as
# benchmarks/...; the label is the path without benchmarks/ and .vcy.
_label() { local l="${1#benchmarks/}"; printf '%s' "${l%.vcy}"; }

# run_exit BENCH_PATH CMD...
#   Pass if CMD exits 0.
run_exit() {
    local label; label=$(_label "$1"); shift
    local out rc
    out=$(cd "$REPO_ROOT" && "$@" 2>&1); rc=$?
    if [[ "$rc" -eq 0 ]]; then
        _record pass "$label" "[ok]"
    else
        local snippet; snippet=$(printf '%s\n' "$out" | grep -v '^\s*$' | tail -1 | cut -c1-60)
        _record fail "$label" "[exit $rc: $snippet]"
    fi
}

# run_incorrect BENCH_PATH
#   The condition is wrong: verify must report it incorrect (and so exits
#   non-zero, which is not checked).
run_incorrect() {
    local label; label=$(_label "$1")
    local out
    out=$(cd "$REPO_ROOT" && "$VCY" verify "$1" --prover cvc5 2>&1)
    if printf '%s\n' "$out" | grep -q 'verified as incorrect'; then
        _record pass "$label" "[incorrect]"
    else
        _record fail "$label" "[want incorrect]"
    fi
}

# run_table BENCH_PATH
#   The condition fails, and verify --html must write the counterexample
#   table (Model_table) somewhere under the run directory.
run_table() {
    local label; label=$(_label "$1")
    local d; d=$(mktemp -d -p "$TMPF")
    (cd "$REPO_ROOT" && "$VCY" verify "$1" --prover cvc5 --html --out-dir "$d" > /dev/null 2>&1)
    if [[ -n "$(find "$d" -name expr_table.html)" ]]; then
        _record pass "$label" "[table]"
    else
        _record fail "$label" "[no expr_table.html]"
    fi
}

# run_interp_ok BENCH_PATH [ARGS...]
#   Pass if interp reports no error (these programs print no Return line).
run_interp_ok() {
    local label; label=$(_label "$1")
    local out
    out=$(cd "$REPO_ROOT" && "$VCY" interp "$@" 2>&1)
    if printf '%s\n' "$out" | grep -q 'error occurred\|Fatal error'; then
        _record fail "$label" "[$(printf '%s\n' "$out" | grep -m1 'error occurred\|Fatal error' | cut -c1-60)]"
    else
        _record pass "$label" "[ok]"
    fi
}

# Servois2 looks for cvc5 only at fixed paths (see Provers.ProverCVC5), so
# being on $PATH is not enough.
if [[ -x /usr/local/bin/cvc5 || -x /usr/bin/cvc5 || -x /opt/homebrew/bin/cvc5 ]]; then
    run_verify "banking"            "$GC/banking.vcy"                  5
    run_verify "erc20"              "$GC/erc20.vcy" 3
    run_verify "motivation"         "$GC/motivation.vcy"               1
    run_verify "multi-blocks"       "$GC/multi-blocks.vcy"             11
    run_verify "vote"               "$GC/vote.vcy"                 6
    run_verify "simple-io"          "$GC/simple-io.vcy"                1
    run_verify "ncb_dot_product"    "$GC/test/ncb_dot_product.vcy"          1
    run_verify "ncb_histogram"      "$GC/test/ncb_histogram.vcy"            1
    # md5_lower and string_of_int have no model: uninterpreted functions.
    run_verify "commset-verify"     "$GC/test/commset-verify.vcy"      1
    # The inner 10x / nFeatures loops have literal trip counts and are unrolled.
    run_verify "commset"            "$GC/commset.vcy"                  1
    run_verify "commset-potrace"    "$GC/commset-potrace.vcy"          1
    run_verify "commset-kmeans"     "$GC/commset-kmeans.vcy"           1

    # Not verified: other/simple-vector{,-err}, other/sollve_dotprod and
    # other/ncb_max_reduce have loops that read their counter or share the
    # block with other code, so they need an invariant (see
    # known_verify_failure).  2d-array and ps-dswp have no commutativity
    # conditions; vote-infer uses `_` (infer, not verify).

    # The suites below run only with --all (make test-all).  The
    # benchmarks/ ones were test.sh; each loops over its directory, so a
    # new benchmark there is picked up without being listed.
    if [[ "$ALL" -eq 1 ]]; then
        echo ""
        echo "=== Loop unrolling and block encoding (vcy verify --prover cvc5) ==="
        LU="../benchmarks/loop-unroll"
        run_loop_unroll "lu mid-block-ok"         "$LU/mid-block-ok.vcy"         correct
        run_loop_unroll "lu param-in-loop-bad"    "$LU/param-in-loop-bad.vcy"    incorrect
        run_loop_unroll "lu nested-block-bad"     "$LU/nested-block-bad.vcy"     incorrect
        run_loop_unroll "lu counter-written"      "$LU/counter-written-nofire.vcy" nofire
        run_loop_unroll "lu shadow"               "$LU/shadow-nofire.vcy"        nofire
        run_loop_unroll "lu use-before-decl"      "$LU/use-before-decl-nofire.vcy" nofire
        run_loop_unroll "lu if-shadow"            "$LU/if-shadow-reject.vcy"     reject

        echo ""
        echo "=== Counter-loop abstraction (vcy verify --prover cvc5) ==="
        LA="../benchmarks/loop-abstract"
        run_loop_abs "la commute-ok"     "$LA/commute-ok.vcy"     correct
        run_loop_abs "la commute-cond"   "$LA/commute-cond.vcy"   correct
        run_loop_abs "la both-loops"     "$LA/both-loops.vcy"     correct
        run_loop_abs "la for-loop"       "$LA/for-loop.vcy"       correct
        run_loop_abs "la commute-bad"    "$LA/commute-bad.vcy"    incorrect
        run_loop_abs "la guard-unstable" "$LA/guard-unstable.vcy" nofire
        run_loop_abs "la phi-unstable"   "$LA/phi-unstable.vcy"   nofire
        run_loop_abs "la counter-read"   "$LA/counter-read.vcy"   nofire

        echo ""
        echo "=== benchmarks/verify (vcy verify --prover cvc5) ==="
        for f in "$REPO_ROOT"/benchmarks/verify/*.vcy; do
            f="benchmarks/${f#"$REPO_ROOT"/benchmarks/}"
            case "$f" in
                # The condition `true` is wrong: the decrement is guarded on c > 0.
                */counter.vcy)  run_incorrect "$f" ;;
                # Its loop summary uses havoc.
                */loop-amt.vcy) run_exit "$f" "$VCY" verify "$f" --prover cvc5 -ae ;;
                *)              run_exit "$f" "$VCY" verify "$f" --prover cvc5 ;;
            esac
        done

        echo ""
        echo "=== benchmarks/loops (vcy verify --prover cvc5) ==="
        for f in "$REPO_ROOT"/benchmarks/loops/*.vcy; do
            f="benchmarks/${f#"$REPO_ROOT"/benchmarks/}"
            run_exit "$f" "$VCY" verify "$f" --prover cvc5
        done

        echo ""
        echo "=== benchmarks/models (counterexample tables) ==="
        for f in seq-read-after-write array-write-conflict heap-read-after-write; do
            run_table "benchmarks/models/$f.vcy"
        done
        # Known limitation: the loop summarisation finds no counterexample, so
        # there is no model and no table.  Exit status only; see that file's header.
        run_exit benchmarks/models/loop-read-after-write.vcy \
            "$VCY" verify benchmarks/models/loop-read-after-write.vcy --prover cvc5

        echo ""
        echo "=== benchmarks/prepost (vcy infer --prover cvc5) ==="
        for f in "$REPO_ROOT"/benchmarks/prepost/*.vcy; do
            f="benchmarks/${f#"$REPO_ROOT"/benchmarks/}"
            run_exit "$f" "$VCY" infer "$f" --prover cvc5
        done

        # These have no commute blocks, so they are interpreted, not inferred.
        MOVERS_INTERP=" parse1 test-heap-smt1 test-heap-write test-interp1 test-interp2 test-interp3 "
        echo ""
        echo "=== benchmarks/movers (vcy infer --prover cvc5 -ae, or interp) ==="
        for f in "$REPO_ROOT"/benchmarks/movers/*.vcy; do
            f="benchmarks/${f#"$REPO_ROOT"/benchmarks/}"
            name=$(basename "$f" .vcy)
            if [[ "$MOVERS_INTERP" == *" $name "* ]]; then
                if [[ "$name" == test-interp3 ]]; then run_interp_ok "$f" 3
                else run_interp_ok "$f"; fi
            else
                run_exit "$f" "$VCY" infer "$f" --prover cvc5 -ae
            fi
        done

        echo ""
        echo "=== benchmarks/invariants (vcy invariants --prover cvc5) ==="
        for f in "$REPO_ROOT"/benchmarks/invariants/*.vcy; do
            f="benchmarks/${f#"$REPO_ROOT"/benchmarks/}"
            run_exit "$f" "$VCY" invariants "$f" --prover cvc5
        done

        echo ""
        echo "=== benchmarks/inferred (vcy infer --prover cvc5) ==="
        for f in "$REPO_ROOT"/benchmarks/inferred/*.vcy; do
            f="benchmarks/${f#"$REPO_ROOT"/benchmarks/}"
            [[ "$f" == *tmp.vcy ]] && continue
            run_exit "$f" "$VCY" infer "$f" --prover cvc5
        done
    else
        echo ""
        echo "=== loop-unroll, loop-abstract, benchmarks/{verify,loops,models,prepost,movers,invariants,inferred}: skipped (run make test-all) ==="
    fi
else
    echo "  SKIP  cvc5 not found in /usr/local/bin, /usr/bin or /opt/homebrew/bin"
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
TOTAL=$((PASS + FAIL))
XNOTE=""
[[ "$XFAIL" -gt 0 ]] && XNOTE=" (${XFAIL} known failures not counted)"
if [[ "$FAIL" -eq 0 ]]; then
    echo "=== All ${TOTAL} tests passed${XNOTE}. ==="
else
    echo "=== ${PASS}/${TOTAL} passed, ${FAIL} FAILED${XNOTE}. ==="
fi
echo ""

[[ "$FAIL" -eq 0 ]]
