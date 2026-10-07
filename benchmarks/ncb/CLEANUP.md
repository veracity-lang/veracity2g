# Deletion candidates in `benchmarks/ncb/`

None of these files is referenced by `scripts/run_tests.sh`, `scripts/emit_tasks.sh`,
`reports/*.py`, `src/test/`, or the README. Nothing has been deleted yet.

## Drafts and stale copies superseded by a file in use

| File | Superseded by | Why delete |
|------|---------------|------------|
| `old-motivation.vcy` | `motivation.vcy` | Earlier version of the running example (condition `i_2 != i_1 && x != 1 \|\| x == 1`). |
| `template.vcy` | `multi-blocks.vcy` | Same hashtable/files blocks `f1`–`f6`, in an older syntax (bare labels, a grouped `{f4, f5, f6}` entry). |
| `vote-run-temp.vcy` | `vote-run.vcy` | "temp" copy. It also reads `proposals`, which is never declared. |
| `blockchain-erc20.vcy` | `blockchain-erc20-1dArray.vcy` | Pseudocode that won't parse: `int_of_string()` with no argument, undeclared `i`, `j`, `nAgents`, `maxSpend`, `account`, and calls to undefined `calc`/`calc2`. |
| `simple-vector2.vcy` | `simple-vector.vcy` | `for`-loop/`havoc` variant. It declares `z` but never uses it, and the `(c)` parameters in the condition don't match the bare `f1:`/`f2:` labels. |
| `simple_vector_while.vcy` | `simple-vector.vcy` | `while` variant with an out-of-bounds read: `x[size-m]` at `m = 0`. |
| `simple-vector-err.vcy` | `simple-vector.vcy` | Same program without `scalingfactor`/`busy_wait`. The `-err` suffix suggests it reproduced a bug. Check that the bug is fixed before deleting. |
| `simple_frags.vcy` | `simple-vector.vcy` / `motivation.vcy` | Uses `n`, which is never declared. The condition is over `c` but the blocks are bare labels. |
| `array.vcy` | `motivation.vcy`, `multi-blocks.vcy` | Early DSWP demo with hand-placed `mutex_lock`s and pasted-in inferred conditions. Lock synthesis now produces these locks automatically. |

## Early PS-DSWP sketches (superseded by `ps-dswp-ek.vcy`, which `emit_tasks.sh` uses)

| File | Why delete |
|------|------------|
| `ps-dswp.vcy` | Won't type-check: it assigns `int[]` values to `hashtable[string,int[]]` variables and applies `!` to an `int`. Only a usage comment in `src/vcy/codegen_c.ml:135` mentions it; update that comment if this file is deleted. |
| `ps-dswp-arr.vcy` | Uses undeclared `q` and `p_inner_list`. The loop increments `id` instead of `p`, so it never terminates. |
| `notes.vcy` | Not a program. These are hand-written TASK 0–3 notes on how `ps-dswp-ek.vcy` decomposes. Move them into a comment in `ps-dswp-ek.vcy` if they're worth keeping. |

## `veracity/`: copies that `reports/speedup_gen_veracity.py` doesn't run

The script runs the other 26 files in this folder. These 3 are only modified copies of
the originals in `benchmarks/inferred/` (and `verify/` / `invariants/`):

| File | Original |
|------|----------|
| `veracity/nested-counter.vcy` | `benchmarks/inferred/nested-counter.vcy` |
| `veracity/nested.vcy` | `benchmarks/inferred/nested.vcy` |
| `veracity/pullPayment.vcy` | `benchmarks/inferred/pullPayment.vcy` |

Also, `speedup_gen_veracity.py` has a commented-out line for `veracity/basic-matrix.vcy`,
which doesn't exist. Delete that line as well.

## Moved to `test/` (kept)

These are small programs that each exercise one feature or one subcommand on a
known example. They aren't wired into any script yet.

| File | Exercises |
|------|-----------|
| `forall.vcy` | A `forall` quantifier in a commutativity condition |
| `arguments.vcy` | Block parameters vs. condition variables (`i1 == i2 && b == 1`) |
| `sec5.vcy` | A block nested under an `if` (small example, presumably from §5) |
| `simple_if.vcy`, `nested_if.vcy`, `nested_if_loop.vcy` | Control flow with an empty `commutativity {}` section (PDG/DSWP) |
| `commset-verify.vcy`, `commset_infer.vcy` | `verify` / `infer` (`_`) on the CommSet md5 example |
| `simple-io-verify.vcy` | `verify` on the file-I/O example |
| `simple.vcy` | `infer` (`_`) with an array-indexed write |
| `vote-infer2.vcy` | `infer` on bare block labels (`{vote1}, {vote2}`), compared with `vote-infer.vcy` |
