# Deletion candidates in `benchmarks/ncb/`

The other candidates were deleted on 2026-10-07. This one is still open:

| File | Superseded by | Why it's still here |
|------|---------------|---------------------|
| `simple-vector-err.vcy` | `simple-vector.vcy` | It keeps the `x[999] = 999;` statement before `f1` that commit `d82dfb7` restored "to show error". Commit `dcae1e7` ("fix data-dependency in simple-vector", `exe_pdg.ml`) probably fixed that bug. Run this file and confirm it behaves correctly before deleting it. |

## `test/`

These are small programs that each exercise one feature or one subcommand on a known
example. They aren't wired into any script yet.

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
