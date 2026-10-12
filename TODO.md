# TODO

## SSA version names collide with user identifiers ending in `_N`

**Status:** open. `benchmarks/ncb/simple-io.vcy` works around it by renaming
`fname_1..4` to `srcA`/`dstA`/`srcB`/`dstB`.

### Problem

The spec generator names successive versions of a variable `x`, `x_1`, `x_2`, …
(`Ast.mangle_servois_id`, `src/vcy/ast.ml:243`; `src/analysis/spec_generator.ml:334,352`).
Veracity identifiers are `[a-zA-Z][a-zA-Z0-9_]*`, so a user variable such as
`x_1` is indistinguishable from version 1 of `x`.

Library calls make it worse. To find the variable behind their first argument,
they apply `remove_index` to the SMT name (`spec_generator.ml:499,760`), and
`remove_index` strips the *first* `_[0-9]+` it finds (`ast.ml:441`). In the
original `simple-io`:

- `open_read(fname_3)`, `open_write(fname_4)` and the source of
  `cp(fname_1, fname_2)` all ended up acting on the unrelated global `fname`
  (`"a.txt"`).
- Each call gave `fname` a new version named `fname_1`, then `fname_2`,
  shadowing the user's variables of the same names.

As a result, the encoded program really did conflict on `fname`, and verify
reported a spurious counterexample.

Servois2 has the same weakness one level down. It appends state suffixes
(`1`, `2`, `12`, `21`) directly to names, so `x_1` in state `2` and a variable
named `x_12` in the initial state both become `x_12`. Its own `remove_index`
(`src/servois2/src/predicate.ml:14`, used when generating terms for `infer`)
strips `_N` the same way.

### Proposed fix

1. Use a version separator that cannot appear in an identifier and is legal
   in an SMT-LIB symbol, e.g. `x!1`. Change `mangle_servois_id`, the two
   `spec_generator.ml` sites, and `remove_index` (which should strip only a
   trailing `!N`).
2. Do the same in Servois2 for `remove_index` and the state suffixes. This is
   a submodule change; bump the pointer afterwards.
3. In the library-call translation, take the target variable from the AST
   argument (`Id x`) instead of un-mangling the SMT name. That also lifts two
   current limits:
   - a literal or indexed argument (`open_read("a.txt")`, `open_read(argv[1])`)
     fails with `non string var`;
   - a block-local channel such as `in_channel c = open_read(...)` raises
     `Not_found`.
4. Stop the string-based I/O models (`open_*`, `cp`, `read_line`, `write`)
   from giving their first argument a new version (`f1 := f0`). Only the
   hashtable models need that.

### How to check

Revert `simple-io.vcy` to the `fname_1..4` names; it should still verify as
correct. Add a regression benchmark that declares both `x` and `x_1`, and
assigns `x` inside a commute block.

## `vote-run` interpreter run is vacuous

**Status:** open.

`benchmarks/ncb/vote-run.vcy` never populates `voter_weight`, `voter_voted`,
`voter_vote` or `proposals`. `ht_get` on a missing key returns null, so
`weight != 0` always holds and every vote is rejected. The `interp` test passes
without ever reaching the `proposals` updates; that is how the missing
`proposals` declaration went unnoticed. The weight check is also inverted
relative to the Solidity example it cites (`require(sender.weight != 0)`).
`verify` is unaffected, since it starts from an arbitrary state.

To fix: seed the tables in `main` before the vote blocks, and decide whether
the check should be `weight == 0` (reject voters with no weight).
