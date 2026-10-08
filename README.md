# Veracity2G

Veracity2G (V2G) parallelizes sequential programs by exploiting the
commutativity of **named commutative blocks (NCBs)**.

An NCB gives a name to a region of code, such as a loop body or a block
in `main`. A `commutativity { }` prelude specifies the conditions under
which instances of these regions commute. V2G can then verify these
conditions, transform the program into parallel tasks, synthesize locks,
and execute the result on a multicore runtime.

## Quick Start

The provided artifact VM already contains the required dependencies and
configuration. From the repository root, run:

```bash
make
```

This builds the `vcy` executable in the repository root.

For VM setup and environment details, see the **VM README** included with
the artifact.

The following example uses:

```text
benchmarks/ncb/motivation.vcy
```

The benchmark contains two named blocks, `f1` and `f2`, inside a loop.
Its commutativity condition is:

```text
commutativity {
    {f1(i_1, x, arr)}, {f2(i_2, arr)}:
        ((i_1 != i_2) || (i_1 == i_2 && arr[i_1] > 0))
}
```

The condition states that an `f1` instance and an `f2` instance commute
when they operate on different indices, or when they operate on the same
index and `arr[i_1] > 0`.

### Quick workflow

After building, the main workflow can be run with:

```bash
# 1. Inspect the transformed program
./vcy parse --synthesize-locks --pretty \
    benchmarks/ncb/motivation.vcy

# 2. Verify the commutativity condition
./vcy verify benchmarks/ncb/motivation.vcy --prover cvc5

# 3. Run sequentially
./vcy interp benchmarks/ncb/motivation.vcy 100 10

# 4. Run in parallel with synthesized locks
./vcy interp --dswp benchmarks/ncb/motivation.vcy 100 10

# 5. Optionally infer the commutativity condition (You need to remove the condition first and replace it with _)
./vcy infer benchmarks/ncb/motivation.vcy --prover cvc5 --poke2 --timeout=30
```

The two arguments `100 10` are passed to `main` as `argv`:

* `100` is the `scalingfactor`.
* `10` is the size of the output array.

The sequential and parallel executions should produce the same return
value.

The four main commands are described in more detail below.

### 1. Parse

Inspect the transformed program without executing it:

```bash
./vcy parse \
    --synthesize-locks \
    --pretty \
    benchmarks/ncb/motivation.vcy
```

This is useful for inspecting the locks synthesized for shared state and
understanding the program transformation.

### 2. Verify

Check that the commutativity condition is sound:

```bash
./vcy verify benchmarks/ncb/motivation.vcy --prover cvc5
```

The result reports whether the condition is correct, incorrect, or could
not be verified.

An unsound condition can allow non-commuting blocks to execute
concurrently, so conditions should be verified before parallel
execution.

### 3. Interpret

Run the benchmark sequentially:

```bash
./vcy interp benchmarks/ncb/motivation.vcy 100 10
```

Then run it using the task-parallel execution model:

```bash
./vcy interp \
    --dswp \
    --synthesize-locks \
    benchmarks/ncb/motivation.vcy 100 10
```

With `--dswp`, V2G constructs parallel tasks and executes them using
the commutativity-aware scheduler. `--synthesize-locks` inserts
fine-grained locks where necessary.

The program prints:

```text
Return: N
```

where `N` is the return value of `main`.

### 4. Infer

V2G can also infer a commutativity condition. Replace the explicit
condition in `motivation.vcy` with `_`:

```text
commutativity {
    {f1(i_1, x, arr)}, {f2(i_2, arr)}: _
}
```

Then run:

```bash
./vcy infer benchmarks/ncb/motivation.vcy --prover cvc5
```

Inference is experimental and may time out on larger blocks. Writing a
condition explicitly and verifying it is the recommended workflow.

---

# Detailed Documentation

## Named Commutative Blocks

A named commutative block gives a name to a region of code and can
optionally specify input variables:

```text
label(x, y): { ... }

label: { ... }
```

The parameters are not function arguments. They identify local
variables whose values at block entry can be referenced by the
commutativity condition.

When the program is executed sequentially, the labels have no effect.

### The `commutativity` prelude

At the top of a program, NCB pairs and their conditions are specified
in a `commutativity` block:

```text
commutativity {
    {f(i_1, arr)}, {g(i_2, arr)} :
        (i_1 != i_2 || (i_1 == i_2 && arr[i_1] > 0));

    {f(i_1, arr)}, {f(i_2, arr)} :
        (i_1 != i_2);

    {g(i_1, arr)}, {g(i_2, arr)} :
        (i_1 != i_2)
}
```

Important rules:

* Entries are separated by `;`.
* Parameters are matched to block parameters by position.
* Names such as `i_1` and `i_2` are aliases used in the condition.
* Different aliases should be used when comparing two instances of the
  same NCB.
* The condition is a pure boolean expression over NCB inputs and global
  state.
* Conditions may use constants, arithmetic, comparisons, boolean
  operators, array reads, struct field reads, and read-only hashtable
  operations.
* Use `true` when two blocks always commute.
* Use `_` to request condition inference.
* Pairs that are not listed are assumed not to commute.

At runtime, the scheduler evaluates the condition using the shared
global state and the input values of the two jobs.

## Commands

The general command-line form is:

```bash
./vcy <command> [flags] <program.vcy> [program args]
```

### `verify`

Verify explicit commutativity conditions:

```bash
./vcy verify benchmarks/ncb/banking.vcy --prover cvc5
```

Useful options include:

| Flag         | Description                            |
| ------------ | -------------------------------------- |
| `-q`         | Print only `correct` / `incorrect`     |
| `--cond`     | Print each condition                   |
| `--html`     | Generate an HTML verification report   |
| `--htmlopen` | Generate and open an HTML report       |
| `-ae`        | Required when the program uses `havoc` |

### `infer`

Infer conditions for NCBs whose condition is `_`:

```bash
./vcy infer benchmarks/ncb/vote-infer.vcy --prover cvc5
```

Inference can be limited with:

```bash
./vcy infer program.vcy --prover cvc5 --timeout N
```

### `parse`

Parse and inspect a program:

```bash
./vcy parse --pretty program.vcy
```

To inspect synthesized locks:

```bash
./vcy parse --synthesize-locks --pretty program.vcy
```

### `interp`

Run a program sequentially:

```bash
./vcy interp program.vcy ARGS
```

Run it using task parallelism:

```bash
./vcy interp --dswp program.vcy ARGS
```

Run it with synthesized locks:

```bash
./vcy interp --dswp --synthesize-locks program.vcy ARGS
```

Important options:

| Flag                    | Description                                    |
| ----------------------- | ---------------------------------------------- |
| `--dswp`                | Enable task-parallel execution                 |
| `--threads N`           | Worker pool size; default is 8                 |
| `--synthesize-locks`    | Insert fine-grained locks                      |
| `--emit-tasks`          | Print generated task bodies and exit           |
| `--html` / `--htmlopen` | Generate a PDG, SCC DAG, and task-graph report |
| `--time`                | Print execution time                           |
| `--force-sequential`    | Disable parallel execution                     |
| `--out-dir DIR`         | Specify the output directory                   |

To inspect generated tasks without executing them:

```bash
./vcy interp --dswp --synthesize-locks --emit-tasks program.vcy ARGS
```

## NCB Benchmarks

NCB examples are located in `benchmarks/ncb/`.

| Benchmark                      | Illustrates                                               | Example arguments          |
| ------------------------------ | --------------------------------------------------------- | -------------------------- |
| `ncb_dot_product.vcy`          | Self-commuting loop body and synthesized reduction lock   | `4`                        |
| `ncb_histogram.vcy`            | `(true)` condition and shared bucket update               | `8`                        |
| `ncb_max_reduce.vcy`           | Max-reduction pattern                                     | `10`                       |
| `motivation.vcy`               | Paper running example with conditional commutativity      | `100 10`                   |
| `banking.vcy`                  | Deposits, withdrawals, and transfers on distinct accounts | `1 100 1000`               |
| `blockchain-erc20-1dArray.vcy` | ERC20 transfers                                           | `1 1 2`                    |
| `vote-run.vcy`                 | Smart-contract voting                                     | `1`                        |
| `multi-blocks.vcy`             | Multiple NCBs and hashtable conditions                    | `1`                        |
| `simple-io.vcy`                | Commutativity involving file I/O                          | Four file paths            |
| `commset.vcy`                  | Benchmark adapted from CommSet                            | See `scripts/run_tests.sh` |
| `commset-kmeans.vcy`           | Benchmark adapted from CommSet                            | See `scripts/run_tests.sh` |
| `commset-potrace.vcy`          | Benchmark adapted from CommSet                            | See `scripts/run_tests.sh` |
| `sollve_dotprod.vcy`           | Benchmark adapted from PS-DSWP / SOLLVE                   | `1`                        |
| `simple-vector.vcy`            | Benchmark adapted from PS-DSWP / SOLLVE                   | `1`                        |
| `2d-array.vcy`                 | Benchmark adapted from PS-DSWP / SOLLVE                   | `1`                        |

## Building

When using the provided artifact VM, no dependency installation or
environment configuration is required. Run:

```bash
make
```

For VM installation and environment setup, see the VM README.

When building outside the provided VM, V2G requires OCaml 5, OPAM,
Dune, `domainslib`, and the other OCaml dependencies used by the
project. V2G also uses Servois2 for SMT queries and requires at least
one supported SMT solver.

CVC5 is the recommended solver. Z3 and Yices are also supported:

```bash
./vcy verify program.vcy --prover z3
./vcy verify program.vcy --prover yices
```

## Testing

Run the complete test suite:

```bash
make test
```

Run the NCB benchmark and lock-synthesis tests:

```bash
bash scripts/run_tests.sh
```

## Original Veracity `commute` Blocks

V2G also supports the original Veracity constructs, which reason about
sequentially composed blocks:

```text
commute _ {
    { block_A }
    { block_B }
}

commute (x > 0) {
    { block_A }
    { block_B }
}
```

Mover variants include:

```text
commute_left
commute_right
commute_left_ctx <ctx>
commute_right_ctx <ctx>
```

Related commands are:

| Command      | Description                                        |
| ------------ | -------------------------------------------------- |
| `infer`      | Infer conditions for `commute _` blocks            |
| `verify`     | Verify explicit conditions                         |
| `invariants` | Check that annotated loop invariants are inductive |
| `assertions` | Check `assert()` statements                        |
| `translate`  | Translate to C                                     |

Examples:

```bash
./vcy infer benchmarks/prepost/pre.vcy --prover cvc5
./vcy verify benchmarks/verify/even-odd.vcy --prover cvc5
./vcy verify benchmarks/loops/scan.vcy --prover cvc5
./vcy invariants benchmarks/invariants/inc.vcy --prover cvc5
./vcy assertions benchmarks/vcgen/assert.vcy --prover cvc5
```

### Loop invariants

When a `commute` block contains a loop, annotate it with an invariant:

```text
while (i < n) invariant i >= 0 && i <= n {
    i = i + 1;
}
```

The invariant is used by the SMT encoding to represent the loop's net
effect. Check that an invariant is inductive with:

```bash
./vcy invariants benchmarks/invariants/inc.vcy --prover cvc5
```

### Quantified conditions

A `commute` condition may use `forall` or `exists`:

```text
commute (forall k : int . a[k] == 0) {
    ...
}
```

Quantified conditions are supported by `verify`. They are not generated
by inference and cannot be executed by `interp`.

## Reading Verification Counterexamples

When `verify` rejects a condition and `--html` is provided, Veracity
writes an `expr_table.html` file into the corresponding report
directory.

The table maps program expressions to their SMT values before and after
each block execution. A counterexample is a state in which the two
execution orders produce different final states.

## Repository Layout

| Path                                           | Contents                                             |
| ---------------------------------------------- | ---------------------------------------------------- |
| `benchmarks/ncb/`                              | NCB programs                                         |
| `benchmarks/lock_synth/`                       | Lock-synthesis tests                                 |
| `benchmarks/inferred/`, `verify/`, `loops/`, … | Original Veracity benchmarks                         |
| `scripts/`                                     | Test and task-generation scripts                     |
| `reports/`                                     | Speedup and inference/verification scripts and plots |
| `src/vcy/`                                     | Lexer, parser, interpreter, and CLI                  |
| `src/analysis/`                                | Servois2 translation, PDG, and task construction     |
| `src/parallel/`                                | Multicore and single-core runtime backends           |
| `src/api/`                                     | Programmatic OCaml API                               |
| `src/test/`                                    | OUnit2 test suites                                   |

## OCaml API

The functionality is also available programmatically through
`Vcy.Veracity`.

See [API.md](API.md).
