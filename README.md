# Veracity2G

Veracity2G (V2G) parallelizes sequential programs by exploiting the
commutativity of **named commutative blocks (NCBs)**.

An NCB gives a name to a region of code, such as a loop body or a block
in `main`. A `commutativity { }` prelude specifies the conditions under
which instances of these regions commute. V2G can then verify these
conditions, transform the program into parallel tasks, synthesize locks,
and execute the result on a multicore runtime.

The source code is available on GitHub:
<https://github.com/veracity-lang/veracity2g>.

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
# 1. Verify the commutativity condition
./vcy verify benchmarks/ncb/motivation.vcy --prover cvc5

# 2. Run sequentially
./vcy interp benchmarks/ncb/motivation.vcy 100 10

# 3. Run in parallel with synthesized locks
./vcy interp --dswp --synthesize-locks benchmarks/ncb/motivation.vcy 100 10

# 4. Optionally infer the commutativity condition (You need to remove the condition first and replace it with _)
./vcy infer benchmarks/ncb/motivation.vcy --prover cvc5 --poke2 --timeout=30
```

The two arguments `100 10` are passed to `main` as `argv`:

* `100` is the `scalingfactor`.
* `10` is the size of the output array.

The sequential and parallel executions should produce the same return
value.

The three main commands are described in more detail below.

### 1. Verify

Check that the commutativity condition is sound:

```bash
./vcy verify benchmarks/ncb/motivation.vcy --prover cvc5
```

The result reports whether the condition is correct, incorrect, or could
not be verified.

An unsound condition can allow non-commuting blocks to execute
concurrently, so conditions should be verified before parallel
execution.

### 2. Interpret

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

Lock synthesis operates on the parallel tasks produced by the DSWP
transformation, not on the sequential program, so `--synthesize-locks`
is always used together with `--dswp`.

To see the synchronization that V2G generates for the tasks, add
`--codegen`:

```bash
./vcy interp --dswp --synthesize-locks benchmarks/ncb/commset.vcy --codegen
```

This writes the generated C code to `/tmp/autogen_tasks.c`, where you
can inspect the semaphores (`sem_t`, `sem_init`, `sem_wait`,
`sem_post`) generated to enforce the dependencies between tasks.

### 3. Infer

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
./vcy infer benchmarks/ncb/other/vote-infer.vcy --prover cvc5
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
| `--codegen`             | Write generated C to `/tmp/autogen_tasks.c`    |
| `--html` / `--htmlopen` | Generate a PDG, SCC DAG, and task-graph report |
| `--time`                | Print execution time                           |
| `--job-stats`           | Print task/job counts and average job time     |
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
| `test/ncb_dot_product.vcy`     | Self-commuting loop body and synthesized reduction lock   | `4`                        |
| `test/ncb_histogram.vcy`       | `(true)` condition and shared bucket update               | `8`                        |
| `other/ncb_max_reduce.vcy`     | Max-reduction pattern                                     | `10`                       |
| `motivation.vcy`               | Paper running example with conditional commutativity      | `100 10`                   |
| `banking.vcy`                  | Deposits, withdrawals, and transfers on distinct accounts | `1 100 1000`               |
| `erc20.vcy`                    | ERC20 transfers                                           | `1 1 2`                    |
| `vote.vcy`                 | Smart-contract voting                                     | `1`                        |
| `multi-blocks.vcy`             | Multiple NCBs and hashtable conditions                    | `1`                        |
| `simple-io.vcy`                | Commutativity involving file I/O                          | Four file paths            |
| `commset.vcy`                  | Benchmark adapted from CommSet                            | See `scripts/run_tests.sh` |
| `commset-kmeans.vcy`           | Benchmark adapted from CommSet                            | See `scripts/run_tests.sh` |
| `commset-potrace.vcy`          | Benchmark adapted from CommSet                            | See `scripts/run_tests.sh` |
| `other/sollve_dotprod.vcy`     | Benchmark adapted from PS-DSWP / SOLLVE                   | `1`                        |
| `other/simple-vector.vcy`      | Benchmark adapted from PS-DSWP / SOLLVE                   | `1`                        |
| `other/2d-array.vcy`           | Benchmark adapted from PS-DSWP / SOLLVE                   | `1`                        |

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

## Reproducing the Paper's Results

The scripts are in `reports/`. Each one changes into its own directory and
resolves paths from there, so run them from `reports/` as `./script.py` or
`python3 ./script.py`. (`python3 script.py` without `./` fails.) Output
directories are created under `reports/`. The plotting scripts need
`pandas` and `matplotlib`, which are installed in the VM.

### Speedup measurements

Each measurement script runs every benchmark in its `benchmarks` list,
sequentially (`vcy interp --time`) and in parallel
(`vcy interp --time --dswp --synthesize-locks`), for each computation size N
in `n_values` (10 to 5·10⁷), `<trials>` times:

```bash
cd reports
python3 ./speedup_dswp.py      out-ncbpar <trials>   # NCBPar.: NCBs with their commutativity conditions
python3 ./speedup_dswp_nc.py   out-nc     <trials>   # False-Comm.: every condition replaced by false
python3 ./speedup_dswp_noNB.py out-noNB   <trials>   # No-NCB.: commutativity block and NCB labels removed
```

Each writes four tab-separated tables to its output directory, with one row
per N and one column per benchmark:

| File            | Contents                                         |
| --------------- | ------------------------------------------------ |
| `seq.csv`       | Mean sequential time (s)                         |
| `par.csv`       | Mean parallel time (s)                           |
| `ratio.csv`     | Geometric mean of the per-trial speedups         |
| `ratio_std.csv` | Standard deviation of the per-trial speedups     |

Add `--test` after `<trials>` to run only N = 10⁶, as a quick check.

**A single benchmark.** Pass the program path (relative to the repository
root), followed by any arguments after the first. The script supplies the
first argument, N, itself and sweeps it, so do not pass N:

```bash
python3 ./speedup_dswp.py out-motivation 5 benchmarks/ncb/motivation.vcy 10
# runs: vcy interp ... motivation.vcy <N> 10   for each N
```

This works for all three scripts. Note that a program given this way always
receives N itself as its first argument, while the built-in `benchmarks` list
may scale it (`motivation.vcy` receives N·100 there). To reproduce the
paper's numbers, use the built-in list.

### Fig. 6

Run the three measurement scripts above, then:

```bash
python3 ./speedup_plot_compare.py out-ncbpar out-nc out-noNB fig6 [--err]
```

This writes one `<benchmark>-comparison.png` per benchmark to `fig6/`.
`--err` adds error bars from `ratio_std.csv`.

To plot a single result directory instead, run
`python3 ./speedup_plot.py <result-dir> <out-dir>`. It reads that directory's
`ratio.csv` and writes one `<benchmark>-plot.png` per benchmark.

### Table 3

Each row uses, for that benchmark, the computation size N with the highest
speedup in `ratio.csv` from `speedup_dswp.py`:

| Benchmark      | N          |
| -------------- | ---------- |
| `motivation`   | 50,000,000 |
| `simple-io`    | 1,000,000  |
| `multi-blocks` | 10,000,000 |
| `vote`         | 50,000,000 |
| `erc20`        | 50,000,000 |
| `banking`      | 50,000,000 |

| Column                     | Source                                                                                                        |
| -------------------------- | ------------------------------------------------------------------------------------------------------------- |
| Total Exec (Seq, Par)      | `seq.csv` and `par.csv` at that N                                                                             |
| Speedup (Obsrv.)           | `ratio.csv` at that N (geometric mean of per-trial speedups)                        |
| Nodes                      | Nodes in `pdg.dot`, the PDG before transformation                                                             |
| Depth                      | Longest control-dependence chain from the entry node in `pdg.dot`                                             |
| Tasks                      | `Tasks:` from `--job-stats`: static tasks, as listed in the HTML report (init task not counted)              |
| Locks                      | Synthesized locks in the task bodies: distinct locks (distinct `mutex_lock` ids), not `mutex_lock`/`mutex_unlock` pairs |
| Jobs                       | `Jobs:` from `--job-stats`: dynamic job instances executed in the parallel run                                |
| Avg Job Exec (Pure, +Deps) | `Avg job exec (pure)` / `(+deps)` from `--job-stats`: average seconds per job for its body alone (Pure), and including waits on dependencies (+Deps) |
| Speedup (Thry.)            | Derived by hand from the thread count (default 8 (9 domains), `--threads`), the number of jobs, and dependencies that keep threads idle |


To get Tasks, Jobs and Avg Job Exec, run the parallel configuration once at
that N with `--job-stats`:

```bash
./vcy interp --dswp --synthesize-locks --time --job-stats benchmarks/ncb/<bench>.vcy <args>
```

```
Tasks: 7
Jobs: 65
Avg job exec (pure): 0.000042 s
Avg job exec (+deps): 0.000233 s
0.001065
```

The statistics go to stderr, so the `--time` value is still the last line of
stdout. Each job is timed in `run_job` (`src/vcy/interp.ml`): Pure covers
only the job's body, +Deps also covers the time it spends in `wait_deps`
before the body starts. Time a job spends queued in the worker pool before it
starts is not counted. Do not add `-d`/`--debug`: its output is printed from
inside each job and inflates both averages. Keep `--time`, which suppresses
the program's own `print` output for the same reason.

To get the PDG and tasks for a benchmark, run it once with `--html`:

```bash
./vcy interp --dswp --synthesize-locks --html benchmarks/ncb/<bench>.vcy <args>
```

This writes `pdg.dot`, `dag-scc.dot`, `tasks.dot` and an HTML report to
`veracity_output/latest/`. Add `--emit-tasks` to print the task bodies,
including synthesized locks, without running the program.

To draw the tasks as an image, use `reports/tasks_to_jpg.py`. It runs
`vcy interp --dswp --synthesize-locks --emit-tasks` on each `.vcy` file (or
every `.vcy` file in a folder) and writes one `.jpg` per program. Each task is
a card with its id, label (Doall/Sequential) and code with synthesized locks
highlighted. Arrows show dependencies with the variables they carry and their
commute conditions. Run `make` first, since it calls `./vcy`; it needs
`matplotlib`.

```bash
python3 reports/tasks_to_jpg.py benchmarks/ncb/erc20.vcy
python3 reports/tasks_to_jpg.py benchmarks/ncb/ -o reports/tasks-img --save-txt
```

Images go to `reports/tasks-img/` by default (`-o DIR` to change). `-r`
searches folders recursively, `--save-txt` also saves the raw `--emit-tasks`
output, and `--timeout N` sets the per-file timeout (default 120 s). The task
count shown for each file matches `Tasks:` from `--job-stats`, and the
highlighted locks can be used to count Locks.

### Geometric-mean speedup

The overall speedup reported in the paper is the geometric mean of the
Obsrv. column of Table 3 across its six benchmarks (4.49×).

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

### Loop support

Loops inside a block being verified are supported in one of three ways:

1. **User-provided loop invariants.** A `while` loop annotated with an
   `invariant` is encoded by its invariant, as described above.
2. **Unrolling.** A `while` loop that iterates a constant number of
   times (a counter initialized to a literal, compared against a
   literal bound, and incremented by a constant)
   is replaced by that many copies of its body. Unrolling is exact.
   Examples are in `benchmarks/loop-unroll/`.
3. **Per-iteration commutativity.** When the loop body does not depend on
   the loop counter, and each iteration commutes with the body of
   another NCB, `verify` checks a single iteration against the other
   block. By induction on swaps, the whole loop then commutes with that
   block. Examples are in `benchmarks/loop-abstract/`.

Any other loop is rejected with an error rather than being encoded
unsoundly. Commutativity of general loops is an open problem and is
left for future work.

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
