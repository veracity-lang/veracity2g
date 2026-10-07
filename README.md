# Veracity2G

  Veracity2G (V2G) parallelizes sequential programs by exploiting the
  commutativity of **named commutative blocks** (NCBs). You give a name to any
  region of code (a loop body, a branch, a block in `main`), and in a
  `commutativity { }` prelude you state the conditions under which instances of
  those regions commute. V2G then:

  - **verifies** that each stated commutativity condition is sound (via the
    [Servois2](https://github.com/jdublu10/servois2) SMT back-end),
  - builds a *commutativity-aware* program dependence graph and splits the
    program into asynchronous **tasks**,
  - **synthesizes locks** so that concurrently running jobs are pairwise atomic,
    and
  - **executes** the result on a multicore runtime scheduler that checks the
    commutativity conditions *at runtime* to decide whether two jobs may run in
    parallel even though they touch the same data.

  Unlike the original Veracity, the commuting regions do not need to be adjacent:
  an NCB at the top of `main` can be declared to commute with every iteration of
  a later loop, and a loop body can be declared to commute with *itself* across
  iterations.

  ## A first example

  ```
  commutativity { {dot(i_1)}, {dot(i_2)} : (i_1 != i_2) }

  int[] a  = new int[16];
  int[] b  = new int[16];
  int result = 0;

  int main(int argc, string[] argv) {
      int n = int_of_string(argv[1]);
      int i = 0;
      while (i < n) { a[i] = i + 1; b[i] = 1; i = i + 1; }
      i = 0;
      while (i < n) {
          dot(i): {
              busy_wait(10);
              int contrib = a[i] * b[i];
              result = result + contrib;
          }
          i = i + 1;
      }
      return result;
  }
  ```

  The loop body is the NCB `dot(i)`. The prelude says that two instances of
  `dot` commute whenever they were entered with different values of `i`, i.e.
  for different iterations. (`benchmarks/ncb/ncb_dot_product.vcy`)

  ```bash
  ./vcy verify   benchmarks/ncb/ncb_dot_product.vcy            # check the condition
  ./vcy interp   benchmarks/ncb/ncb_dot_product.vcy 4          # sequential run
  ./vcy interp --dswp --synthesize-locks \
                 benchmarks/ncb/ncb_dot_product.vcy 4          # parallel run
  ```

  Under `--dswp` the iterations become concurrent jobs; lock synthesis wraps only
  the shared update `result = result + contrib` in a critical section, so the
  reads and `busy_wait` proceed in parallel.

  ## Writing NCB programs

  ### Naming a block

  Any block can be given a label and a list of *input variables*:

  ```
  label(x, y): { ... }
  label: { ... }                // no parameters
  ```

  The parameters are not function arguments. They name the local variables,
  in scope at that point, whose values at block entry the commutativity
  condition may refer to. Running the program sequentially simply ignores the
  label.

  ### The `commutativity` prelude

  At the top of the program, list pairs of NCBs together with a condition:

  ```
  commutativity {
      {f(i_1, arr)}, {g(i_2, arr)} : (i_1 != i_2 || (i_1 == i_2 && arr[i_1] > 0));
      {f(i_1, arr)}, {f(i_2, arr)} : (i_1 != i_2);
      {g(i_1, arr)}, {g(i_2, arr)} : (i_1 != i_2)
  }
  ```

  - Entries are separated by `;`.
  - Each side `{name(a, b, ...)}` refers to an NCB by label. Parameters are
    matched to the block's parameters **by position**, and the names you write
    here are *aliases* used in the condition. Write `i_1` and `i_2` so the two
    instances can be told apart, which matters most when an NCB is paired with
    itself (*self-commutativity*, e.g. different iterations of the same loop
    body).
  - The condition is a pure boolean expression over the aliased NCB inputs and
    the global state: constants, arithmetic, comparisons, `&&`/`||`/`!`, array
    reads, struct field reads and read-only hashtable operations such as
    `ht_size(tbl)`. Use `(true)` if two blocks always commute.
  - Write `_` instead of a condition to ask V2G to *infer* one (see below).
  - Pairs that are not listed are assumed **not** to commute; ordinary data and
    control dependences then apply.

  At runtime the scheduler evaluates the condition over the shared global state
  plus the two jobs' own input values, and runs the two jobs in parallel only
  when it holds.

  ## Workflow

  ```
  ./vcy <command> [flags] <program.vcy> [program args]
  ```

  ### 1. Verify the commutativity conditions

  ```bash
  ./vcy verify benchmarks/ncb/banking.vcy --prover cvc5
  ```

  Each prelude entry is translated into a Servois2 ADT whose state is split into
  globals and per-block locals, and checked. Each entry gets one of
  `verified as correct`, `verified as incorrect`, or `unable to verify`. An
  unsound condition can let non-commuting blocks run concurrently, so verify
  before you run in parallel.

  Useful flags: `-q` (print only `correct`/`incorrect`), `--cond` (echo each
  condition), `--html` / `--htmlopen` (HTML report with counterexamples, see
  [Reading a counterexample](#reading-a-counterexample)), `-ae` (required if the
  program uses `havoc`).

  ### 2. (Optional) Infer conditions

  Write `_` as the condition and run:

  ```bash
  ./vcy infer benchmarks/ncb/vote-infer.vcy --prover cvc5
  ```

  Inference of NCB conditions is experimental; on larger blocks it frequently
  times out (use `--timeout N`), and writing a condition and then verifying it
  is the main supported route.

  ### 3. Run

  | Command | Effect |
  |---------|--------|
  | `./vcy interp prog.vcy ARGS` | Sequential reference run (labels ignored) |
  | `./vcy interp --dswp prog.vcy ARGS` | Parallel run: PDG → tasks → commutativity-aware scheduler |
  | `./vcy interp --dswp --synthesize-locks prog.vcy ARGS` | Parallel run with synthesized locks for pairwise atomicity (the configuration used in
  the paper's evaluation) |

  `main` receives `ARGS` as `argv`; the program prints `Return: N` with
  `main`'s return value.

  Interp flags relevant to NCBs:

  | Flag | Description |
  |------|-------------|
  | `--dswp` | Enable the task-parallel execution model |
  | `--threads N` | Worker pool size for `--dswp` (default 8) |
  | `--synthesize-locks` | Insert fine-grained `mutex_lock`/`mutex_unlock` (post-decomposition when combined with `--dswp`) |
  | `--emit-tasks` | With `--dswp`: print the generated task bodies and exit |
  | `--html` / `--htmlopen` | With `--dswp`: HTML report with the PDG, SCC DAG and task graph |
  | `--time` | Print execution time instead of `main`'s return value |
  | `--force-sequential` | Disable all parallel execution |
  | `--out-dir DIR` | Where to write output (default `./veracity_output/run_NNNN/`) |

  To inspect the transformation without running:

  ```bash
  ./vcy parse --synthesize-locks --pretty prog.vcy          # source with synthesized locks
  ./vcy interp --dswp --synthesize-locks --emit-tasks prog.vcy ARGS
  ```

  ## Examples

  NCB examples live in `benchmarks/ncb/`. These are the ones
  exercised by `scripts/run_tests.sh`:

  | Benchmark | Illustrates | Example args |
  |-----------|-------------|--------------|
  | `ncb_dot_product.vcy` | Self-commuting loop body, one synthesized lock around the reduction | `4` |
  | `ncb_histogram.vcy` | `(true)` condition, shared bucket update guarded by a lock | `8` |
  | `ncb_max_reduce.vcy` | Max-reduction pattern | `10` |
  | `motivation.vcy` | The paper's running example: `f`/`g` commute when `i != j` or `arr[i] > 0` | `100 10` |
  | `banking.vcy` | Deposits, withdrawals and transfers commuting on distinct accounts | `1 100 1000` |
  | `blockchain-erc20-1dArray.vcy` | ERC20 transfers, commuting when balances suffice | `1 1 2` |
  | `vote-run.vcy` | Smart-contract voting | `1` |
  | `multi-blocks.vcy` | Several NCBs and hashtable conditions | `1` |
  | `simple-io.vcy` | Commutativity over file I/O | four file paths |
  | `commset.vcy`, `commset-kmeans.vcy`, `commset-potrace.vcy` | Benchmarks adapted from CommSet | see `scripts/run_tests.sh` |
  | `sollve_dotprod.vcy`, `simple-vector.vcy`, `2d-array.vcy` | Benchmarks adapted from PS-DSWP / SOLLVE | `1` |

  Typical session:

  ```bash
  ./vcy verify benchmarks/ncb/motivation.vcy
  ./vcy interp --dswp --synthesize-locks benchmarks/ncb/motivation.vcy 100 10
  ```

  ## Building

  ```
  add-apt-repository ppa:avsm/ppa
  apt update
  apt install opam
  apt install cvc5
  apt install graphviz # optional, for PDG output

  opam init
  eval $(opam env)

  opam update
  opam switch create 5.2.0
  eval $(opam env)

  opam install dune ounit2 menhir zarith yaml domainslib
  eval $(opam env)

  git submodule update --init --recursive
  make
  ```

  `make` builds the OCaml sources with dune and installs the `vcy` executable in
  the repository root; `make clean` removes build artifacts. OCaml 5 with
  `domainslib` is needed for the multicore runtime; without it V2G falls back to
  a thread-based implementation.

  Veracity uses [Servois2](https://github.com/jdublu10/servois2) (a submodule)
  for SMT queries and needs at least one solver. **CVC5 is recommended**
  (`brew install cvc5` / `apt install cvc5`); Z3 and Yices are also supported via
  `--prover z3` / `--prover yices`.

  ## Testing

  ```
  make test                    # benchmark suites + OUnit2 unit tests
  bash scripts/run_tests.sh    # NCB benchmarks and lock-synthesis checks
  ```

  ## Repository layout

  | Path | Contents |
  |------|----------|
  | `benchmarks/ncb/` | NCB programs (`test/`: small feature/regression programs; `CLEANUP.md`: one open deletion candidate) |
  | `benchmarks/lock_synth/` | Lock-synthesis tests (NCB and non-NCB) |
  | `benchmarks/inferred/`, `verify/`, `loops/`, … | Adjacent `commute`-block benchmarks from the original Veracity |
  | `scripts/` | `run_tests.sh` and `emit_tasks.sh` |
  | `reports/` | Speedup and inference/verification scripts and plots |
  | `src/vcy/` | Lexer, parser, interpreter, CLI |
  | `src/analysis/` | Translation to Servois2, PDG and task construction |
  | `src/parallel/` | Multicore / single-core runtime backends |
  | `src/api/` | Programmatic OCaml API (`Vcy.Veracity`), see [API.md](API.md) |
  | `src/test/` | OUnit2 test suites |

  ---

  ## Adjacent `commute` blocks (original Veracity)

  V2G still supports the original Veracity constructs, which reason about
  two (or more) *sequentially composed* blocks:

  ```
  commute _ {          // infer the condition
      { block_A }
      { block_B }
  }

  commute (x > 0) {    // verify this condition
      { block_A }
      { block_B }
  }
  ```

  Mover variants: `commute_left`, `commute_right`, `commute_left_ctx <ctx>`,
  `commute_right_ctx <ctx>`. Related commands:

  | Command | Description |
  |---------|-------------|
  | `infer`      | Infer conditions for all `commute _` blocks (`--force` re-infers provided ones) |
  | `verify`     | Verify explicit conditions |
  | `invariants` | Check that annotated `while` loop invariants are inductive |
  | `assertions` | Check that `assert()` statements hold |
  | `translate`  | Translate to C |

  ```bash
  ./vcy infer      benchmarks/prepost/pre.vcy --prover cvc5
  ./vcy verify     benchmarks/verify/even-odd.vcy --prover cvc5
  ./vcy verify     benchmarks/loops/scan.vcy --prover cvc5
  ./vcy invariants benchmarks/invariants/inc.vcy --prover cvc5
  ./vcy assertions benchmarks/vcgen/assert.vcy --prover cvc5
  ```

  ### Loop invariants

  When a `commute` block contains a loop, annotate it with an `invariant`. The
  SMT encoding uses the invariant to represent the loop's net effect, and
  `./vcy invariants` checks that it is inductive:

  ```
  while (i < n) invariant i >= 0 && i <= n {
      i = i + 1;
  }
  ```

  ### Quantified conditions

  A `commute` condition may use `forall` / `exists`, e.g.
  `commute (forall k : int . a[k] == 0) { ... }`. The binder type defaults to
  `int` and the body extends as far right as possible. Quantified conditions
  only make sense for `verify`: inference never produces them and `interp`
  cannot execute them.

  ### Reading a counterexample

  When `verify` rejects a condition and `--html` is given, Veracity writes
  `expr_table.html` into each `commute_NNNN/` directory of the report. It
  re-keys the solver's model by the expressions written in the block, so you
  don't have to read Servois2's raw state variables:

  | Veracity expression | SMT expression | initial | after block 1 | after block 1; block 2 | after block 2 | after block 2; block 1 |
  |---|---|---|---|---|---|---|
  | `l1->value` | `(select heap_value l1)` | 0 | 1 | 1 | 0 | 1 |
  | `x` | `x` | 0 | 0 | **1** | 0 | **0** |

  A counterexample is exactly a row where the two final states differ, so those
  rows are highlighted. Under `-ae` the reversed run is existentially bound, so
  its columns are omitted. See `benchmarks/models/`.

  ## OCaml API

  Everything above is also available as a library via `Vcy.Veracity`. See
  [API.md](API.md).

  If your terminal still renders it, run ! cat /tmp/claude-1001/-workspace/01ea1976-1036-4126-9063-0187541ca036/scratchpad/README.md to print the
  file exactly as it is.