#!/usr/bin/env python3

# Invoke with: python3 ./speedup_dswp.py out-dswp-results-dir
# The directory will be created if it doesn't exist,
#   and 3 CSV files will be generated inside the directory

from posixpath import join
from pathlib import Path
import subprocess
import sys, os
from typing import Tuple, List, Callable
import functools
import re
import tempfile
import shutil

Benchmark = Tuple[str, Callable[[int],List[str]]]
Data = Tuple[float, float]
Result = Tuple[Benchmark, Data]
Row = Tuple[int, List[float]]

os.chdir(os.path.dirname(sys.argv[0]))

vcy_exe = '../src/vcy.exe'

dir = ''
num_trials = 0

class VcyError(Exception):
    def __init__(self, msg) -> None:
        super().__init__(msg)
        self.msg = msg

n_values = [
    1e1, 2e1, 5e1,
    1e2, 2e2, 5e2,
    1e3, 2e3, 5e3,
    1e4, 2e4, 5e4,
    1e5, 2e5, 5e5,
    1e6, 2e6, 5e6,
    1e7, 2e7, 5e7,
    # 1e8
]

timeout = 5

def mean(values):
    return sum(values) / len(values)

def geo_mean(values):
    return functools.reduce(lambda x,y: x * y, values, 1) ** (1 / len(values))

def prep_commset(n):
    with open("a.txt", "w") as f:
        f.write("A"*(n))
    with open("b.txt", "w") as f:
        f.write("B"*(n))
    with open("c.txt", "w") as f:
        f.write("C"*(n))
    with open("d.txt", "w") as f:
        f.write("D"*(n))
    return [os.path.join(os.path.dirname(sys.argv[0]), "a.txt"), os.path.join(os.path.dirname(sys.argv[0]), "b.txt"), os.path.join(os.path.dirname(sys.argv[0]), "c.txt"), os.path.join(os.path.dirname(sys.argv[0]), "d.txt")]

def prep_simpleio(n):
    with open("a.txt", "w") as f:
        f.write("A")
    with open("b.txt", "w") as f:
        f.write("B"*(n))
    with open("c.txt", "w") as f:
        f.write("C"*(n))
    with open("d.txt", "w") as f:
        f.write("D"*(n))
    return [os.path.join(os.path.dirname(sys.argv[0]), "a.txt"), os.path.join(os.path.dirname(sys.argv[0]), "b.txt"), os.path.join(os.path.dirname(sys.argv[0]), "c.txt"), os.path.join(os.path.dirname(sys.argv[0]), "d.txt")]


def prep_potrace(n):
    result = [str(n)]
    result.extend(prep_simpleio(n))
    return result

# Program name, followed by any command line arguments
benchmarks : List[Benchmark] = [
    ("benchmarks/global_commutativity/sollve_dotprod.vcy", lambda n : [str(n)]),
    ("benchmarks/global_commutativity/simple-vector.vcy", lambda n : [str(n)]),
    ("benchmarks/global_commutativity/2d-array.vcy", lambda n : [str(n)]),
    ("benchmarks/global_commutativity/vote-run.vcy", lambda n : [str(n)]),
    ("benchmarks/global_commutativity/commset.vcy", prep_commset),
    ("benchmarks/global_commutativity/multi-blocks.vcy", lambda n : [str(n)]),
    ("benchmarks/global_commutativity/simple-io.vcy", prep_simpleio),
    ("benchmarks/global_commutativity/motivation.vcy", lambda n : [str(n * 100), "10"]),
    ("benchmarks/global_commutativity/blockchain-erc20-1dArray.vcy", lambda n : [str(n), str(1), str(2)]),
    ("benchmarks/global_commutativity/banking.vcy", lambda n : [str(n), str(1), "1000"]),
    ("benchmarks/global_commutativity/array.vcy", lambda n : [str(n)]),
    ("benchmarks/global_commutativity/commset-potrace.vcy", prep_potrace)
]
    
def replace_commutativity_predicate_in_memory(code: str) -> str:
    def find_matching_brace(s, start):
        count = 1
        i = start
        while i < len(s) and count > 0:
            if s[i] == '{':
                count += 1
            elif s[i] == '}':
                count -= 1
            i += 1
        return i if count == 0 else -1

    pattern_commutativity = re.compile(
        r'commutativity\s*\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}\s*',
        re.DOTALL
    )
    code_without_commutativity = re.sub(pattern_commutativity, '', code)

    pattern_label = re.compile(r'(\w+(?:\([^)]*\))?)\s*:\s*\{')

    result = ""
    pos = 0
    while True:
        match = pattern_label.search(code_without_commutativity, pos)
        if not match:
            result += code_without_commutativity[pos:]
            break

        result += code_without_commutativity[pos:match.start()]

        open_brace_pos = match.end() - 1
        close_brace_pos = find_matching_brace(code_without_commutativity, open_brace_pos + 1)

        if close_brace_pos == -1:
            result += code_without_commutativity[match.start():]
            break

        content = code_without_commutativity[open_brace_pos:close_brace_pos + 1]
        result += content

        pos = close_brace_pos + 1
        
    return result
    

def run_benchmark(index: int, n: int, b: Benchmark) -> Result:
    prog, fargs = b
    args = fargs(n)

    # Read the original file content
    original_file_path = '../' + prog
    with open(original_file_path, 'r') as file:
        original_code = file.read()

    # Replace commutativity predicate in memory
    modified_code = replace_commutativity_predicate_in_memory(original_code)

    # Create a temporary directory and file for the modified code
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_file_path = os.path.join(temp_dir, os.path.basename(prog))
        with open(temp_file_path, 'w') as temp_file:
            temp_file.write(modified_code)

        # Run the benchmark using the temporary file
        command_seq = [vcy_exe, 'interp', '--time', '--timeout', str(timeout), temp_file_path] + args
        command_par = [vcy_exe, 'interp', '--time', '--dswp', '--timeout', str(timeout), temp_file_path] + args

        def f(command: List[str], floatize: bool):
            popen = subprocess.Popen(
                command, universal_newlines=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env={'LD_LIBRARY_PATH': '../veracity/src'}
            )
            out, err = popen.communicate()
            if err:
                raise VcyError(err)
            try:
                return float(out) if floatize else out
            except TypeError:
                raise TypeError(f'Output {out} could not be parsed into a float')

        sys.stdout.write(f'{(index+1):#2d}/{len(benchmarks) * len(n_values)} Executing {prog} in sequence... ')
        sys.stdout.flush()
        seq_time = f(command_seq, True)

        sys.stdout.write(f'Done. Now in DSWP mode... ')
        sys.stdout.flush()
        par_time = f(command_par, True)

        sys.stdout.write(f'Done.\n')
        sys.stdout.flush()
        return b, (float(seq_time), float(par_time))
    
def line_of_row(r : Row) -> str:
    n, l = r
    return f'{n}\t' + '\t'.join(f'{v:#.6f}' if v != None else '' for v in l)

def mk_table_start():
    return 'N\t' + '\t'.join(Path(s).stem for (s,_) in benchmarks)

def build_table(rs : List[Row]) -> str:
    rows = "\n".join(map(line_of_row, rs))
    return mk_table_start() + '\n' + rows

def build_file():
    results_ratio : List[Row] = []
    results_seq : List[Row]   = []
    results_par : List[Row]   = []
    for i, n in enumerate(map(int, n_values)):
        row_ratio = []
        row_seq = []
        row_par = []
        for j, b in enumerate(benchmarks):
            try:
                test_seq = []
                test_par = []
                test_ratio = []
                for _ in range(num_trials):
                    _, (seq, par) = run_benchmark(j + i * len(benchmarks), n, b)
                    test_seq.append(seq)
                    test_par.append(par)
                    test_ratio.append(seq / par)
                row_seq.append(mean(test_seq))
                row_par.append(mean(test_par))
                row_ratio.append(geo_mean(test_ratio))
            except VcyError as err:
                sys.stdout.write(f'\nFailure: {err.msg}\n')
                row_seq.append(None)
                row_par.append(None)
                row_ratio.append(None)
        results_seq.append((n, row_seq))
        results_par.append((n, row_par))
        results_ratio.append((n, row_ratio))

    os.makedirs(dir, exist_ok=True)
    with open(f'{dir}/ratio.csv', 'w') as file:
        file.write(build_table(results_ratio))
    with open(f'{dir}/seq.csv', 'w') as file:
        file.write(build_table(results_seq))
    with open(f'{dir}/par.csv', 'w') as file:
        file.write(build_table(results_par))

if __name__ == '__main__':
    try:
        dir = sys.argv[1]
        if '--test' in sys.argv: n_values = [1e6]
        num_trials = int(sys.argv[2])
        if len(sys.argv) > 3 and sys.argv[3] != '--test':
            benchmarks = [(sys.argv[3], lambda n: [str(n)] + sys.argv[4:])]
        build_file()
    except:
        print(f'Usage: {sys.argv[0]} <output-dir> <num-trials> [program] [--test]')
