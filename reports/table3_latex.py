#!/usr/bin/env python3
# Build the LaTeX for Table 3 from the job statistics run_experiments.sh writes.
#
# Usage: ./table3_latex.py [stats-file] [csv-dir] [out-file]
#   stats-file  default table3-jobstats.txt
#   csv-dir     output directory of speedup_dswp.py, default out-ncbpar
#   out-file    default table3.tex
#
# Tasks, Jobs and Avg Job Exec come from the stats file. Seq, Par and Obsrv.
# come from seq.csv, par.csv and ratio.csv in csv-dir, at the N in TABLE_N
# (or the largest N measured, if that one was not). Nodes, Depth, Locks and
# Thry. are not printed by vcy, so they are kept in STATIC below.

import os
import re
import sys

# name: (PDG_C nodes, PDG_C depth, locks, theoretical speedup)
STATIC = {
    'motivation':   (20, 3, 1, 8),
    'simple-io':    (15, 2, 0, 2),
    'multi-blocks': (25, 2, 3, 3),
    'vote':         (7,  2, 1, 4),
    'erc20':        (44, 4, 5, 9),
    'banking':      (57, 5, 0, 9),
}

ORDER = ['motivation', 'simple-io', 'multi-blocks', 'vote', 'erc20', 'banking']

# The N each row is reported at, matching the job_stats runs in run_experiments.sh
TABLE_N = {
    'motivation':   50000000,
    'simple-io':    1000000,
    'multi-blocks': 1000000,
    'vote':         50000000,
    'erc20':        50000000,
    'banking':      50000000,
}

FIELDS = {
    'tasks': re.compile(r'^Tasks: (\d+)'),
    'jobs':  re.compile(r'^Jobs: (\d+)'),
    'pure':  re.compile(r'^Avg job exec \(pure\): ([\d.]+)'),
    'deps':  re.compile(r'^Avg job exec \(\+deps\): ([\d.]+)'),
}

HEADER = r"""\begin{table}[t]
	\renewcommand{\arraystretch}{0.7}
		\setlength{\tabcolsep}{{\benchtabletabcolsep}}
		\centering
		\small
		\setlength\extrarowheight{2mm}
		\begin{tabular}{l|cc|ccc|rr|rr|rr}
		\toprule
		 & \multicolumn{2}{c|}{{\bf PDG$_C$ stats}} & & & & \multicolumn{2}{c|}{\bf Avg Job Exec(s)} & \multicolumn{2}{c|}{\bf Total Exec(s)} & \multicolumn{2}{c}{\bf Speedup} \\
		 {\bf Name} & {\bf Nodes} & {\bf Depth} & {\bf Tasks} & {\bf Locks} & {\bf Jobs} & {\bf Pure} & {\bf +Deps} & {\bf Seq} & {\bf Par} & {\bf Thry.} & {\bf Obsrv.} \\
		\midrule
"""

FOOTER = r"""		\bottomrule
		\end{tabular}
	\caption{\label{table:execution}
	Runtime execution statistics and performance for the new benchmarks. See inline prose for column descriptions.
    ``Speedup'' compares theoretical and observed speedups over sequential execution.
	}
\end{table}
"""

def parse(path):
    stats, cur = {}, None
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith('== '):
                cur = stats.setdefault(line[3:].strip(), {})
                continue
            if cur is None: continue
            for key, rx in FIELDS.items():
                m = rx.match(line)
                if m: cur[key] = float(m.group(1))
    return stats

# {benchmark: {N: value}} from one of speedup_dswp.py's tab-separated tables
def read_csv(path):
    table = {}
    if not os.path.exists(path): return table
    with open(path) as f:
        names = f.readline().rstrip('\n').split('\t')[1:]
        for line in f:
            cells = line.rstrip('\n').split('\t')
            for name, v in zip(names, cells[1:]):
                if v: table.setdefault(name, {})[int(cells[0])] = float(v)
    return table

def at_n(name, csvs):
    ns = set.intersection(*(set(t.get(name, {})) for t in csvs.values()))
    if not ns: return {}
    n = TABLE_N.get(name)
    if n not in ns:
        print(f'warning: {name} has no CSV row at N = {n}, using N = {max(ns)}',
              file=sys.stderr)
        n = max(ns)
    return {k: t[name][n] for k, t in csvs.items()}

def num(s, key, fmt):
    return fmt.format(s[key]) if key in s else '--'

def row(name, s):
    nodes, depth, locks, thry = STATIC.get(name, ('--',) * 4)
    obsrv = f"{s['ratio']:.2f}$\\times$" if 'ratio' in s else '--'
    thry = f'{thry}$\\times$' if thry != '--' else thry
    cells = [f'\\texttt{{{name}}}', nodes, depth,
             num(s, 'tasks', '{:.0f}'), locks, num(s, 'jobs', '{:.0f}'),
             num(s, 'pure', '{:.2f}'), num(s, 'deps', '{:.2f}'),
             num(s, 'seq', '{:.2f}'), num(s, 'par', '{:.2f}'),
             thry, obsrv]
    return '\t\t' + ' & '.join(map(str, cells)) + ' \\\\\n'

if __name__ == '__main__':
    src = sys.argv[1] if len(sys.argv) > 1 else 'table3-jobstats.txt'
    csv_dir = sys.argv[2] if len(sys.argv) > 2 else 'out-ncbpar'
    dst = sys.argv[3] if len(sys.argv) > 3 else 'table3.tex'
    stats = parse(src)
    csvs = {k: read_csv(f'{csv_dir}/{k}.csv') for k in ('seq', 'par', 'ratio')}
    for name, s in stats.items():
        s.update(at_n(name, csvs))
    names = [n for n in ORDER if n in stats] + [n for n in stats if n not in ORDER]
    with open(dst, 'w') as f:
        f.write(HEADER + ''.join(row(n, stats[n]) for n in names) + FOOTER)
    print(f'Table 3 LaTeX written to reports/{dst}')
