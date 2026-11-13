# Summary plots of the prior-work benchmarks for the paper's Fig. summary:
#   2d-array-plot-noLeg.png  (psdswp) and speedup-plot.png (commset-*).
#
# python3 ./speedup_plot_prior_summary.py out-dswp-prior-works-hl

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import sys
import os

if len(sys.argv) != 2:
    print("Usage: python script.py <input_output_directory>")
    sys.exit(1)

directory = sys.argv[1]
data = pd.read_csv(os.path.join(directory, 'ratio.csv'), sep=r"\s+")
log_N = np.log10(data.iloc[:, 0])

def finish(output_file):
    plt.axhline(y=1, color='black', linestyle='--', linewidth=2.5)
    plt.xticks(fontsize=19)
    plt.yticks(fontsize=19)
    plt.xlabel('Log(Computation Size)', fontsize=19)
    plt.ylabel('Par-to-Seq Speedup', fontsize=19)
    plt.grid(True, linestyle=':', alpha=0.6)
    plt.subplots_adjust(left=0.16, right=0.98, bottom=0.17, top=0.97)
    plt.savefig(output_file, dpi=300, transparent=True)
    plt.close()
    print(f"Plot saved at {output_file}")

plt.figure(figsize=(6, 4))
plt.plot(log_N, data['2d-array'], marker='o', markersize=6, linewidth=2)
finish(os.path.join(directory, '2d-array-plot-noLeg.png'))

plt.figure(figsize=(6, 4))
for column, label, marker in [('commset', 'commset-md5', 'o'),
                              ('commset-potrace', 'commset-potrace', 's'),
                              ('commset-kmeans', 'commset-kmeans', '^')]:
    plt.plot(log_N, data[column], label=label, marker=marker, markersize=6, linewidth=2)
plt.legend(loc='upper left', fontsize=14)
finish(os.path.join(directory, 'speedup-plot.png'))
