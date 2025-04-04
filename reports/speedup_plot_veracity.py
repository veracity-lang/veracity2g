import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import sys
import os

if len(sys.argv) != 2:
    print("Usage: python script.py <input_output_directory>")
    sys.exit(1)

directory = sys.argv[1]

input_csv_file = os.path.join(directory, 'ratio.csv')
output_plot_file = os.path.join(directory, 'speedup-plot.png')
output_plot_file_apx = os.path.join(directory, 'speedup-plot-apx.png')

if not os.path.exists(input_csv_file):
    print(f"Error: {input_csv_file} does not exist.")
    sys.exit(1)

try:
    data = pd.read_csv(input_csv_file, delim_whitespace=True)
except pd.errors.ParserError:
    print(f"Error: The file {input_csv_file} does not have the correct format.")
    sys.exit(1)

N = data.iloc[:, 0]
log_N = np.log10(N)
columns = data.columns[1:]

markers = ['o', 's', '^', 'D', 'v', '<', '>', 'p', '*', 'H', '+', 'x']

plt.figure(figsize=(12, 8))
for i, column in enumerate(columns):
    label = column.replace("vote-run", "vote")
    plt.plot(log_N, data[column], label=label, marker=markers[i % len(markers)])

# Add horizontal line for speedup = 1
plt.axhline(y=1, color='black', linestyle='--', label='Speedup = 1', linewidth=2.5)

plt.xticks(fontsize=17)
plt.yticks(fontsize=17)

# plt.xlabel('Log(Computation Size)', fontsize=15)
# plt.ylabel('Parallel-to-Sequential Speedup', fontsize=15)
plt.grid(True, linestyle=':', alpha=0.6)

plt.savefig(output_plot_file, dpi=300, bbox_inches='tight', transparent=True)

plt.xlabel('Log(Computation Size)', fontsize=15)
plt.ylabel('Parallel-to-Sequential Speedup', fontsize=15)
plt.legend()
plt.savefig(output_plot_file_apx, dpi=300, bbox_inches='tight', transparent=True)

print(f"Plot saved successfully at {output_plot_file}")