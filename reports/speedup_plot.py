import pandas as pd
import matplotlib.pyplot as plt
import numpy as np


input_csv_file = 'out-dswp/ratio.csv'
data = pd.read_csv(input_csv_file, delim_whitespace=True)


N = data.iloc[:, 0]
log_N = np.log10(N) 
columns = data.columns[1:]


plt.figure(figsize=(12, 8))


for column in columns:
    plt.plot(log_N, data[column], label=column, marker='o')

# plt.yscale('linear')
# plt.yscale('log')

plt.axhline(y=1, color='black', linestyle='--', label='Speedup = 1', linewidth=2.5)

plt.xlabel('computation size')
plt.ylabel('parallel-to-sequential speedup')
plt.legend()
plt.grid(True)


plt.savefig('out-dswp/output_plot.png')

