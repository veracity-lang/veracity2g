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


plt.yscale('log')

plt.xlabel('log(N)')
plt.ylabel('Values')
plt.legend()
plt.grid(True)


plt.savefig('out-dswp/output_plot.png')

