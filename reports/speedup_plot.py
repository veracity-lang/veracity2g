import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import sys
import os

def read_csv(file_path):
    try:
        return pd.read_csv(file_path, delim_whitespace=True)
    except pd.errors.ParserError:
        print(f"Error: The file {file_path} does not have the correct format.")
        sys.exit(1)

def create_plot(data, benchmark, output_dir):
    N = data.iloc[:, 0]
    log_N = np.log10(N)

    plt.figure(figsize=(6, 4))
    
    plt.plot(log_N, data[benchmark], 
             marker='o', markersize=6, linewidth=2, 
             label='NCBPar.')

    plt.axhline(y=1, color='black', linestyle='--', 
                label='Speedup = 1', linewidth=1.6)

    plt.xticks(fontsize=15)
    plt.yticks(fontsize=15)
    
    plt.legend(loc='best', fontsize=14)
    plt.grid(True, linestyle=':', alpha=0.6)
    
    plt.tight_layout()

    output_file = os.path.join(output_dir, f'{benchmark}-plot.png')
    plt.savefig(output_file, dpi=300, bbox_inches='tight', transparent=True)
    plt.close()
    print(f"Plot for {benchmark} saved at {output_file}")

def main():
    if len(sys.argv) != 3:
        print("Usage: python script.py <csv_dir> <output_directory>")
        sys.exit(1)

    csv_dir = sys.argv[1]
    output_dir = sys.argv[2]

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    data = read_csv(os.path.join(csv_dir, 'ratio.csv'))
    
    benchmarks = data.columns[1:]

    for benchmark in benchmarks:
        create_plot(data, benchmark, output_dir)

if __name__ == "__main__":
    main()