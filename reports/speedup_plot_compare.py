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

def create_comparison_plot(data_commute, data_no_commute, benchmark, output_dir):
    N = data_commute.iloc[:, 0]
    log_N = np.log10(N)

    plt.figure(figsize=(6, 4))
    
    plt.rcParams.update({'font.size': 12})
    
    plt.plot(log_N, data_commute[benchmark], label='Comm.', 
             marker='o', markersize=6, linewidth=2)
    plt.plot(log_N, data_no_commute[benchmark], label='Non-Comm.', 
             marker='s', markersize=6, linewidth=2, color='red')

    plt.axhline(y=1, color='black', linestyle='--', 
                label='Speedup = 1', linewidth=1.5)

    plt.xlabel('Log(Computation Size)')
    plt.ylabel('Parallel-to-Sequential Speedup')
    
    benchmark_name = benchmark.replace('vote-run', 'vote').title()
    plt.title(benchmark_name, fontsize=12, pad=10)
    
    plt.legend(loc='best', fontsize=10)
    plt.grid(True, linestyle=':', alpha=0.6)
    
    plt.tight_layout()

    output_file = os.path.join(output_dir, f'{benchmark}-comparison.png')
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"Plot for {benchmark} saved at {output_file}")

def main():
    if len(sys.argv) != 4:
        print("Usage: python script.py <commute_csv_dir> <no_commute_csv_dir> <output_directory>")
        sys.exit(1)

    commute_csv = sys.argv[1]
    no_commute_csv = sys.argv[2]
    output_dir = sys.argv[3]

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    data_commute = read_csv(os.path.join(commute_csv, 'ratio.csv'))
    data_no_commute = read_csv(os.path.join(no_commute_csv, 'ratio.csv'))

    benchmarks = data_commute.columns[1:]

    for benchmark in benchmarks:
        create_comparison_plot(data_commute, data_no_commute, benchmark, output_dir)

if __name__ == "__main__":
    main()