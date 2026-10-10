# Without error bars:
# python3 ./speedup_plot_compare.py out-dswp-arran out-dswp-nc out-dswp-noNB out-dswp-comparison-all
#
# With error bars:
# python3 ./speedup_plot_compare.py out-dswp-arran out-dswp-nc out-dswp-noNB out-dswp-comparison-all --err

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import sys
import os

def read_csv(file_path):
    try:
        return pd.read_csv(file_path, sep=r"\s+")
    except pd.errors.ParserError:
        print(f"Error: The file {file_path} does not have the correct format.")
        sys.exit(1)


def create_comparison_plot(
    data_commute,
    data_no_commute,
    data_no_NB,
    err_commute,
    err_no_commute,
    err_no_NB,
    benchmark,
    output_dir,
    error_bars=False
):
    N = data_commute.iloc[:, 0]
    log_N = np.log10(N)

    plt.figure(figsize=(6, 4))

    if error_bars:
        # Plot with error bars
        plt.errorbar(
            log_N,
            data_commute[benchmark],
            yerr=err_commute[benchmark],
            label='NCBPar.',
            marker='o',
            markersize=6,
            linewidth=2,
            capsize=4
        )

        plt.errorbar(
            log_N,
            data_no_commute[benchmark],
            yerr=err_no_commute[benchmark],
            label='False-Comm.',
            marker='s',
            markersize=6,
            linewidth=2,
            color='red',
            capsize=4
        )

        plt.errorbar(
            log_N,
            data_no_NB[benchmark],
            yerr=err_no_NB[benchmark],
            label='No-NCB.',
            marker='^',
            markersize=6,
            linewidth=2,
            color='green',
            capsize=4
        )

    else:
        # Plot without error bars
        plt.plot(
            log_N,
            data_commute[benchmark],
            label='NCBPar.',
            marker='o',
            markersize=6,
            linewidth=2
        )

        plt.plot(
            log_N,
            data_no_commute[benchmark],
            label='False-Comm.',
            marker='s',
            markersize=6,
            linewidth=2,
            color='red'
        )

        plt.plot(
            log_N,
            data_no_NB[benchmark],
            label='No-NCB.',
            marker='^',
            markersize=6,
            linewidth=2,
            color='green'
        )

    plt.axhline(
        y=1,
        color='black',
        linestyle='--',
        label='Speedup = 1',
        linewidth=1.6
    )

    plt.xlabel('Log(Computation Size)', fontsize=19)
    plt.ylabel('Par-to-Seq Speedup', fontsize=19)

    plt.xticks(fontsize=19)
    plt.yticks(fontsize=19)

    plt.legend(loc='best', fontsize=14)
    plt.grid(True, linestyle=':', alpha=0.6)

    plt.tight_layout()

    output_file = os.path.join(
        output_dir,
        f'{benchmark}-comparison.png'
    )

    plt.savefig(
        output_file,
        dpi=300,
        bbox_inches='tight',
        transparent=True
    )

    plt.close()

    print(f"Plot for {benchmark} saved at {output_file}")


def main():
    if len(sys.argv) < 5 or len(sys.argv) > 6:
        print(
            "Usage: python script.py "
            "<commute_csv_dir> "
            "<no_commute_csv_dir> "
            "<no_NB_csv_dir> "
            "<output_directory> "
            "[--err]"
        )
        sys.exit(1)

    commute_csv = sys.argv[1]
    no_commute_csv = sys.argv[2]
    no_NB_csv = sys.argv[3]
    output_dir = sys.argv[4]

    error_bars = False

    if len(sys.argv) == 6:
        if sys.argv[5] == "--err":
            error_bars = True
        else:
            print(f"Unknown option: {sys.argv[5]}")
            print("Use: --err")
            sys.exit(1)

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    data_commute = read_csv(os.path.join(commute_csv, 'ratio.csv'))
    data_no_commute = read_csv(os.path.join(no_commute_csv, 'ratio.csv'))
    data_no_NB = read_csv(os.path.join(no_NB_csv, 'ratio.csv'))

    # Only read error files when error bars are requested.
    if error_bars:
        err_commute = read_csv(os.path.join(commute_csv, 'ratio_std.csv'))
        err_no_commute = read_csv(os.path.join(no_commute_csv, 'ratio_std.csv'))
        err_no_NB = read_csv(os.path.join(no_NB_csv, 'ratio_std.csv'))
    else:
        err_commute = None
        err_no_commute = None
        err_no_NB = None

    benchmarks = data_commute.columns[1:]

    for benchmark in benchmarks:
        create_comparison_plot(
            data_commute,
            data_no_commute,
            data_no_NB,
            err_commute,
            err_no_commute,
            err_no_NB,
            benchmark,
            output_dir,
            error_bars=error_bars
        )


if __name__ == "__main__":
    main()