import csv
from pathlib import Path

import matplotlib.pyplot as plt

RESULTS_DIR = Path("learning_results")
PROBLEMS = ["Problem1", "Problem2", "Problem4", "Problem7", "ProblemPin"]


def read_points(csv_path):
    times = []
    states = []

    with csv_path.open(newline="") as file:
        reader = csv.DictReader(file)
        for row in reader:
            times.append(int(row["time_ms"]))
            states.append(int(row["states"]))

    return times, states


def plot_problem(problem):
    csv_path = RESULTS_DIR / f"{problem}_states.csv"

    if not csv_path.exists():
        print(f"Missing {csv_path}")
        return

    times_ms, states = read_points(csv_path)
    times_seconds = [time / 1000.0 for time in times_ms]

    plt.figure(figsize=(8, 5))
    plt.plot(times_seconds, states, marker="o")
    plt.xlabel("Time (seconds)")
    plt.ylabel("Number of states")
    plt.title(f"Number of states over time for {problem}")
    plt.grid(True)
    plt.tight_layout()

    output_path = RESULTS_DIR / f"{problem}_states_over_time.png"
    plt.savefig(output_path, dpi=300)
    plt.close()

    print(f"Wrote {output_path}")


for problem in PROBLEMS:
    plot_problem(problem)