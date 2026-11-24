"""Recompute the appendix LT6 table from its archived primary predictions."""

from collections import defaultdict
import csv
from math import sqrt
from pathlib import Path
from statistics import mean


def fold_scores(rows):
    rows = sorted(rows, key=lambda row: int(row["source_day"]))
    if [int(row["source_day"]) for row in rows] != [3, 6, 10, 16]:
        raise ValueError("Each held condition needs all four sample days")

    def error(marker):
        residuals = [float(row["predicted_" + marker])
                     - float(row["observed_" + marker]) for row in rows[1:]]
        return sqrt(mean(value ** 2 for value in residuals))

    predicted = [float(row["predicted_cd3"]) for row in rows[:2]]
    rise = predicted[1] > predicted[0] + 1e-7
    return error("cd33"), error("cd3"), rise


def main():
    table = Path(__file__).with_name("data") / "lt6_predictions.csv"
    conditions = defaultdict(list)
    with table.open(newline="", encoding="utf-8") as source:
        for row in csv.DictReader(source):
            key = (row["model"], row["strategy"], row["genotype"],
                   row["held_ratio"])
            conditions[key].append(row)

    by_method = defaultdict(list)
    for (model, strategy, genotype, ratio), rows in conditions.items():
        by_method[model, strategy].append(fold_scores(rows))
    print("Model and training rule                 CD33 RMSE   CD3 RMSE  Rises")
    for (model, strategy), scores in sorted(by_method.items()):
        if len(scores) != 12:
            raise ValueError(f"Expected twelve held conditions for {model} {strategy}")
        target, consumer, rises = zip(*scores)
        name = f"{model} / {strategy}"
        print(f"{name:40s} {mean(target):9,.0f} {mean(consumer):10,.0f} {sum(rises):4d}/12")


if __name__ == "__main__":
    main()
