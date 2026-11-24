"""Compare the exact Lean input rows to the archived LT6.csv for a specified source file."""

import argparse
import csv
from decimal import Decimal
from hashlib import sha256
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "csv", nargs="?", type=Path, default=Path(__file__).with_name("data") / "LT6.csv",
        help="Path to the original LT6.csv (defaults to the bundled copy)",
    )
    path = parser.parse_args().csv
    digest = sha256(path.read_bytes()).hexdigest()
    if digest != "8faaafd4d89fdc98749177fd08db3afece59dc563d37914fcb47afe5f0374eba":
        raise ValueError(f"Source digest differs: {digest}")

    source = {}
    with path.open(newline="", encoding="utf-8") as source_file:
        for row in csv.DictReader(source_file):
            if row["effector"] != "CART" or row["time"] not in {"3", "6"}:
                continue
            ratio = re.fullmatch(r"1:(\d+)", row["ratio"])
            if not ratio:
                raise ValueError(f'Unexpected ratio {row["ratio"]}')
            key = (row["target"], int(ratio.group(1)), int(row["time"]))
            count = Decimal(row["CD3"]) * 10
            if key in source or count != count.to_integral_value() or count < 0:
                raise ValueError(f"Unexpected source entry for {key}")
            source[key] = int(count)

    lean = Path(__file__).with_name("Direction3.lean").read_text(encoding="utf-8")
    table = lean.split("def observations : List Observation := [", 1)[1].split("]", 1)[0]
    encoded = {}
    for line in table.strip().splitlines():
        row = re.fullmatch(r'\s*⟨"([^"]+)", (\d+), (\d+), (\d+)⟩,?\s*', line)
        if not row:
            raise ValueError(f"Unexpected Lean input line: {line}")
        target, ratio, early, late = row.groups()
        for day, count in [(3, early), (6, late)]:
            key = (target, int(ratio), day)
            if key in encoded:
                raise ValueError(f"Duplicate Lean key {key}")
            encoded[key] = int(count)
    if len(source) != 24 or source != encoded:
        raise ValueError("Lean inputs differ from the 24 selected source values")
    print(f"Source SHA-256 {digest}")
    print("24 exact CD3 values across 12 paired rows match Direction3.lean")


if __name__ == "__main__":
    main()
