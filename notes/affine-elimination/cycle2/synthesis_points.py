"""Classify five full-domain singleton forbidden fibers for three product pairs."""

import argparse
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json


def submasks(mask):
    value = mask
    while True:
        yield value
        if value == 0:
            break
        value = (value - 1) & mask


def full_points():
    table = [len({0, z & 3, (z >> 2) & 3, (z >> 4) & 3, z >> 6}) == 4 for z in range(256)]
    weight_counts = Counter()
    for pivots in combinations(range(8), 6):
        mask = 255 ^ sum(1 << p for p in pivots)
        options = [[(1 << p) | tail for tail in submasks(mask & ~((2 << p) - 1))] for p in pivots]
        for basis in product(*options):
            span = [0]
            for v in basis:
                span.extend([x ^ v for x in span])
            for origin in submasks(mask):
                values = [int(table[origin ^ x]) for x in span]
                weight = sum(values)
                weight_counts[weight] += 1
    assert sum(weight_counts.values()) == 43180 and max(weight_counts) == 24
    return {"flats_checked": sum(weight_counts.values()), "weight_counts": dict(sorted(weight_counts.items()))}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("synthesis-points-results.json"))
    args = parser.parse_args()
    result = full_points()
    path = args.output
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(result)
