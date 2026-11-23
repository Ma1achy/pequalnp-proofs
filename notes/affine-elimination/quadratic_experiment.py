"""Compare two exact projection orders on inner-product parity. Standard library only."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from flat_elimination import Counts, clause, encoded_bits, metrics, normalize, parity, project


def quadratic_instance(k: int, strict: bool):
    """Variables x[0:k], y[k:2k], t[2k:3k], and optionally a,b in two more blocks."""
    if k < 1:
        raise ValueError("k must be positive")
    n = (5 if strict else 3) * k
    xs, ys, ts = (list(range(block * k, (block + 1) * k)) for block in range(3))
    raw = [parity(ts, 0)]
    auxiliary = []
    for i, (x, y, t) in enumerate(zip(xs, ys, ts)):
        if strict:
            a, b = 3 * k + i, 4 * k + i
            raw.extend([parity((x, t, a), 0), parity((y, t, b), 0)])
            for u, v in ((a, b), (a, t), (b, t)):
                raw.append(clause(-(u + 1), -(v + 1)))
            auxiliary.extend((a, b))
        else:
            raw.extend([clause(-(t + 1), x + 1), clause(-(t + 1), y + 1),
                        clause(t + 1, -(x + 1), -(y + 1))])
    terminals = [v for pair in zip(xs, ys) for v in pair]
    return n, raw, auxiliary, ts, terminals


def oracle_models(k: int, strict: bool):
    """Construct satisfying assignments directly from the bitwise products."""
    for x in range(1 << k):
        for y in range(1 << k):
            t = x & y
            if t.bit_count() % 2:
                continue
            assignment = x | (y << k) | (t << (2 * k))
            if strict:
                assignment |= ((x ^ t) << (3 * k)) | ((y ^ t) << (4 * k))
            yield assignment


def check_projection(flats, remaining, models):
    """Independent model-set oracle for all assignments of the remaining variables."""
    mask = sum(1 << v for v in remaining)
    assert all((row >> 1) & ~mask == 0 for flat in flats for row in flat)
    expected = {model & mask for model in models}
    assignment = 0
    tested = 0
    while True:
        allowed = not any(all(((row >> 1) & assignment).bit_count() % 2 == (row & 1)
                              for row in flat) for flat in flats)
        assert allowed == (assignment in expected), (remaining, assignment, allowed)
        tested += 1
        if assignment == mask:
            return tested
        assignment = (assignment - mask) & mask


def check_all_small_flats(k: int):
    """Enumerate by dimension, starting from all points of the odd quadric."""
    assert 1 <= k <= 3
    bound = 1 << k
    target = {x | (y << k) for x in range(bound) for y in range(bound)
              if (x & y).bit_count() % 2}
    level = {frozenset((point,)) for point in target}
    level_counts = []
    while level:
        level_counts.append(len(level))
        larger = set()
        for flat in level:
            anchor = next(iter(flat))
            for point in target - flat:
                shift = point ^ anchor
                other_coset = {z ^ shift for z in flat}
                if other_coset <= target:
                    larger.add(flat | other_coset)
        level = larger
    max_size = 1 << (len(level_counts) - 1)
    explicit_cover = [{p for p in target if p % bound == x} for x in range(1, bound)]
    assert all(len(flat) == max_size for flat in explicit_cover)
    assert set().union(*explicit_cover) == target
    assert max_size == 1 << (k - 1)
    assert len(target) == (bound - 1) * max_size
    return {"k": k, "odd_points": len(target), "flats_by_dimension": level_counts,
            "largest_flat_size": max_size, "minimum_cover_count": bound - 1}


def check_three_lines():
    # x,y,z are variables 0,1,2. Rows with RHS zero.
    z = 1 << 3
    raw = [(z, 1 << 1), (z, 1 << 2), (z, (1 << 1) | (1 << 2))]
    before = normalize(raw, 3, Counts(), merge=False)
    counts = Counts()
    after = normalize(before, 3, counts, merge=True)
    assert after == before and len(after) == 3 and counts.parallel_merges == 0
    oracle = tuple(range(4, 8))
    assert check_projection(after, (0, 1, 2), oracle) == 8
    assert check_projection(((z,),), (0, 1, 2), oracle) == 8
    return {"reducer_flats": len(after), "minimum_flats": 1, "points_checked": 8}


def compare(k: int, strict: bool, easy: bool, oracle_limit: int):
    n, raw, auxiliary, products, terminals = quadratic_instance(k, strict)
    prefix = auxiliary + products
    order = terminals + auxiliary + products if easy else prefix + terminals
    remain = set(range(n))
    models = tuple(oracle_models(k, strict))
    counts = Counts()
    flats = normalize(raw, n, counts, merge=True)
    initial_count = len(flats)
    projection_size = None
    steps = []
    tested = 0
    for idx in range(n + 1):
        if len(remain) <= oracle_limit or (not easy and idx == len(prefix)):
            tested += check_projection(flats, remain, models)
        steps.append({"eliminated": order[idx - 1] if idx else None,
                      "flats": len(flats), "metrics": metrics(flats, n),
                      "operations": counts.as_dict()})
        if not easy and idx == len(prefix):
            projection_size = len(flats)
            expected_size = 3**k - 2**k if strict else (3**k - 1) // 2
            assert projection_size == expected_size >= 2**k - 1
            if strict:
                assert all(len(flat) == k + 1 for flat in flats)
        if idx == n:
            assert not flats
            break
        counts = Counts()
        flats = project(flats, order[idx], n, counts, merge=True)
        remain.remove(order[idx])
    peak_count = max(step["flats"] for step in steps)
    if easy:
        assert peak_count <= len(raw)
    return {"k": k, "gadget": "binary_plus_parity" if strict else "and_cnf_plus_parity",
            "order": "terminals_first" if easy else "auxiliaries_first",
            "variables": n, "input_flats": len(raw), "encoded_input_bits": encoded_bits(raw, n),
            "initial_flats": initial_count, "peak_flats": peak_count,
            "projected_inner_product_flats": projection_size, "proved_minimum": 2**k - 1,
            "max_exhaustive_remaining_variables": oracle_limit,
            "truth_assignments_checked_across_steps": tested, "final_sat": True, "steps": steps}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=6)
    parser.add_argument("--oracle-limit", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("quadratic-results.json"))
    args = parser.parse_args()
    runs = []
    for k in range(1, args.max_k + 1):
        for strict in (False, True):
            for easy in (False, True):
                run = compare(k, strict, easy, args.oracle_limit)
                runs.append(run)
                print(k, run["gadget"], run["order"], run["peak_flats"],
                      run["projected_inner_product_flats"], flush=True)
    result = {"runs": runs, "three_lines": check_three_lines(),
              "all_flats_checks": [check_all_small_flats(k) for k in (1, 2, 3)]}
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
