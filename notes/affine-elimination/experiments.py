"""Rebuild the small-instance checks and per-step measurements with Python 3."""

import argparse
import json
import random
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path

from pure_baselines import gaussian_decision, two_sat_decision
from flat_elimination import Counts, clause, decide, encoded_bits, metrics, normalize, parity, project, satisfied


def reference_value(raw, assignment, n):
    """Evaluate raw equations by summing individual bits, independently of the solver."""
    for flat in raw:
        for row in flat:
            total = sum(((row >> (i + 1)) & 1) * ((assignment >> i) & 1)
                        for i in range(n))
            if total % 2 != row % 2:
                break
        else:
            return False
    return True


def table(flats, n):
    return tuple(satisfied(flats, assignment) for assignment in range(1 << n))


def project_table(values, variable):
    return tuple(a or values[i ^ (1 << variable)] for i, a in enumerate(values))


def exactly_one(a, b, c):
    """Three zero-based variable IDs, positive one-in-three."""
    return [parity((a, b, c), 1)] + [clause(-i - 1, -j - 1) for i, j in combinations((a, b, c), 2)]


def pigeonhole(pigeons, holes):
    rows = [clause(*(1 + p * holes + h for h in range(holes))) for p in range(pigeons)]
    rows.extend(clause(-1 - p * holes - h, -1 - q * holes - h)
                for h in range(holes) for p, q in combinations(range(pigeons), 2))
    return rows


def examples():
    # Variable order is z,x,y,t. Forbid x=z=0 and y=z xor t=0.
    yield "minimal_width_growth", 4, [clause(2, 1), (1 << 3, (1 << 1) | (1 << 4))], True
    yield "parity_sat", 5, [parity((0, 1, 4), 1), parity((1, 2), 0), parity((2, 3, 4), 1)], True
    yield "parity_unsat", 4, [parity((0, 1), 0), parity((1, 2, 3), 1), parity((0, 2, 3), 0)], False
    yield "2sat_sat", 4, [clause(1, 2), clause(-1, 3), clause(-2, -3), clause(3, 4)], True
    yield "2sat_unsat", 2, [clause(x, y) for x, y in product((1, -1), (2, -2))], False
    yield "one_in_three_sat", 5, exactly_one(0, 1, 2) + exactly_one(2, 3, 4), True
    all_triples = [flat for triple in combinations(range(4), 3) for flat in exactly_one(*triple)]
    yield "one_in_three_unsat", 4, all_triples, False
    yield "pigeonhole_sat_2_2", 4, pigeonhole(2, 2), True
    yield "pigeonhole_unsat_3_2", 6, pigeonhole(3, 2), False
    yield "empty_conjunction", 0, [], True
    yield "empty_clause", 0, [()], False
    for seed in (2718, 31415, 65537):
        rng = random.Random(seed)
        n = 6
        # Alternate ordinary clauses, parity equations and general affine clauses.
        raw = []
        for i in range(9):
            if i % 3 == 0:
                raw.append(clause(*(rng.choice((-1, 1)) * (x + 1) for x in rng.sample(range(n), 3))))
            elif i % 3 == 1:
                raw.append(parity(rng.sample(range(n), 3), rng.randrange(2)))
            else:
                raw.append(tuple(rng.randrange(2, 1 << (n + 1)) for _ in range(2)))
        yield f"mixed_seed_{seed}", n, raw, None


def exercise_instance(name, n, raw, expected_sat, merge):
    values = tuple(reference_value(raw, x, n) for x in range(1 << n))
    oracle_sat = any(values)
    assert decide(raw, n, merge) == oracle_sat, name
    if expected_sat is not None:
        assert expected_sat == oracle_sat, name
    trace = []
    counts = Counts()
    flats = normalize(raw, n, counts, merge)
    assert table(flats, n) == values, name
    trace.append({"eliminated": None, **metrics(flats, n), "operations": counts.as_dict()})
    for variable in range(n):
        counts = Counts()
        flats = project(flats, variable, n, counts, merge)
        values = project_table(values, variable)
        assert table(flats, n) == values, (name, variable)
        if name == "minimal_width_growth" and variable == 0:
            assert flats == normalize([clause(2, 3, -4)], n, Counts())
        assert all(row >> 1 & ((1 << (variable + 1)) - 1) == 0 for flat in flats for row in flat)
        trace.append({"eliminated": variable, **metrics(flats, n), "operations": counts.as_dict()})
    assert flats == (() if oracle_sat else ((),)), name
    return {
        "name": name,
        "variables": n,
        "merge_parallel_cosets": merge,
        "original_dense_encoded_bits": encoded_bits(raw, n),
        "raw_input": raw,
        "satisfiable": oracle_sat,
        "trace": trace,
    }


def check_baseline_identities():
    for a, b, c, d in product((0, 1), repeat=4):
        lhs = any((a or z ^ b) and (c or z ^ d) for z in (0, 1))
        assert lhs == bool(a or c or not (b ^ d))
    for a, b, c in product((0, 1), repeat=3):
        x = a | b << 1 | c << 2
        assert reference_value(exactly_one(0, 1, 2), x, 3) == (a + b + c == 1)


def exhaustive_checks():
    check_baseline_identities()
    n = 3
    # Every nonempty flat has a basis of at most n nonzero equations.
    # Include tautology and contradiction as possible one-row systems.
    all_flats = {}
    checked_systems = 0
    for k in range(n + 1):
        for rows in combinations(range(1 << (n + 1)), k):
            normal = normalize([rows], n, Counts())
            membership = tuple(not reference_value((rows,), x, n) for x in range(1 << n))
            assert table(normal, n) == tuple(not v for v in membership)
            if normal:
                previous = all_flats.setdefault(membership, normal[0])
                assert previous == normal[0]
            checked_systems += 1
    assert len(all_flats) == 51
    checked_pairs = 0
    for a, b in combinations_with_replacement(all_flats, 2):
        expected = tuple(not (inside_a or inside_b) for inside_a, inside_b in zip(a, b))
        for merge in (False, True):
            flats = normalize([all_flats[a], all_flats[b]], n, Counts(), merge)
            assert table(flats, n) == expected
            for variable in range(n):
                projected = project(flats, variable, n, Counts(), merge)
                assert table(projected, n) == project_table(expected, variable)
                checked_pairs += 1
    checked_functions = 0
    points = [tuple((1 << (i + 1)) | ((x >> i) & 1) for i in range(n)) for x in range(1 << n)]
    for false_mask in range(1 << (1 << n)):
        raw = [flat for i, flat in enumerate(points) if false_mask >> i & 1]
        expected = tuple(not ((false_mask >> i) & 1) for i in range(1 << n))
        for merge in (False, True):
            flats = normalize(raw, n, Counts(), merge)
            assert table(flats, n) == expected
            for variable in range(n):
                projected = project(flats, variable, n, Counts(), merge)
                assert table(projected, n) == project_table(expected, variable)
                checked_functions += 1
    return {
        "baseline_identity_inputs": 16,
        "exactly_one_inputs": 8,
        "raw_single_flat_systems_checked": checked_systems,
        "distinct_nonempty_flats_on_three_variables": len(all_flats),
        "flat_pair_projection_cases": checked_pairs,
        "point_union_function_projection_cases": checked_functions,
    }


def check_pure_baselines():
    records = []
    for name, n, raw, expected_sat in examples():
        if name.startswith("parity_"):
            sat, stats = gaussian_decision(raw, n)
            solver = "gaussian"
        elif name.startswith("2sat_"):
            sat, stats = two_sat_decision(raw, n)
            solver = "scc"
        else:
            continue
        assert sat == expected_sat
        records.append({"name": name, "solver": solver, "satisfiable": sat, **stats})

    # Instances too large for the truth-table oracle, with explicit certificates.
    # All variables equal x_0=0. x_last=0 retains the all-zero model. x_last=1
    # implies 0=1 by summing the chain equations. Check two independent solvers.
    n = 64
    for last_bit in (0, 1):
        raw = ([parity((0,), 0)] + [parity((i, i + 1), 0) for i in range(n - 1)]
               + [parity((n - 1,), last_bit)])
        sat, stats = gaussian_decision(raw, n)
        trace = []
        counts = Counts()
        flats = normalize(raw, n, counts)
        trace.append({"eliminated": None, **metrics(flats, n), "operations": counts.as_dict()})
        for variable in range(n):
            counts = Counts()
            flats = project(flats, variable, n, counts)
            trace.append({"eliminated": variable, **metrics(flats, n), "operations": counts.as_dict()})
        assert sat == (last_bit == 0)
        assert flats == (() if sat else ((),))
        records.append({"name": f"parity_chain_64_last_{last_bit}", "solver": "gaussian_and_generic",
                        "original_dense_encoded_bits": encoded_bits(raw, n),
                        "satisfiable": sat, "generic_trace": trace, **stats})

    # Cross-check both reference solvers against full Boolean enumeration.
    for seed in range(64):
        rng = random.Random(seed)
        n = 5
        xor_rows = [parity(rng.sample(range(n), rng.randrange(n + 1)), rng.randrange(2))
                    for _ in range(rng.randrange(11))]
        cnf_rows = [clause(*(rng.choice((-1, 1)) * rng.randrange(1, n + 1)
                             for _ in range(rng.randrange(1, 3)))) for _ in range(rng.randrange(12))]
        for raw, decision in ((xor_rows, gaussian_decision), (cnf_rows, two_sat_decision)):
            expected = any(reference_value(raw, x, n) for x in range(1 << n))
            assert decision(raw, n)[0] == expected
    return {"records": records, "seeded_truth_table_checks": 128, "seeds": [0, 63]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("experiments.json"))
    args = parser.parse_args()
    if not __debug__:
        parser.error("run with Python assertions enabled")
    checks = exhaustive_checks()
    runs = [exercise_instance(name, n, raw, label, merge) for name, n, raw, label in examples()
            for merge in (False, True)]
    args.output.write_text(json.dumps({"checks": checks, "runs": runs, "pure_baselines": check_pure_baselines()}, indent=2) + "\n")
    print(json.dumps(checks))
    print(f"{len(runs)} experiment traces, {sum(len(r['trace']) for r in runs)} states; {args.output}")


if __name__ == "__main__":
    main()
