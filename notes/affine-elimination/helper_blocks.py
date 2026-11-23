"""Eliminate a block of helpers when each forbidden flat has helper rank at most one."""

import argparse
import random
from itertools import combinations, product

from flat_elimination import Counts, encoded_bits, normalize, project, rref, satisfied


def project_block(flats, n, helpers):
    """Return cylinders and consistent dependent-subset conflicts, without global minimization."""
    helpers = tuple(helpers)
    if len(set(helpers)) != len(helpers) or any(not 0 <= h < n for h in helpers):
        raise ValueError("invalid helper IDs")
    helper_mask = sum(1 << (h + 1) for h in helpers)
    counts = Counts()
    guards, output = [], []
    for flat in flats:
        rows = rref(flat, n, counts)
        if rows is None:
            continue
        pivot = next((row for row in rows if row & helper_mask), None)
        if pivot is None:
            output.append(rows)
            continue
        normal = pivot & helper_mask
        domain = []
        for row in rows:
            part = row & helper_mask
            if row == pivot:
                continue
            if part and part != normal:
                raise ValueError("flat has helper rank greater than one")
            domain.append(row ^ pivot if part else row)
        # If active, avoidance requires normal.w = parity(visible mask) + constant.
        demand = (pivot ^ normal) ^ 1
        guards.append((normal, demand, domain))

    tested = 0
    for size in range(2, min(len(helpers) + 1, len(guards)) + 1):
        for subset in combinations(guards, size):
            normal = 0
            rhs = 0
            for vector, demand, _ in subset:
                normal ^= vector
                rhs ^= demand
            tested += 1
            if normal:
                continue
            rows = [row for _, _, domain in subset for row in domain]
            rows.append(rhs ^ 1)
            conflict = rref(rows, n, counts)
            if conflict is not None:
                output.append(conflict)
    return tuple(output), tested


def fixed_block(k, indices, pattern):
    fixed = []
    dot = 0
    for local, index in enumerate(indices):
        value = pattern >> local & 1
        fixed.append((1 << (1 + index)) | value)
        dot |= value << (1 + k + index)
    return fixed, dot


def equality_family(k, h):
    """h+1 balanced blocks. The final block must equal the XOR of all h helpers."""
    if not 0 <= h < k:
        raise ValueError("expected 0 <= h < k")
    index = 0
    clauses = []
    helpers = tuple(range(2*k, 2*k + h))
    for block in range(h + 1):
        size = k // (h + 1) + int(block < k % (h + 1))
        indices = range(index, index + size)
        index += size
        witness_bits = helpers if block == h else (helpers[block],)
        parity = sum(1 << (1 + j) for j in witness_bits)
        for pattern in range(1 << size):
            fixed, dot = fixed_block(k, indices, pattern)
            clauses.append(tuple(fixed + [parity ^ dot ^ 1]))
    return helpers, clauses


def check_family(k, h):
    helpers, raw = equality_family(k, h)
    n = 2*k + h
    projected, tested = project_block(raw, n, helpers)
    direct = []
    for pattern in range(1, 1 << k):
        fixed, dot = fixed_block(k, range(k), pattern)
        direct.append(tuple(fixed + [dot ^ 1]))
    reduced = normalize(projected, n, Counts())
    assert len(reduced) == 2**k - 1
    assert reduced == normalize(direct, n, Counts())
    if h == 1:
        singles = normalize(raw, n, Counts())
        assert project(singles, helpers[0], n, Counts()) == reduced
    for x, y in product(range(1 << k), repeat=2):
        point = x | (y << k)
        expected = ((x & y).bit_count() & 1) == 0
        count = sum(satisfied(raw, point | (w << (2*k))) for w in range(1 << h))
        assert count == int(expected)
        assert satisfied(projected, point) == expected
    return k, h, len(raw), len(reduced), tested, encoded_bits(raw, n)


def check_random():
    rng = random.Random(70281)
    for case in range(512):
        n = 5
        h = case % 4
        helpers = tuple(rng.sample(range(n), h))
        mask = sum(1 << j for j in helpers)
        visible = ((1 << n) - 1) ^ mask
        raw = []
        for _ in range(rng.randrange(9)):
            normal = rng.randrange(1 << n) & mask
            rows = []
            for _ in range(rng.randrange(5)):
                vector = (rng.randrange(1 << n) & visible) | (normal if rng.randrange(2) else 0)
                rows.append(2 * vector + rng.randrange(2))
            raw.append(rows)
        projected, _ = project_block(raw, n, helpers)
        for p in range(1 << n):
            if p & mask:
                continue
            allowed = any(satisfied(raw, p | w) for w in range(1 << n) if not w & visible)
            assert satisfied(projected, p) == allowed
    # A singleton in a two-helper plane needs two independent helper rows.
    try:
        project_block([(2, 4)], 2, (0, 1))
    except ValueError as e:
        assert "rank greater than one" in str(e)
    else:
        raise AssertionError("accepted an out-of-class flat")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-k", type=int, default=5)
    args = parser.parse_args()
    check_random()
    print("512 seeded block projections passed")
    print("k helpers input_clauses projected_clauses subsets_tested dense_input_bits")
    for k in range(2, args.max_k + 1):
        for h in range(1, min(3, k - 1) + 1):
            print(*check_family(k, h))
