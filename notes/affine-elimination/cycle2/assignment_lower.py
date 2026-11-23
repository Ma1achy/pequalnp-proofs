"""Exhaustive small audits of matching signatures and directed-cycle fibre sizes."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial


def is_cycle(p):
    position = 0
    size = 0
    while True:
        position = p[position]
        size += 1
        if position == 0:
            return size == len(p)


def edges(p):
    return sum(1 << (i * len(p) + j) for i, j in enumerate(p))


def signature(p, red):
    selected = [(i, j) for i, j in enumerate(p) if red >> (i * len(p) + j) & 1]
    return sum(1 << i for i, _ in selected), sum(1 << j for _, j in selected)


def signature_capacity(m):
    cycles = tuple(p for p in permutations(range(m)) if is_cycle(p))
    checked = 0
    for z in range(1, m):
        for rows in combinations(range(m), z):
            counts = Counter(frozenset(p[i] for i in rows) for p in cycles)
            for cols in combinations(range(m), z):
                t = len(set(rows) - set(cols))
                assert counts[frozenset(cols)] == t * factorial(z - 1) * factorial(m - z - 1)
                checked += 1
    return checked


def check_signatures(m, cycle):
    perms = tuple(p for p in permutations(range(m)) if not cycle or is_cycle(p))
    solutions = [(p, edges(p)) for p in perms]
    positions = [i * m + j for i in range(m) for j in range(m) if not cycle or i != j]
    tested_splits = tested_pairs = 0
    for split in combinations(positions, len(positions) // 2):
        red = sum(1 << i for i in split)
        reps = {}
        counts = Counter()
        for p, mask in solutions:
            sig = signature(p, red)
            reps[sig] = mask
            counts[sig[0].bit_count()] += 1
        zmean = sum(Fraction(z * count, len(solutions)) for z, count in counts.items())
        zvar = sum(count * (z - zmean)**2 for z, count in counts.items()) / len(solutions)
        if not cycle and m > 1:
            rowcounts = [sum((red >> (i * m + j)) & 1 for j in range(m)) for i in range(m)]
            colcounts = [sum((red >> (i * m + j)) & 1 for i in range(m)) for j in range(m)]
            sq = sum((m*m * ((red >> (i*m+j)) & 1) - m*rowcounts[i] - m*colcounts[j] + len(split))**2
                     for i in range(m) for j in range(m))
            assert zvar == Fraction(sq, m**4 * (m - 1))
        bound = sum(count * comb(m, z) for z, count in counts.items())
        assert len(reps) * len(solutions) * (2 if cycle else 1) >= bound
        if m <= 3:
            for a, b in combinations(reps.values(), 2):
                crossed = [(a & red) | (b & ~red), (b & red) | (a & ~red)]
                assert not all(any(mask & g == mask for _, mask in solutions) for g in crossed)
                tested_pairs += 1
        tested_splits += 1
    return tested_splits, tested_pairs


if __name__ == '__main__':
    for m in range(2, 8):
        print(f'm={m} directed-cycle (R,C) fibre checks={signature_capacity(m)}')
    for m in (2, 3, 4):
        for cycle in (False, True):
            splits, pairs = check_signatures(m, cycle)
            print(f'm={m} directed_cycles={cycle} balanced_splits={splits} exhaustive_crosses={pairs}')
