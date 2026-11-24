#!/usr/bin/env python3
"""Finite affine isolation on distinct, rooted directed-tour incidence vectors.

A row packs its linear coefficients in the low e bits and a random affine
offset in bit e. A witness v survives exactly when every row evaluates to 0.
A trial uses all prefix lengths 1..K of the same independent uniform rows.
The prefixes need not be independent: one good length suffices.

For d>0 choose k=ceil(log2 d)+1, so d/2^k lies in (1/4,1/2]. Pairwise
independence and the union bound give isolation probability at least
d/2^k − d(d−1)/2^(2k) >= 3/16. For d=1 the probability is exactly 1/2.
Repeating independent trials t times with 2^e*(13/16)^t<1 guarantees that
some fixed list serves all graphs of this input length. Here we construct
and exhaustively replay concrete small lists. This script only filters the
tour witnesses; it constructs no graph reduction encoding the hash.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import factorial, prod
from random import Random

from boolean_jet import tour_masks, zeta_full


def survivor_mask(row, tours, edges):
    return sum(1 << i for i, v in enumerate(tours)
               if ((row & v).bit_count() & 1) == (row >> edges))


def hash_distribution(tours, edges):
    patterns = Counter(survivor_mask(row, tours, edges) for row in range(1 << (edges+1)))
    total = sum(patterns.values())
    for i in range(len(tours)):
        assert sum(count for mask, count in patterns.items() if mask >> i & 1) == total//2
    for i, j in combinations(range(len(tours)), 2):
        for a in (0, 1):
            for b in (0, 1):
                assert sum(count for mask, count in patterns.items()
                           if (mask >> i & 1, mask >> j & 1) == (a, b)) == total//4
    return patterns


def fixed_level_probabilities(initial, patterns, levels):
    """Exact probabilities, retaining all dependencies among three or more tours."""
    distribution = {initial: 1}
    row_count = sum(patterns.values())
    result = []
    for k in range(1, levels+1):
        after = Counter()
        for current, count in distribution.items():
            for row, multiplicity in patterns.items():
                after[current & row] += count*multiplicity
        distribution = after
        outcomes = row_count**k
        assert sum(after.values()) == outcomes
        result.append(Fraction(sum(count for mask, count in after.items() if mask.bit_count() == 1), outcomes))
    return result


def filtered_parity(graph, tours, rows, edges):
    """Evaluate the filtered tour sum over F₂ using a product of affine indicators."""
    result = 0
    for tour in tours:
        arc_indices = [e for e in range(edges) if tour >> e & 1]
        monomial = prod((graph >> e) & 1 for e in arc_indices)
        for row in rows:
            linear = sum(row >> e & 1 for e in arc_indices)
            monomial *= (1 + (row >> edges) + linear) % 2
        result ^= monomial
    return result


def prefix_filters(seed, tours, edges):
    mask = (1 << len(tours))-1
    filters = []
    for row in seed:
        mask &= survivor_mask(row, tours, edges)
        filters.append(mask)
    return filters


def fixed_seeds(families, tours, edges, levels):
    """Select explicit matrices and replay them. The probability proof is separate."""
    bound = 0
    while (1 << edges)*13**bound >= 16**bound:
        bound += 1
    rng = Random(31711 + edges)
    missing = set(families) - {0}
    seeds = []
    for _ in range(bound):
        seed = tuple(rng.getrandbits(edges+1) for _ in range(levels))
        filters = prefix_filters(seed, tours, edges)
        hit = {f for f in missing if any((f & h).bit_count() == 1 for h in filters)}
        if hit:  # Omitted trials could not help any still-uncovered witness family.
            seeds.append(seed)
            missing -= hit
        if not missing:
            break
    assert not missing, "the deterministic test list failed"
    return seeds, bound


def check_completion_ideal(n, families, tours, coefficients):
    """Möbius inversion in both directions on the full Boolean cube over F₂."""
    edges = n*(n-1)
    full = (1 << edges)-1
    parity = [f.bit_count() % 2 for f in families]
    promised = [g for g, f in enumerate(families) if f.bit_count() <= 1]
    free = [g for g, f in enumerate(families) if f.bit_count() >= 2]
    pairs = {a | b for a, b in combinations(tours, 2)}
    assert free == [g for g in range(full+1) if any(g & pair == pair for pair in pairs)]
    assert len(free) == {2: 0, 3: 1, 4: 270}[n]
    rng = Random(12041+n)

    def assignments():
        if n <= 3:
            return range(1 << len(free))
        return [rng.getrandbits(len(free)) for _ in range(24)]

    def varies_with_graph(values):
        # Two inputs containing exactly the same tours can still receive
        # opposite answers. Thus the sample depends on more than tour count.
        answers = {}
        for g in free:
            family = families[g]
            if family in answers and answers[family] != values[g]:
                return True
            answers[family] = values[g]
        return False

    forward = list(assignments())
    for bits in forward:
        values = parity.copy()
        for i, g in enumerate(free):
            values[g] = bits >> i & 1
        difference = [a ^ b for a, b in zip(zeta_full(values, edges), coefficients)]
        assert not any(difference[g] for g in promised)
        assert zeta_full(difference, edges) == [x ^ y for x, y in zip(values, parity)]
        if n == 4:
            assert varies_with_graph(values)

    backward = list(assignments())
    for bits in backward:
        perturbed = coefficients.copy()
        values = parity.copy()
        for i, support in enumerate(free):
            if bits >> i & 1:
                perturbed[support] ^= 1
                # Independently evaluate this squarefree monomial by toggling
                # precisely its supergraphs, using no transform.
                unchosen = full ^ support
                extra = unchosen
                while True:
                    values[support | extra] ^= 1
                    if not extra:
                        break
                    extra = (extra-1) & unchosen
        assert all(values[g] == parity[g] for g in promised)
        assert zeta_full(values, edges) == perturbed
        if n == 4:
            assert varies_with_graph(values)
    print(f"n={n} completion ideal: free supports={len(free)}, forward tests={len(forward)}, "
          f"inverse tests={len(backward)}, graph supports per test={len(families)}")


def check_parity_completion(n, graphs, tours):
    """Construct the truth table independently by counting paths rooted at 0."""
    arcs = [(u, v) for u in range(n) for v in range(n) if u != v]
    edge = {a: 1 << i for i, a in enumerate(arcs)}
    counts = []
    for graph, tour_family in enumerate(graphs):
        paths = {(1, 0): 1}
        for visited in range(1, 1 << n, 2):
            for last in range(1, n):
                if visited >> last & 1:
                    prev = visited ^ (1 << last)
                    paths[visited, last] = sum(paths.get((prev, u), 0) for u in range(n)
                                               if prev >> u & 1 and graph & edge[u, last])
        full = (1 << n)-1
        count = sum(paths[full, u] for u in range(1, n) if graph & edge[u, 0])
        assert count == tour_family.bit_count()
        counts.append(count)

    parity = zeta_full([d % 2 for d in counts], len(arcs))
    support = {mask for mask, coefficient in enumerate(parity) if coefficient}
    assert support == set(tours) and all(t.bit_count() == n for t in support)
    check_completion_ideal(n, graphs, tours, parity)

    # Distinct successor permutations cannot differ at one position. Switching
    # just two successors splits a spanning cycle, so two tours require ≥n+3 arcs.
    sparse = [g for g in range(len(graphs)) if g.bit_count() < n+3]
    assert all(counts[g] <= 1 for g in sparse)
    for values in ([int(d == 1) for d in counts], [int(d > 0) for d in counts]):
        other = zeta_full(values, len(arcs))
        assert all(other[g] == parity[g] for g in sparse)
    if n >= 3:
        assert any(d > 1 and g.bit_count() == n+3 for g, d in enumerate(counts))
        cycle = sum(edge[u, (u+1) % n] for u in range(n))
        chord_graph = cycle | edge[0, 2]
        choices = [v for v in range(1, n) if chord_graph & edge[0, v]]
        assert counts[chord_graph] == 1 and choices == [1, 2]
    return len(sparse)


def check(n):
    edges = n*(n-1)
    tours = tuple(tour_masks(n))
    assert len(set(tours)) == len(tours) == factorial(n-1)
    assert all(t.bit_count() == n for t in tours)
    levels = (len(tours)-1).bit_length()+1
    graphs = [sum(1 << i for i, t in enumerate(tours) if g & t == t) for g in range(1 << edges)]
    sparse = check_parity_completion(n, graphs, tours)
    patterns = hash_distribution(tours, edges)
    minima = {}
    # Includes even the subsets of tours that no graph happens to realize.
    for f in range(1 << len(tours)):
        probs = fixed_level_probabilities(f, patterns, levels)
        d = f.bit_count()
        if not d:
            assert not any(probs)
            continue
        k = (d-1).bit_length()+1
        weight = 1 << k
        lower = Fraction(d*(weight-d+1), weight**2)
        assert probs[k-1] >= lower >= Fraction(3, 16)
        if d == 1:
            assert k == 1 and probs[0] == Fraction(1, 2)
        minima[d] = min(minima.get(d, 1), probs[k-1])
        assert sum(probs)/levels >= Fraction(3, 16*levels)  # independent uniform choice of level

    seeds, guaranteed = fixed_seeds(set(graphs), tours, edges, levels)
    batches = [(seed, prefix_filters(seed, tours, edges)) for seed in seeds]
    for graph, family in enumerate(graphs):
        singleton, parity, nonempty = False, False, False
        for seed, filters in batches:
            for k, h in enumerate(filters, start=1):
                d = (family & h).bit_count()
                bit = filtered_parity(graph, tours, seed[:k], edges)
                assert bit == d % 2
                singleton |= d == 1
                parity |= bool(bit)
                nonempty |= d > 0
        # On a multi-witness filtered instance a promise solver may give either
        # answer. The worst and best possible ORs already agree here.
        assert singleton == parity == nonempty == bool(family)
    print(f"n={n}, {len(graphs)} graphs, {len(tours)} rooted tours, {levels} levels")
    print(f"  parity ANF has just the {len(tours)} tour monomials; all {sparse} graphs below n+3 arcs have at most one tour")
    if n >= 3:
        print("  forward chord 0→2 leaves one tour and gives two initial successor choices")
    print("  exact minimum at good level by witness count:", " ".join(f"{d}={p}" for d, p in sorted(minima.items())))
    print(f"  {len(seeds)} fixed trials serve every input (union-bound budget {guaranteed}): {seeds}")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    for n in (2, 3, 4):
        check(n)
