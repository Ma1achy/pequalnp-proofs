#!/usr/bin/env python3
"""Count labelled Hamiltonicity ANF cores by size and arc surplus.

Run with Python 3.10+. Only the standard library is needed. The core counter
multiplies the Boolean disjunction of tour monomials in the squarefree F₂ ring.
A separate bit-parallel path recurrence builds the actual decision truth table
and a subset Möbius transform recovers every coefficient through five vertices.
"""

from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import comb, factorial


def _arc_bits(n):
    return {(i, j): 1 << a for a, (i, j) in enumerate(
        (i, j) for i in range(n) for j in range(n) if i != j)}


def _tour_masks(n, arc):
    for tail in permutations(range(1, n)):
        order = (0, *tail)
        yield sum(arc[order[i-1], order[i]] for i in range(n))


def core_counts(n, surplus_limit):
    """Return c_(n,k), retaining only unions of at most n+surplus_limit arcs."""
    arc = _arc_bits(n)
    max_degree = n + surplus_limit
    support = set()
    for tour in _tour_masks(n, arc):
        # f OR t = f + t + f*t. Products use union, additions toggle parity.
        # Larger unions can never contribute back to a lower-degree monomial.
        change = {tour}
        for old in support:
            union = old | tour
            if union.bit_count() <= max_degree:
                if union in change:
                    change.remove(union)
                else:
                    change.add(union)
        support.symmetric_difference_update(change)
    row_masks = [sum(arc[i, j] for j in range(n) if i != j) for i in range(n)]
    col_masks = [sum(arc[i, j] for i in range(n) if i != j) for j in range(n)]
    neighborhoods = row_masks + col_masks
    return Counter(mask.bit_count()-n for mask in support
                   if all((mask & incident).bit_count() >= 2 for incident in neighborhoods))


def diagonal_count(p):
    """Independently check c_(p,p) by marking one particular directed tour.

    A core here has two arcs in and out at each vertex. Removing its marked
    tour leaves a permutation, with no loop or marked arc. Directly take the
    parity of all positive edge assignments in each template. Weight by the
    reciprocal of the number of tours to remove the mark.
    """
    arc = _arc_bits(p)
    tours = tuple(_tour_masks(p, arc))
    base = sum(arc[i, (i+1) % p] for i in range(p))
    weighted = Fraction(0)
    for successor in permutations(range(p)):
        if any(v == u or v == (u+1) % p for u, v in enumerate(successor)):
            continue
        template = base | sum(arc[i, j] for i, j in enumerate(successor))
        containing = [t for t in tours if t & template == t]
        edges = [e for e in arc.values() if e & template]
        compact = [sum(1 << j for j, e in enumerate(edges) if t & e) for t in containing]
        positives = sum(any(mask & t == t for t in compact) for mask in range(1 << len(edges)))
        if positives % 2:
            weighted += Fraction(1, len(containing))
    return factorial(p-1)*weighted


def decision_layers(n):
    """Evaluate all 2^(n(n−1)) inputs by subset/endpoint DP, then invert."""
    arc = _arc_bits(n)
    bits = len(arc)
    size = 1 << bits
    universe = (1 << size)-1
    high_halves = {}
    for edge in arc.values():
        # Bit j of this integer is the arc's Boolean value on graph mask j.
        stride = edge
        pattern = ((1 << stride)-1) << stride
        width = 2*stride
        while width < size:
            pattern |= pattern << width
            width *= 2
        high_halves[edge] = pattern

    full = (1 << n)-1
    paths = {(1, 0): universe}
    for visited in range(1, full+1, 2):  # root zero belongs to each visited set
        for last in range(1, n):
            if not visited & (1 << last):
                continue
            prior = visited ^ (1 << last)
            truth = 0
            for prev in range(n):
                if prior & (1 << prev):
                    truth |= paths.get((prior, prev), 0) & high_halves[arc[prev, last]]
            paths[visited, last] = truth

    truth = 0
    for last in range(1, n):
        truth |= paths[full, last] & high_halves[arc[last, 0]]
    for edge, high in high_halves.items():
        # On upper-half assignments XOR the corresponding lower-half value.
        truth ^= (truth << edge) & high

    layers = Counter()
    for byte_index, byte in enumerate(truth.to_bytes((size+7)//8, "little")):
        while byte:
            bit = byte & -byte
            mask = 8*byte_index + bit.bit_length()-1
            layers[mask.bit_count()-n] += 1
            byte ^= bit
    return layers


def stretched_count(n, k, cores):
    if k == 0:
        return factorial(n-1)
    return sum((factorial(n)//factorial(p)) * comb(n-1, p-1) * cores[p][k]
               for p in range(2, min(n, k)+1))


def main():
    if not __debug__:
        raise RuntimeError("run with Python assertions enabled")
    # For n<=5 all surpluses are affordable, enabling full truth-table checks.
    cores = {p: core_counts(p, p*(p-1)-p if p <= 5 else 6) for p in range(2, 7)}
    expected = {(3, 3): 1, (4, 4): 3, (4, 5): 8, (5, 5): 96,
                (4, 6): 12, (5, 6): 480, (6, 6): 1920}
    assert all(cores[p][k] == expected.get((p, k), 0)
               for p in range(2, 7) for k in range(1, 7))
    assert all(diagonal_count(p) == cores[p][p] for p in range(3, 7))
    for k in range(1, 7):
        print(f"k={k}: " + ", ".join(f"c_{{{p},{k}}}={cores[p][k]}" for p in range(2, 7)))
    for n in range(2, 6):
        layers = decision_layers(n)
        size = n*(n-1)
        for k in range(-n, size-n+1):
            assert layers[k] == stretched_count(n, k, cores), (n, k, layers[k])
        assert sum(layers.values()) == {2: 1, 3: 3, 4: 53, 5: 14519}[n]
        print(f"m={n}: {1 << size} graphs, {size+1} layers, {sum(layers.values())} monomials")


if __name__ == "__main__":
    main()
