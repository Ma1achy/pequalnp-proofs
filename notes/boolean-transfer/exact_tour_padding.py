#!/usr/bin/env python3
"""Check exact-tour padding on every retained-arc assignment of small graphs.

Read the integer coefficients from a Boolean truth table by Möbius inversion.
Both homogeneous extractions and the final sign are checked over the integers.
All graphs are loopless. The source permits the indicated optional arcs and
sets every other unused coordinate to zero.
"""

from itertools import combinations, permutations
from math import comb


def rooted_path(n, h):
    """Replace root 0 by 0,n,...,n+h-1. The old outgoing arcs leave its end."""
    path = [0, *range(n, n + h)]
    base = [(u, v) for u in range(n) for v in range(n) if u != v]
    visible = [(path[-1] if u == 0 else u, v) for u, v in base]
    forced = list(zip(path, path[1:]))
    optional = [(u, v) for u in range(1, n) for v in path[1:]]
    optional.extend((v, u) for i, v in enumerate(path) for u in path[:i])
    assert len(set(visible + forced + optional)) == len(visible + forced + optional)
    assert len(optional) == h * (n - 1) + h * (h + 1) // 2
    return base, visible, forced, optional


def exact_tour(size, arcs, mask):
    """Recognize the graph itself as one directed spanning cycle."""
    if mask.bit_count() != size:
        return False
    successor = {}
    while mask:
        bit = mask & -mask
        u, v = arcs[bit.bit_length() - 1]
        if u in successor:
            return False
        successor[u] = v
        mask ^= bit
    vertex = 0
    visited = set()
    while vertex not in visited:
        visited.add(vertex)
        vertex = successor[vertex]
    return vertex == 0 and len(visited) == size


def coefficients(values):
    """Transform Boolean values into canonical integer multilinear coefficients."""
    step = 1
    while step < len(values):
        for low in range(0, len(values), 2 * step):
            for i in range(low, low + step):
                values[i + step] -= values[i]
        step *= 2


def target_tours(n, base):
    index = {arc: 1 << i for i, arc in enumerate(base)}
    tours = set()
    for middle in permutations(range(1, n)):
        cycle = [0, *middle, 0]
        tours.add(sum(index[u, v] for u, v in zip(cycle, cycle[1:])))
    return tours


def check(n, h, base, visible, forced, optional):
    retained = visible + forced + list(optional)
    k = len(optional)
    visible_count = len(visible)
    visible_mask = (1 << visible_count) - 1
    forced_mask = ((1 << h) - 1) << visible_count
    optional_mask = ((1 << k) - 1) << (visible_count + h)
    size = n + h

    base_values = [exact_tour(n, base, mask) for mask in range(1 << len(base))]
    values = []
    for mask in range(1 << len(retained)):
        actual = exact_tour(size, retained, mask)
        factored = (base_values[mask & visible_mask]
                    and mask & forced_mask == forced_mask
                    and mask & optional_mask == 0)
        assert actual == factored, (n, h, optional, mask, "Boolean factorization")
        values.append(int(actual))
    coefficients(values)

    degree = size + k
    result = {}
    for mask, coeff in enumerate(values):
        target = mask & visible_mask
        if coeff and mask.bit_count() == degree and target.bit_count() == n:
            result[target] = result.get(target, 0) + coeff
    expected = {mask: (-1) ** k for mask in target_tours(n, base)}
    assert result == expected, (n, h, optional, "two layers")
    # Query the same homogeneous layer with exactly b optional arcs set to
    # one, holding all forced arcs at one. Keep every visible output degree.
    oracle_sum = {}
    for b in range(k + 1):
        enabled = ((1 << b) - 1) << (visible_count + h)
        weight = (-1) ** b * comb(k, b)
        for mask, coeff in enumerate(values):
            if coeff and mask.bit_count() == degree and not mask & (optional_mask ^ enabled):
                target = mask & visible_mask
                oracle_sum[target] = oracle_sum.get(target, 0) + weight * coeff
    oracle_sum = {mask: value for mask, value in oracle_sum.items() if value}
    assert oracle_sum == {mask: 1 for mask in expected}, (n, h, optional, "oracle sum")
    return len(values)


def run():
    cases = assignments = 0
    for n, h in [(2, 0), (2, 1), (2, 2), (3, 1), (3, 2), (4, 1)]:
        base, visible, forced, available = rooted_path(n, h)
        if n + h <= 4:
            # Every choice of allowable padding arcs, including zero and capacity.
            choices = (subset for k in range(len(available) + 1)
                       for subset in combinations(available, k))
        else:
            # Exercise both families of arcs and the maximum possible excess.
            choices = [(), available[:1], available[-1:], available]
        for optional in choices:
            assignments += check(n, h, base, visible, forced, optional)
            cases += 1
    print(f"Exact-tour factorization, signed two-layer projection, and oracle sum passed "
          f"for {cases} graphs and {assignments} Boolean assignments.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with Python assertions enabled")
    run()
