"""Exact order search for the touched-row boundary rank in syndrome.py."""

from dataclasses import dataclass
from itertools import combinations, permutations
from pathlib import Path
from random import Random
import sys


@dataclass(frozen=True)
class Result:
    width: int
    order: tuple
    prefix_ranks: tuple
    subsets: int
    predecessor_checks: int
    row_xors: int


def _insert(basis, row):
    xors = 0
    while row:
        pivot = row.bit_length() - 1
        if not basis[pivot]:
            basis[pivot] = row
            return 1, xors
        row ^= basis[pivot]
        xors += 1
    return 0, xors


def _group_scopes(flats, n):
    groups = {}
    for flat in flats:
        rows = []
        scope = 0
        for augmented in flat:
            if not isinstance(augmented, int) or augmented < 0 or augmented.bit_length() > n + 1:
                raise ValueError("row outside the specified variable universe")
            row = augmented >> 1
            rows.append(row)
            scope |= row
        if scope:
            groups.setdefault(scope, []).extend(rows)
    return groups


def _components(groups, n):
    # Each factor's support lies in a single connected component.
    parent = list(range(n))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for scope in groups:
        first = (scope & -scope).bit_length() - 1
        for v in range(first + 1, n):
            if scope >> v & 1:
                parent[find(v)] = find(first)
    vertices = {}
    for v in range(n):
        vertices.setdefault(find(v), []).append(v)
    scopes = {}
    for scope, rows in groups.items():
        root = find((scope & -scope).bit_length() - 1)
        scopes.setdefault(root, []).append((scope, rows))
    return [(part, scopes.get(root, [])) for root, part in vertices.items()]


def _component_order(variables, groups):
    n = len(variables)
    if not groups:
        return Result(0, tuple(variables), tuple(0 for _ in range(n+1)), 0, 0, 0)

    def local(mask):
        return sum(((mask >> v) & 1) << i for i, v in enumerate(variables))

    compressed = []
    xors = 0
    for scope, rows in groups:
        basis = [0] * n
        for row in rows:
            _, count = _insert(basis, local(row))
            xors += count
        compressed.append((local(scope), [row for row in basis if row]))

    length = 1 << n
    full = length - 1
    rank = [0] * length
    width = [0] * length
    last = [0] * length
    checks = 0
    for prefix in range(1, length):
        remaining = full ^ prefix
        possible = remaining.bit_count()
        basis = [0] * n
        current = 0
        for scope, rows in compressed:
            if current == possible:
                break
            if scope & prefix and scope & remaining:
                for row in rows:
                    added, count = _insert(basis, row & remaining)
                    current += added
                    xors += count
                    if current == possible:
                        break
        rank[prefix] = current
        best = n + 1
        candidates = prefix
        while candidates:
            bit = candidates & -candidates
            score = width[prefix ^ bit]
            checks += 1
            if score < best:
                best, last[prefix] = score, bit.bit_length() - 1
            if best <= current:
                break
            candidates ^= bit
        width[prefix] = max(current, best)
    reverse_order = []
    reverse_ranks = []
    mask = full
    while mask:
        reverse_ranks.append(rank[mask])
        variable = last[mask]
        reverse_order.append(variables[variable])
        mask ^= 1 << variable
    return Result(width[full], tuple(reversed(reverse_order)), (0, *reversed(reverse_ranks)),
                  length, checks, xors)


def optimal_order(flats, n):
    """Return an optimal order and cut ranks, using all declared variable IDs."""
    if n < 0:
        raise ValueError("negative variable count")
    order = []
    ranks = [0]
    subsets = predecessor_checks = xors = 0
    for variables, groups in _components(_group_scopes(flats, n), n):
        result = _component_order(variables, groups)
        order.extend(result.order)
        ranks.extend(result.prefix_ranks[1:])
        subsets += result.subsets
        predecessor_checks += result.predecessor_checks
        xors += result.row_xors
    return Result(max(ranks), tuple(order), tuple(ranks), subsets, predecessor_checks, xors)


def reference_ranks(flats, n):
    """Independent cut ranks by enumeration of the span of restricted global rows."""
    ranks = []
    for prefix in range(1 << n):
        span = {0}
        for flat in flats:
            if any((row >> 1) & prefix for row in flat):
                for row in flat:
                    restricted = (row >> 1) & ~prefix
                    span.update([v ^ restricted for v in span])
        ranks.append(len(span).bit_length() - 1)
    return ranks


def path_ranks(ranks, order):
    prefix = 0
    values = [ranks[0]]
    for v in order:
        prefix |= 1 << v
        values.append(ranks[prefix])
    return tuple(values)


def graph_instance(edges):
    return [(1 << (1 + a), 1 << (1 + b)) for a, b in edges]


def exterior_boundaries(edges, n):
    result = []
    for prefix in range(1 << n):
        exterior = set()
        for a, b in edges:
            if (prefix >> a) & 1 and not (prefix >> b) & 1:
                exterior.add(b)
            if (prefix >> b) & 1 and not (prefix >> a) & 1:
                exterior.add(a)
        result.append(len(exterior))
    return result


def check_orders(flats, n, ranks):
    actual = optimal_order(flats, n)
    assert sorted(actual.order) == list(range(n))
    assert path_ranks(ranks, actual.order) == actual.prefix_ranks
    assert max(actual.prefix_ranks) == actual.width
    best = min(max(path_ranks(ranks, order)) for order in permutations(range(n)))
    assert best == actual.width
    return actual


def main():
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from math import factorial
    from syndrome import syndrome_prefixes
    graph_count = graph_orders = graph_cuts = 0
    for n in range(6):
        all_edges = list(combinations(range(n), 2))
        for mask in range(1 << len(all_edges)):
            edges = [e for i, e in enumerate(all_edges) if mask >> i & 1]
            flats = graph_instance(edges)
            ranks = reference_ranks(flats, n)
            assert ranks == exterior_boundaries(edges, n)
            check_orders(flats, n, ranks)
            graph_count += 1
            graph_cuts += len(ranks)
            graph_orders += factorial(n)
    rng = Random(78301)
    affine_orders = affine_cuts = 0
    for i in range(140):
        n = i % 7
        flats = [tuple(rng.randrange(1 << (n+1)) for _ in range(rng.randrange(5)))
                 for _ in range(rng.randrange(9))]
        ranks = reference_ranks(flats, n)
        result = check_orders(flats, n, ranks)
        observed = tuple(len(layer.basis) for layer in syndrome_prefixes(flats, n, result.order))
        assert result.prefix_ranks == observed
        affine_cuts += len(ranks)
        affine_orders += factorial(n)
    print(f"Graphs {graph_count}, cuts {graph_cuts}, exhaustive orders {graph_orders}")
    print(f"Affine inputs 140, cuts {affine_cuts}, exhaustive orders {affine_orders}, seed 78301")
    path = [(i, i+1) for i in range(8)]
    grid = [(i, i+1) for i in range(9) if i % 3 != 2] + [(i, i+3) for i in range(6)]
    rows = [("path9", 9, path, 1), ("cycle9", 9, path + [(8,0)], 2),
            ("star9", 9, [(0,i) for i in range(1,9)], 1),
            ("clique9", 9, list(combinations(range(9), 2)), 8), ("grid3x3", 9, grid, 3),
            ("three_disjoint_edges", 6, [(0,1),(2,3),(4,5)], 1)]
    for name, n, edges, expected in rows:
        flats = graph_instance(edges)
        result = optimal_order(flats, n)
        assert result.width == expected
        print(name, result)


if __name__ == "__main__":
    main()
