#!/usr/bin/env python3
"""A directed Hamiltonian-cycle kernel for simple loopless graphs, parameter q=e−n.

The input is a nonempty tuple of n adjacency bitmasks. The output is a graph
with n' <= q, e' <= 2q, or a constant Decision with precisely 0 or 1 tours.
Tour counts treat cyclic rotations as identical and distinguish directions.
Running the file checks the kernel against an independent permutation oracle.
"""

from enum import Enum
from itertools import permutations
from random import Random


class Decision(Enum):
    NO = 0
    YES = 1


def surplus(rows):
    return sum(row.bit_count() for row in rows) - len(rows)


def forced_cycle_length(successor):
    """Return the length of any cycle in the partially defined successor map."""
    seen = set()
    for start in range(len(successor)):
        v = start
        path_index = {}
        while successor[v] is not None and v not in seen:
            seen.add(v)
            path_index[v] = len(path_index)
            v = successor[v]
        if v in path_index:
            return len(path_index) - path_index[v]
    return 0


def contract(rows, u, v):
    """Fuse the sole outgoing arc u→v when n≥3; keep u's label before renumbering.

    In every tour, u is immediately followed by v. Incoming arcs to v other
    than u→v and the arc v→u cannot occur. After contracting, the merged
    vertex takes its incoming arcs from u and outgoing arcs from v. Replacing
    it by (u,v) is an inverse on cyclic tours. No parallel arcs are created.
    Exactly indegree(v) + [v→u] arcs and one vertex disappear.
    """
    if len(rows) < 3 or rows[u] != 1 << v or u == v:
        raise ValueError("expected a sole outgoing arc in a graph on at least three vertices")
    keep = [i for i in range(len(rows)) if i != v]
    merged = []
    for tail in keep:
        outgoing = rows[v] if tail == u else rows[tail]
        merged.append(sum(1 << j for j, head in enumerate(keep)
                          if head != tail and outgoing & (1 << head)))
    return tuple(merged)


def kernel(instance):
    """Return an idempotent, tour-count-preserving reduction in polynomial time.

    A proper forced cycle precludes a spanning tour. A spanning forced cycle
    gives exactly one. Each contraction lowers vertex count and cannot raise
    surplus, since indegree(v)≥1. On a residual graph every outdegree is ≥2,
    so n'≤e'−n'≤q and e'=(e'−n')+n'≤2q. The constant outputs also handle q<0.
    """
    if isinstance(instance, Decision):
        return instance
    rows = tuple(instance)
    if not rows or any(row < 0 or row >> len(rows) or row & (1 << i)
                       for i, row in enumerate(rows)):
        raise ValueError("expected nonempty loopless adjacency rows")
    while True:
        n = len(rows)
        heads = 0
        for row in rows:
            heads |= row
        if 0 in rows or heads != (1 << n)-1:
            return Decision.NO
        if n == 2:
            return Decision.YES  # Both opposite arcs exist.
        successor = [row.bit_length()-1 if row.bit_count() == 1 else None for row in rows]
        length = forced_cycle_length(successor)
        if length:
            return Decision.YES if length == n else Decision.NO
        u = next((u for u, v in enumerate(successor) if v is not None), None)
        if u is None:
            return rows
        rows = contract(rows, u, successor[u])


def _tours(rows):
    """Independent oracle: root each cyclic ordering at vertex zero."""
    n = len(rows)
    tours = set()
    for tail in permutations(range(1, n)):
        order = (0, *tail)
        if all(rows[v] & (1 << order[(i+1) % n]) for i, v in enumerate(order)):
            tours.add(order)
    return tours


def _expand(tour, keep, u, v):
    order = []
    for j in tour:
        order.append(keep[j])
        if keep[j] == u:
            order.append(v)
    start = order.index(0)
    return tuple(order[start:] + order[:start])


def _forced_path_quotient(rows):
    """Independent one-pass construction used by the checker.

    Every sole-outgoing arc is compulsory. Unless these arcs collide or form
    a cycle, they partition the vertices into paths (including singletons).
    Only a path end can send a tour arc to another path's start.
    """
    if 0 in rows:
        return (), Decision.NO
    successor = [row.bit_length()-1 if row.bit_count() == 1 else None for row in rows]
    targets = [v for v in successor if v is not None]
    if len(set(targets)) != len(targets):
        return (), Decision.NO
    length = forced_cycle_length(successor)
    if length:
        return (), Decision.YES if length == len(rows) else Decision.NO
    starts = sorted(set(range(len(rows))) - set(targets))
    paths = []
    for v in starts:
        path = []
        while v is not None:
            path.append(v)
            v = successor[v]
        paths.append(path)
    if len(paths) == 1:
        return (), Decision(bool(rows[paths[0][-1]] & (1 << starts[0])))
    quotient = tuple(sum(1 << j for j, start in enumerate(starts)
                         if i != j and rows[path[-1]] & (1 << start))
                     for i, path in enumerate(paths))
    return paths, quotient


def _check(rows):
    expected = _tours(rows)
    result = kernel(rows)
    assert kernel(result) == result
    if isinstance(result, Decision):
        assert result.value == len(expected)
    else:
        assert len(_tours(result)) == len(expected)
        assert all(row.bit_count() >= 2 for row in result)
        assert surplus(result) <= surplus(rows)
        assert len(result) <= surplus(rows)
        assert sum(row.bit_count() for row in result) <= 2*surplus(rows)
    paths, quotient = _forced_path_quotient(rows)
    if isinstance(quotient, Decision):
        assert quotient.value == len(expected)
    else:
        assert len(quotient) <= surplus(rows)
        assert sum(row.bit_count() for row in quotient) <= 2*surplus(rows)
        assert surplus(quotient) <= surplus(rows)
        expanded = set()
        for tour in _tours(quotient):
            order = [v for i in tour for v in paths[i]]
            start = order.index(0)
            expanded.add(tuple(order[start:] + order[:start]))
        assert expanded == expected
    # Test every eligible contraction, even when the chosen kernel order would
    # stop earlier, and compare actual cyclic orderings under the inverse map.
    checks = 0
    for u, row in enumerate(rows):
        if len(rows) < 3 or row.bit_count() != 1:
            continue
        v = row.bit_length()-1
        smaller = contract(rows, u, v)
        loss = sum(bool(r & (1 << v)) for r in rows)-1 + bool(rows[v] & (1 << u))
        assert surplus(rows)-surplus(smaller) == loss >= 0
        keep = [j for j in range(len(rows)) if j != v]
        smaller_tours = _tours(smaller)
        assert len(smaller_tours) == len(expected)
        assert {_expand(tour, keep, u, v) for tour in smaller_tours} == expected
        checks += 1
    return checks


def _rows(n, arcs):
    rows = [0]*n
    for u, v in arcs:
        rows[u] |= 1 << v
    return tuple(rows)


def _larger_cases():
    rng = Random(60973)
    for n in range(5, 9):
        arcs = [(u, v) for u in range(n) for v in range(n) if u != v]
        cycle = [(u, (u+1) % n) for u in range(n)]
        yield _rows(n, cycle)
        sharp = _rows(n, cycle + [(u, (u+2) % n) for u in range(n)])
        assert kernel(sharp) == sharp and len(sharp) == surplus(sharp)
        yield sharp
        # Replace root 0 by forced path 0→n. Contraction recovers the sharp core.
        padded = _rows(n+1, [(0, n)] + [(n if u == 0 else u, v)
                            for u, v in arcs if sharp[u] & (1 << v)])
        assert kernel(padded) == sharp
        yield padded
        for p in (0.12, 0.3, 0.7):
            for planted in (False, True):
                for _ in range(2):
                    edges = [a for a in arcs if rng.random() < p]
                    yield _rows(n, edges + (cycle if planted else []))


def _check_templates():
    """Verify the x_(u,v) factor with all template arc labels independent."""
    def counts(n, arcs):
        return [len(_tours(_rows(n, (a for i, a in enumerate(arcs) if mask >> i & 1))))
                for mask in range(1 << len(arcs))]

    def coefficients(table):
        # Subset Möbius transform over Z; reduction modulo 2 also gives the ANF.
        values = list(map(int, table))
        bit = 1
        while bit < len(values):
            for mask in range(len(values)):
                if mask & bit:
                    values[mask] -= values[mask ^ bit]
            bit <<= 1
        return values

    templates = []
    for n, u, v in ((3, 2, 0), (4, 0, 1)):
        arcs = [(a, b) for a in range(n) for b in range(n)
                if a != b and (a != u or b == v)]
        templates.append((n, u, v, arcs))
    arcs = [(0, 4), (4, 0), (2, 4)] + [
        (4 if a == 0 else a, (a+d) % 4) for a in range(4) for d in (1, 2)]
    templates.append((5, 0, 4, arcs))
    checks = 0
    for n, u, v, arcs in templates:
        keep = [a for a in range(n) if a != v]
        forced = 1 << arcs.index((u, v))
        # A reduced edge retains the original variable by its index in arcs.
        labels = [i for i, (a, b) in enumerate(arcs) if a != u and b != v and (a, b) != (v, u)]
        reduced = [(keep.index(u if arcs[i][0] == v else arcs[i][0]), keep.index(arcs[i][1]))
                   for i in labels]
        assert _rows(n-1, reduced) == contract(_rows(n, arcs), u, v)
        source, target = counts(n, arcs), counts(n-1, reduced)
        for left, right in ((source, target), (list(map(bool, source)), list(map(bool, target)))):
            for mask, value in enumerate(left):
                projected = sum(1 << j for j, i in enumerate(labels) if mask & (1 << i))
                assert value == bool(mask & forced) * right[projected]
            lifted = {forced | sum(1 << i for j, i in enumerate(labels) if subset & (1 << j)): c
                      for subset, c in enumerate(coefficients(right))}
            assert all(c == lifted.get(mask, 0) for mask, c in enumerate(coefficients(left)))
        checks += len(source)
    print(f"{len(templates)} contraction templates: {checks} subgraphs,"
          f" {2*checks} decision/count coefficient identities")


def main():
    if not __debug__:
        raise RuntimeError("run with Python assertions enabled")
    assert kernel((0,)) == Decision.NO
    assert kernel((2, 1)) == Decision.YES
    proper = _rows(4, [(0, 1), (1, 0), (2, 0), (2, 3), (3, 2), (3, 0)])
    assert forced_cycle_length([1, 0, None, None]) == 2 and kernel(proper) == Decision.NO
    assert kernel(_rows(3, [(0, 1), (1, 2), (2, 1)])) == Decision.NO  # no incoming at 0
    assert kernel(_rows(3, [(0, 1), (0, 2), (1, 0)])) == Decision.NO  # no outgoing at 2
    for n in range(1, 5):
        arcs = [(u, v) for u in range(n) for v in range(n) if u != v]
        checked = 0
        for mask in range(1 << len(arcs)):
            rows = _rows(n, (arc for i, arc in enumerate(arcs) if mask & (1 << i)))
            checked += _check(rows)
        print(f"n={n}: {1 << len(arcs)} graphs, {checked} individual contraction bijections")
    larger = list(_larger_cases())
    checked = sum(_check(rows) for rows in larger)
    print(f"n=5..9: {len(larger)} deterministic graphs, {checked} individual contraction bijections")
    _check_templates()


if __name__ == "__main__":
    main()
