#!/usr/bin/env python3
"""Project hc_N to hc_m with all m(m−1) variables on prescribed disjoint arcs.

City v has an anchor and directed rings O_v[w], I_v[u] indexed respectively
by other heads and tails. Its outgoing ring is entered only from its anchor.
A full tour must traverse the whole ring in order before taking its unique
chosen variable arc O_v[w]→I_w[v]. Its incoming ring can exit only into its
anchor, once; hence it too is entered once and traversed in full. A tour on
the router thus contracts to a single cycle of cities. Conversely the chosen
incoming slot determines the first incoming port, and the chosen outgoing
slot determines the last outgoing port. Each city cycle has exactly one lift.
Tags on its lift are exactly the arcs in the original cycle.

The router uses 2m(m−1)+m vertices. For any larger N replace one anchor by a
forced path. Relabelling all ports then realizes any ordered list of prescribed
pairwise vertex-disjoint variable slots. All untagged entries are 0 or 1.
Coefficient equality holds over the nonnegative integers, hence in any field.
For two distinct surviving tours, the union of their arc sets carries each
tag in the union of the two target tours exactly once. If either source
tour fails to survive, it contains a constant-zero arc. Their union still
contains this arc, so the corresponding squarefree generator maps to zero.
Every Boolean-ideal generator x_e²−x_e with e outside the marked slots
also maps to zero, since its image is evaluated at a constant bit.
Run with Python 3. Only the standard library and sibling verifiers are needed.
"""
from collections import Counter
from dataclasses import dataclass
from itertools import combinations, permutations
from random import Random

from boolean_jet import tour_masks
from unique_tour_gadget import hamiltonian_successors


@dataclass(frozen=True)
class Projection:
    rows: tuple         # permitted source arcs, including the variable slots
    target_arcs: tuple  # target label assigned to each slot
    slots: tuple        # source (tail, head) coordinates in target-arc order

    def specialize(self, target_mask):
        """Set a slot to its bit in the target graph, preserving all constant entries."""
        if not 0 <= target_mask < 1 << len(self.slots):
            raise ValueError("target graph mask out of range")
        rows = list(self.rows)
        for bit, (u, v) in enumerate(self.slots):
            if not target_mask >> bit & 1:
                rows[u] &= ~(1 << v)
        return tuple(rows)

    def image(self, powers):
        """Image exponent tuple, or None for a monomial killed by a zero slot."""
        if any(k and not self.rows[u] & (1 << v) for (u, v), k in powers.items()):
            return None
        return tuple(powers.get(slot, 0) for slot in self.slots)

    def squarefree_image(self, support):
        powers = self.image(dict.fromkeys(support, 1))
        return None if powers is None else sum(e << i for i, e in enumerate(powers))

    def substituted_polynomial(self):
        """Count projected tour monomials with their integer coefficients."""
        return Counter(self.squarefree_image(enumerate(succ))
                       for succ in hamiltonian_successors(self.rows))


def router(m, N=None, matching=None):
    if m < 2:
        raise ValueError("loopless target needs at least two vertices")
    arcs = tuple((u, v) for u in range(m) for v in range(m) if u != v)
    d = len(arcs)
    size = 2*d + m
    if N is None:
        N = size
    if N < size:
        raise ValueError(f"router requires at least {size} host vertices")
    if matching is None:
        matching = tuple((i, d+i) for i in range(d))
    matching = tuple(matching)
    endpoints = [v for pair in matching for v in pair]
    if (len(matching) != d or any(len(pair) != 2 for pair in matching)
            or len(set(endpoints)) != 2*d or any(not 0 <= v < N for v in endpoints)):
        raise ValueError("slots must consist of one vertex-disjoint host arc per target variable")
    occupied = set(endpoints)
    relabel = [u for u, _ in matching] + [v for _, v in matching] + [v for v in range(N) if v not in occupied]
    rows = [0]*N

    def edge(u, v):
        u, v = relabel[u], relabel[v]
        assert u != v and not rows[u] & (1 << v)
        rows[u] |= 1 << v

    def ring(ports):
        if len(ports) >= 2:
            for i, u in enumerate(ports):
                edge(u, ports[(i+1) % len(ports)])

    index = {arc: i for i, arc in enumerate(arcs)}
    for v in range(m):
        anchor = 2*d+v
        path = [anchor, *range(size, N)] if v == 0 else [anchor]
        for u, w in zip(path, path[1:]):
            edge(u, w)
        outgoing = [index[v, w] for w in range(m) if v != w]
        incoming = [d+index[u, v] for u in range(m) if u != v]
        ring(outgoing)
        ring(incoming)
        for port in outgoing:
            edge(path[-1], port)
        for port in incoming:
            edge(port, anchor)
    for i in range(d):
        edge(i, d+i)
    assert sum(row.bit_count() for row in rows) == (5 if m >= 3 else 3)*d + N-size
    return Projection(tuple(rows), arcs, matching)


def matching_examples():
    """Check the necessary matching bound inside a contributing source cycle.

    If a projected term uses m variable slots on a source tour, its m arcs
    contain a vertex-disjoint subset of size at least floor(m/2). In a proper
    subset of cycle arcs, take alternating edges on each path. For the whole
    cycle take alternating edges up to floor(m/2). This necessity does not
    require every variable in a projection to have a disjoint slot.
    """
    checked = 0
    for n in range(2, 10):
        cycle = [(i, (i+1) % n) for i in range(n)]
        matchings = [s for r in range(n//2+1) for s in combinations(range(n), r)
                     if len({v for i in s for v in cycle[i]}) == 2*r]
        match_masks = [(sum(1 << i for i in s), len(s)) for s in matchings]
        for chosen in range(1 << n):
            largest = max(size for mask, size in match_masks if not mask & ~chosen)
            k = chosen.bit_count()
            assert largest >= (k//2 if k == n else (k+1)//2)
            checked += 1
        assert max(len(s) for s in matchings) == n//2
    return checked


def check_generators(projected, target, rng):
    survivors = []
    for succ in hamiltonian_successors(projected.rows):
        support = frozenset(enumerate(succ))
        label = sum(1 << i for i, (u, v) in enumerate(projected.slots) if succ[u] == v)
        assert projected.squarefree_image(support) == label
        survivors.append((support, label))
    assert Counter(label for _, label in survivors) == target
    assert projected.substituted_polynomial() == target
    images = Counter()
    for (s, a), (t, b) in combinations(survivors, 2):
        actual = projected.squarefree_image(s | t)
        assert actual == a | b and a != b
        images[actual] += 1
    assert images == Counter(a | b for a, b in combinations(target, 2))

    n = len(projected.rows)
    bad = []
    if n == 6:
        orders = permutations(range(1, n))
    else:
        orders = [rng.sample(range(1, n), n-1) for _ in range(8)]
    for tail in orders:
        order = (0, *tail)
        cycle = frozenset(zip(order, order[1:] + order[:1]))
        if any(not projected.rows[u] & (1 << v) for u, v in cycle):
            assert projected.squarefree_image(cycle) is None
            bad.append(cycle)
    dead = 0
    for s in bad:
        for t, _ in survivors:
            assert projected.squarefree_image(s | t) is None
            dead += 1
    for s, t in combinations(bad, 2):
        assert projected.squarefree_image(s | t) is None
        dead += 1

    # Guard coordinates have bit images; keep an unguarded slot squared in
    # the test monomial to check this is only a partial Boolean reduction.
    slots = set(projected.slots)
    candidates = [(u, v) for u in range(n) for v in range(n) if (u, v) not in slots]
    guard_checks = 0
    for _ in range(4):
        guard = set(rng.sample(candidates, max(1, len(candidates)//4)))
        assert guard.isdisjoint(slots)
        for arc in guard:
            before = {projected.slots[0]: 2, arc: 3}
            after = {projected.slots[0]: 2, arc: 1}
            assert projected.image(before) == projected.image(after)
            assert projected.image({arc: 2}) == projected.image({arc: 1})
            guard_checks += 1
    return sum(images.values()), dead, guard_checks


def check(m):
    rng = Random(8743+m)
    d = m*(m-1)
    base = 2*d + m
    target = Counter({tour: 1 for tour in tour_masks(m)})
    assignments = pairs = dead = guarded = 0
    for padding in (0, 3):
        N = base+padding
        labels = list(range(N))
        rng.shuffle(labels)
        slots = tuple((labels[i], labels[d+i]) for i in range(d))
        projected = router(m, N, slots)
        assert len(projected.rows) == N and projected.slots == slots
        assert len({v for uv in projected.slots for v in uv}) == 2*d
        pair_count, dead_count, guard_count = check_generators(projected, target, rng)
        pairs += pair_count
        dead += dead_count
        guarded += guard_count
        # Check the specialised adjacency rows as well as the symbolic identity.
        if m <= 3:
            masks = range(1 << d)
        else:
            masks = [0, (1 << d)-1, *sorted(target)] + [rng.getrandbits(d) for _ in range(12)]
        for graph in masks:
            expected = sum(graph & tour == tour for tour in target)
            assert sum(1 for _ in hamiltonian_successors(projected.specialize(graph))) == expected
            assignments += 1
    print(f"m={m}: {d} prescribed slots, host sizes {base} and {base+3}, "
          f"{len(target)} degree-{m} monomials of coefficient one, {assignments} graph specializations, "
          f"{pairs} surviving pair images, {dead} killed pair images, {guarded} guarded-coordinate checks")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    for m in range(2, 6):
        check(m)
    print(f"checked the necessary matching bound on {matching_examples()} subsets of cycle arcs")
