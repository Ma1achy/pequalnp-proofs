#!/usr/bin/env python3
"""Check affine-guard cancellation and degree isolation for the two-ring router.

H has one column per ordered host arc. A full-rank column basis P, disjoint
from all outgoing-port → incoming-port coordinates, may include arcs of
either constant value. Keep the router's constants and variable slots; on a
pivot add a linear form determined by H_P F = H_slots over F₂. Each affine
guard then becomes its scalar value at the original baseline. Its Boolean
equation L²−L vanishes even when L's scalar value is one.

Every spanning cycle must exit each outgoing port ring and enter each incoming
port ring. The same obligations apply to any union of spanning cycles.
All cut-crossing arcs have zero baseline. Thus a nonzero product term pays
at least m linear factors. At degree m every factor must pay for one exit AND
one entry. The only eligible doubly crossing arcs are the original marked
slots, because no pivot goes from an outgoing port to an incoming port. Every
other support arc uses its baseline one. The surviving tours at that degree
are exactly the original ones. Distinct original tours require more than m
distinct slots in their union, so the squarefree union generator of any two
different host tours has no term in degrees <=m. Arcs whose complete affine
weight is zero kill the entire product, including every union containing it.
"""

from collections import Counter
from itertools import combinations, permutations, product
from random import Random

from boolean_jet import tour_masks
from unique_tour_gadget import hamiltonian_successors
from weighted_slots import router


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def xor_all(values):
    result = 0
    for value in values:
        result ^= value
    return result


def sample_matrix(size, slots, pivots, wanted, rng):
    """Dense rows, nontrivial invertible pivot minor, and two dependent rows."""
    r = len(pivots)
    minor = [1 << i for i in range(r)]
    for _ in range(4*r):
        if r >= 2:
            i, j = rng.sample(range(r), 2)
            minor[i] ^= minor[j]
    rng.shuffle(minor)
    controlled = sum(1 << e for e in (*pivots, *slots))
    rows = []
    for row in minor:
        rhs = xor_all(wanted[i] for i in indices(row))
        dense = rng.getrandbits(size*size) & ~controlled
        rows.append(dense | sum(1 << pivots[i] for i in indices(row))
                    | sum(1 << slots[i] for i in indices(rhs)))
    rows.extend([xor_all(rows), rows[0]])
    return rows, [rng.randrange(2) for _ in rows]


def project(m, rows, offsets, pivots):
    base = router(m)
    n = len(base.rows)
    slots = tuple(n*u+v for u, v in base.slots)
    assert set(slots).isdisjoint(pivots) and len(set(pivots)) == len(pivots)
    # Each right-hand side is itself a packed row of m(m−1) coefficients.
    system = [[sum(((h >> col) & 1) << i for i, col in enumerate(pivots)),
               sum(((h >> col) & 1) << i for i, col in enumerate(slots))] for h in rows]
    for i in range(len(pivots)):
        pivot = next((j for j in range(i, len(system)) if system[j][0] >> i & 1), None)
        if pivot is None:
            raise ValueError("dependent pivot columns")
        system[i], system[pivot] = system[pivot], system[i]
        for j in range(len(system)):
            if j != i and system[j][0] >> i & 1:
                system[j][0] ^= system[i][0]
                system[j][1] ^= system[i][1]
    if any(a or b for a, b in system[len(pivots):]):
        raise ValueError("prescribed slots are not canceled by this pivot basis")
    linear = [0]*(n*n)
    for i, col in enumerate(slots):
        linear[col] = 1 << i
    for i, col in enumerate(pivots):
        linear[col] = system[i][1]
    baseline = [int(bool(base.rows[u] & (1 << v))) for u in range(n) for v in range(n)]
    for col in slots:
        baseline[col] = 0
    guard_constants = []
    for h, b in zip(rows, offsets, strict=True):
        assert xor_all(linear[j] for j in indices(h)) == 0
        guard_constants.append(b ^ xor_all(baseline[j] for j in indices(h)))
    weights = list(zip(baseline, linear))
    return base, weights, guard_constants


def natural_product(support, weights, cutoff):
    """Direct term expansion with integer multiplicities; repeated target variables remain powers."""
    terms = Counter({(): 1})
    for e in sorted(support):
        c, linear = weights[e]
        result = terms.copy() if c else Counter()
        for term, count in terms.items():
            if len(term) < cutoff:
                for i in indices(linear):
                    result[tuple(sorted((*term, i)))] += count
        terms = result
        if not terms:
            break
    return terms


def parity(terms):
    return {monomial for monomial, multiplicity in terms.items() if multiplicity % 2}


def support_rows(n, weights):
    return tuple(sum(1 << v for v in range(n) if any(weights[u*n+v])) for u in range(n))


def path_dp(n, weights, cutoff):
    """Rooted subset/endpoint recurrence over the truncated formal polynomial ring."""
    rows = support_rows(n, weights)

    def multiply(terms, edge):
        c, linear = weights[edge]
        result = set(terms) if c else set()
        for i in indices(linear):
            for term in terms:
                if len(term) < cutoff:
                    result.symmetric_difference_update((tuple(sorted((*term, i))),))
        return result

    paths = {(1, 0): {()}}
    for _ in range(1, n):
        following = {}
        for (visited, u), terms in paths.items():
            for v in indices(rows[u] & ~visited):
                image = multiply(terms, n*u+v)
                if image:
                    key = visited | (1 << v), v
                    following.setdefault(key, set()).symmetric_difference_update(image)
        paths = {key: val for key, val in following.items() if val}
    result = set()
    for (_, u), terms in paths.items():
        result ^= multiply(terms, n*u)
    return result


def examples(m, seed):
    rng = Random(seed)
    base = router(m)
    n, d = len(base.rows), len(base.slots)
    slots = tuple(n*u+v for u, v in base.slots)
    # Swap anchors 0 and 1 along one known original tour. Its four new arcs
    # are I→anchor or anchor→O, outside the forbidden O→I rectangle.
    original = next(hamiltonian_successors(base.rows))
    c0, c1 = 2*d, 2*d+1
    swapped = [(original.index(c0), c1), (c1, original[c0]),
               (original.index(c1), c0), (c0, original[c1])]
    added = tuple(n*u+v for u, v in swapped)
    ones = (n*c0+original[c0], n*c1+original[c1])
    pivots = added + ones
    assert len(set(pivots)) == 6
    assert all(not (col//n < d and d <= col % n < 2*d) for col in pivots)
    assert all(not (base.rows[e//n] >> (e % n) & 1) for e in added)
    assert all(base.rows[e//n] >> (e % n) & 1 for e in ones)
    # Repeated binomials on distinct edges force formal F₂ cancellation:
    # (x₀+x₁)² has no mixed x₀x₁ term.
    wanted = [3, 3] + [rng.randrange(1, 1 << d) for _ in range(2)] + [3, 3]
    H, b = sample_matrix(n, slots, pivots, wanted, rng)
    _, weights, constants = project(m, H, b, pivots)
    assert [weights[e][1] for e in pivots] == wanted
    assert all(weights[e][0] == 1 for e in ones)
    b[-1] ^= constants[-1] ^ constants[0] ^ 1  # duplicate row, opposite scalar value
    _, weights, constants = project(m, H, b, pivots)
    assert set(constants) == {0, 1}

    rows = support_rows(n, weights)
    cycles = [frozenset(n*u+v for u, v in enumerate(succ)) for succ in hamiltonian_successors(rows)]
    expected = {tuple(indices(t)) for t in tour_masks(m)}
    low = set()
    spurious = cancellations = canonical = 0
    for cycle in cycles:
        all_terms = natural_product(cycle, weights, n)
        nonzero = parity(all_terms)
        assert nonzero and all(len(term) >= m for term in all_terms)
        cancellations += sum(count > 1 and count % 2 == 0 for count in all_terms.values())
        small = natural_product(cycle, weights, m)
        assert parity(small) == {term for term in nonzero if len(term) <= m}
        if any(not (base.rows[e//n] >> (e % n) & 1) for e in cycle):
            spurious += 1
            assert not small and min(map(len, nonzero)) > m
        else:
            canonical += 1
            target = tuple(i for i, slot in enumerate(slots) if slot in cycle)
            assert target in expected and small == Counter({target: 1})
        low ^= parity(small)
    assert low == expected and canonical == len(expected) and spurious and cancellations
    for a, b in combinations(cycles, 2):
        # Before parity reduction, not even a single low-degree term occurs.
        assert not natural_product(a | b, weights, m)
    assert path_dp(n, weights, m) == expected
    if m == 2:
        # Independent complete-host order enumeration includes all killed tours.
        orders = [(0, *p) for p in permutations(range(1, n))]
        supports = [frozenset(n*order[i-1]+u for i, u in enumerate(order)) for order in orders]
        assert set(cycles) == {s for s in supports if all(any(weights[e]) for e in s)}
        for a, b in combinations(supports, 2):
            assert not natural_product(a | b, weights, m)
    print(f"m={m}, N={n}, rank=6: {canonical} canonical tours, {spurious} additional tours at higher degree, "
          f"{len(cycles)*(len(cycles)-1)//2} nonzero-support pair unions, "
          f"{cancellations} canceled individual-product coefficients")


def forbidden_pivot():
    m = 3
    base = router(m)
    n, d = len(base.rows), len(base.slots)
    slots = tuple(n*u+v for u, v in base.slots)
    first = base.target_arcs.index((0, 1))
    alternate = base.target_arcs.index((0, 2))
    # Add O_0[2]→I_1[0] as another way to travel from city 0 to city 1.
    pivot = n*alternate+d+first
    assert not (base.rows[pivot//n] >> (pivot % n) & 1)
    H = [(1 << pivot) | (1 << slots[first])]
    _, weights, _ = project(m, H, [0], (pivot,))
    assert weights[pivot] == (0, 1 << first)
    expected = {tuple(indices(t)) for t in tour_masks(m)}
    actual = path_dp(n, weights, m)
    assert actual == {t for t in expected if first not in t} and len(actual) == 1
    print("forbidden O→I pivot: two lifts cancel the directed 3-tour using arc 0→1")


def check_block_sums(m):
    """Degree m for general homogeneous linear weights on outgoing→incoming arcs.

    Any degree-m term must use precisely one such arc per exit ring and per
    entry ring. All other arcs use their original constant-one options. A
    choice of one concrete port-to-port arc per transition of a city tour
    determines the traversals of every ring uniquely. Summing these port
    choices per transition gives the block sums W_ij. A second distinct
    source tour cannot have a degree-m contribution to the squarefree union:
    it would need exactly the same crossing arcs and the same forced internal
    paths. This argument permits crossing coordinates of arbitrary rank.
    """
    base = router(m)
    n, d = len(base.rows), len(base.slots)
    rng = Random(3107+m)
    blocks = {(i, j): [] for i in range(m) for j in range(m)}
    for o, (i, _) in enumerate(base.target_arcs):
        for t, (_, j) in enumerate(base.target_arcs):
            blocks[i, j].append(n*o+d+t)
    weights = [(int(bool(base.rows[u] & (1 << v))), 0) for u in range(n) for v in range(n)]
    for (i, j), block in blocks.items():
        for col in block:
            weights[col] = (0, 0)
        # Dense port rectangle on three cities, sparse samples on four.
        chosen = block if m == 3 else rng.sample(block, 2)
        for col in chosen:
            weights[col] = (0, rng.randrange(1, 1 << d))
        if (i, j) == (0, 1):
            # An even number of actual arcs with identical labels add to zero.
            for col in chosen:
                weights[col] = (0, 3)
    # Non-crossing baseline-one perturbation does not enter the degree-m layer.
    weights[n*(2*d)] = (1, 3)  # anchor 0 -> the first outgoing port of city 0
    block_weights = {ij: xor_all(weights[col][1] for col in block) for ij, block in blocks.items()}
    assert block_weights[0, 1] == 0

    expected = set()
    for tour in tour_masks(m):
        factors = [indices(block_weights[base.target_arcs[i]]) for i in indices(tour)]
        for choices in product(*factors):
            expected.symmetric_difference_update((tuple(sorted(choices)),))
    assert expected  # Other city cycles remain visible.
    cycles = [frozenset(u*n+v for u, v in enumerate(succ))
              for succ in hamiltonian_successors(support_rows(n, weights))]
    actual = set()
    for cycle in cycles:
        small = natural_product(cycle, weights, m)
        assert all(len(term) == m for term in small)
        actual ^= parity(small)
    assert actual == expected
    if m == 3:  # Full Held–Karp on the dense 28-vertex example is unnecessary.
        assert path_dp(n, weights, m) == expected
    for a, b in combinations(cycles, 2):
        union = a | b
        # An independent pre-expansion cutoff: every zero-constant factor
        # must supply a variable. This makes all-pairs checking inexpensive.
        assert sum(weights[col][0] == 0 for col in union) > m
    print(f"m={m} general port weights: {len(cycles)} actual host tours, "
          f"{len(cycles)*(len(cycles)-1)//2} distinct-pair unions above cutoff, "
          f"{len(expected)} formal terms in hc_m(W)")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    for m in (2, 3, 4):
        examples(m, 82831+m)
    forbidden_pivot()
    for m in (3, 4):
        check_block_sums(m)
