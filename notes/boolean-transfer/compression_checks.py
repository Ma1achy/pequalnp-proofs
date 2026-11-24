"""Check the linear-algebra part of directed-port compression over F_2.

An ambient vector has one coordinate per loopless arc (tail, head). Column e
of a kernel generator is the coordinate functional x_e on parameter vectors.
For disjoint tail bins O_i and heads b_j we test surjectivity of
x -> (sum_{u in O_i} x_{u,b_j})_{j,i}, including prescribed zero diagonals.
Run with standard Python 3. The small tests compare Gaussian nullspaces with
exhaustive solutions to possibly dependent equations, and check every block
image in a six-dimensional kernel over all 810 two-head partitions. The larger
tests check the stronger independence modulo all prior heads and lift each
unit of the block matrix to an actual ambient arc vector obeying the original
constraints. They also test superpositions and the prescribed zero diagonal.
Cases include a full space, systematic random dense constraints, equality
groups and correlations between opposite arcs. The printed union bound is the
analytic bound at those finite parameters; surjectivity is checked directly
even for examples where that bound exceeds one. No tour polynomials are
expanded here.
"""

from itertools import combinations, product
from math import comb
from random import Random


def parity(bits):
    return bits.bit_count() & 1


def insert(basis, vector):
    while vector:
        p = vector.bit_length() - 1
        if p not in basis:
            basis[p] = vector
            return True
        vector ^= basis[p]
    return False


def echelon(vectors):
    basis = {}
    for vector in vectors:
        insert(basis, vector)
    return basis


def coordinates(n):
    return [(u, v) for v in range(n) for u in range(n) if u != v]


def kernel_columns(width, constraints):
    """Derive generator columns from actual homogeneous equations H x = 0."""
    pivots = echelon(constraints)
    free = [e for e in range(width) if e not in pivots]
    columns = [0] * width
    for i, e in enumerate(free):
        x = 1 << e
        for p, row in sorted(pivots.items()):
            if parity(row & x):
                x |= 1 << p
        assert all(not parity(h & x) for h in constraints)
        for v in range(width):
            if x >> v & 1:
                columns[v] |= 1 << i
    assert len(echelon(columns)) == len(free) == width - len(pivots)
    return columns


def ambient(columns, parameter):
    return sum(parity(col & parameter) << e for e, col in enumerate(columns))


def block_data(n, heads, bins, columns):
    """Return each block's ambient mask and its linear functional on K."""
    arc_index = {e: i for i, e in enumerate(coordinates(n))}
    masks, forms = [], []
    for head in heads:
        for tails in bins:
            mask = form = 0
            for tail in tails:
                e = arc_index[tail, head]
                mask |= 1 << e
                form ^= columns[e]
            masks.append(mask)
            forms.append(form)
    return masks, forms


def images(rows, x):
    return sum(parity(r & x) << i for i, r in enumerate(rows))


def right_inverse(rows):
    """Return parameter vectors mapping to each standard unit, or None."""
    pivots = {}
    for i, row in enumerate(rows):
        rhs = 1 << i
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row, rhs
                break
            old, old_rhs = pivots[p]
            row ^= old
            rhs ^= old_rhs
        else:
            return None
    inverse = []
    for i in range(len(rows)):
        parameter = 0
        for p, (row, rhs) in sorted(pivots.items()):
            if parity(row & parameter) ^ (rhs >> i & 1):
                parameter |= 1 << p
        assert images(rows, parameter) == 1 << i
        inverse.append(parameter)
    return inverse


def systematic(n, dimension, rng):
    """Independent parameters on initial coordinates, dense dependent suffix."""
    width = n * (n - 1)
    assert 0 <= dimension <= width
    columns = [1 << i for i in range(dimension)]
    columns.extend(rng.getrandbits(dimension) for _ in range(width - dimension))
    constraints = [(1 << e) ^ columns[e] for e in range(dimension, width)]
    return columns, constraints


def check_small():
    # Independent nullspace enumeration, with redundant equations included.
    rng = Random(119)
    cases = 0
    for _ in range(80):
        hs = [rng.getrandbits(6) for _ in range(rng.randrange(8))]
        hs += [0] + hs[:1]
        cols = kernel_columns(6, hs)
        d = len(echelon(cols))
        brute = {x for x in range(64) if not any(parity(h & x) for h in hs)}
        assert brute == {ambient(cols, z) for z in range(1 << d)}
        cases += 1

    # Every labelled partition with two fixed distinct heads and two reserved
    # anchors, for every unordered choice of the two heads and the two anchors.
    n, m = 6, 2
    cols, hs = systematic(n, 6, rng)
    assert kernel_columns(30, hs + [hs[0], 0]) == cols
    vectors = [ambient(cols, z) for z in range(64)]
    partitions = surjections = 0
    for heads in combinations(range(n), m):
        rest = [v for v in range(n) if v not in heads]
        for anchors in combinations(rest, m):
            allowed = [v for v in rest if v not in anchors]
            for labels in product(range(m+1), repeat=len(allowed)):
                bins = [[v for v, a in zip(allowed, labels) if a == i] for i in range(m)]
                masks, forms = block_data(n, heads, bins, cols)
                observed = {images(masks, x) for x in vectors}
                predicted = {images(forms, z) for z in range(64)}
                assert observed == predicted
                assert len(observed) == 1 << len(echelon(forms))
                inverse = right_inverse(forms)
                assert (inverse is not None) == (len(observed) == 1 << (m*m))
                if inverse is not None:
                    for i, z in enumerate(inverse):
                        assert images(masks, ambient(cols, z)) == 1 << i
                    surjections += 1
                partitions += 1
    assert 0 < surjections < partitions
    print(f'{cases} exact small nullspaces; {partitions} exhaustive partitions, '
          f'{surjections} surjections and {partitions-surjections} dependent maps')


def head_increments(n, cols):
    basis = {}
    tails = [[] for _ in range(n)]
    for e, (u, v) in enumerate(coordinates(n)):
        if insert(basis, cols[e]):
            tails[v].append(u)
    return tails


def independent_mod_prior_heads(n, heads, cols, forms):
    m = len(heads)
    selected = {b: j for j, b in enumerate(heads)}
    basis = {}
    for b in range(n):
        if b in selected:
            j = selected[b]
            extension = basis.copy()
            if not all(insert(extension, row) for row in forms[j*m:(j+1)*m]):
                return False
        for col in cols[b*(n-1):(b+1)*(n-1)]:
            insert(basis, col)
    return True


def check_random_partition(name, n, m, cols, hs, rng, validator=None):
    width = n*(n-1)
    assert len(cols) == width
    independent = head_increments(n, cols)
    d = sum(map(len, independent))
    k = d // (2*n)
    good = [b for b, tails in enumerate(independent) if len(tails) >= k]
    assert len(good) >= k >= m and k >= 2*m
    heads = sorted(rng.sample(good, m))
    rest = [x for x in range(n) if x not in heads]
    anchors = rng.sample(rest, m)
    allowed = [x for x in rest if x not in anchors]
    for b in heads:
        assert len(set(allowed).intersection(independent[b])) >= k-2*m

    for attempt in range(1, 101):
        labels = [rng.randrange(2*m) for _ in allowed]
        bins = [[u for u, label in zip(allowed, labels) if label == i] for i in range(m)]
        masks, forms = block_data(n, heads, bins, cols)
        if independent_mod_prior_heads(n, heads, cols, forms):
            break
    else:
        raise AssertionError(f'found no valid partition for {name}')
    inverse = right_inverse(forms)
    assert inverse is not None
    lifts = [ambient(cols, parameter) for parameter in inverse]
    for i, x in enumerate(lifts):
        assert images(masks, x) == 1 << i
        assert all(not parity(h & x) for h in hs)
        if validator is not None:
            assert validator(x)
    # Check superposition including the actual use with arbitrary target bits
    # off-diagonal and the diagonal fixed zero.
    diag = sum(1 << (j*m+j) for j in range(m))
    targets = list(range(1 << (m*m))) if m <= 3 else [rng.getrandbits(m*m) for _ in range(128)]
    for target in targets:
        for y in (target, target & ~diag):
            x = 0
            for i, lift in enumerate(lifts):
                if y >> i & 1:
                    x ^= lift
            assert images(masks, x) == y
    ub = m*sum(comb(m, h)*(1-h/(2*m))**(k-2*m) for h in range(1, m+1))
    print(f'{name}: n={n}, d={d}, k={k}, {m}x{m} independent blocks, '
          f'attempt={attempt}, union upper bound={ub:.3g}')


def main():
    check_small()
    rng = Random(59491)
    n = 96
    full, constraints = systematic(n, n*(n-1), rng)
    check_random_partition('full', n, 4, full, constraints, rng)

    n = 64
    dense, constraints = systematic(n, 3024, rng)
    check_random_partition('systematic dense constraints', n, 3, dense, constraints, rng)

    def grouped(name, key, m):
        labels, groups = {}, {}
        cols = []
        for e, (u, v) in enumerate(coordinates(n)):
            group = key(u, v)
            index = labels.setdefault(group, len(labels))
            cols.append(1 << index)
            groups[group] = groups.get(group, 0) | (1 << e)
        def validator(x):
            return all((x & mask) in (0, mask) for mask in groups.values())
        check_random_partition(name, n, m, cols, [], rng, validator)

    grouped('equalities within row groups', lambda u, v: (u, v//4), 2)
    grouped('equalities within column groups', lambda u, v: (u//4, v), 2)
    grouped('symmetric matrices', lambda u, v: tuple(sorted((u, v))), 3)

    # With only one free row or column label per index, a full block matrix
    # generally cannot be prescribed. The dimension hypothesis matters.
    n = 9
    heads, bins = [0, 1, 2], [[3], [4], [5]]
    for cols in ([1 << u for u, v in coordinates(n)], [1 << v for u, v in coordinates(n)]):
        _, forms = block_data(n, heads, bins, cols)
        assert len(echelon(forms)) == 3 and right_inverse(forms) is None
    print('Pure row and pure column kernels: both 3x3 maps have rank 3')


if __name__ == '__main__':
    main()
