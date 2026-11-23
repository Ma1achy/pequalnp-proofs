"""Foreign row-rank certificates for an encoding with assigned visible blocks."""

from itertools import combinations, permutations, product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import Counts, encoded_bits, metrics, rref, satisfied
from helper_blocks import equality_family
from verify_inner_product import affine_flats


def binary_rank(vectors):
    pivots = {}
    for vector in vectors:
        while vector:
            lead = vector.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = vector
                break
            vector ^= pivots[lead]
    return len(pivots)


def null_basis(rows, bits):
    # Core RREF uses RHS in bit zero. A unit assignment to one free
    # coordinate determines the pivot values because all pivots are reduced.
    reduced = rref([row << 1 for row in rows], bits, Counts())
    normals = [row >> 1 for row in reduced]
    pivots = [row.bit_length() - 1 for row in normals]
    basis = []
    for j in range(bits):
        if j in pivots:
            continue
        member = 1 << j
        for row, pivot in zip(normals, pivots):
            if row & (1 << j):
                member |= 1 << pivot
        basis.append(member)
    return basis


def parity(bits):
    return bits.bit_count() & 1


def polar(a, b, size):
    return parity((a & (b >> size)) ^ (b & (a >> size)))


def quadratic(point, size):
    return parity(point & (point >> size))


def local_profile(foreign_rows, size):
    basis = null_basis(foreign_rows, 2 * size)
    pairing = [sum(polar(a, b, size) << j for j, b in enumerate(basis)) for a in basis]
    polar_rank = binary_rank(pairing)
    assert not (polar_rank % 2)
    if not basis:
        return len(basis), 0, 0
    u = basis[0]
    # Choose a with q(a+u)+q(a)=1. The two halves of a local vector
    # are the operands of the inner product.
    if quadratic(u, size):
        anchor = 0
    else:
        j = (u & -u).bit_length() - 1
        anchor = 1 << ((j + size) % (2 * size))
    assert quadratic(anchor, size) ^ quadratic(anchor ^ u, size)
    return len(basis), polar_rank // 2, anchor


def foreign_profiles(flats, homes, sizes, helpers):
    """Rows use x blocks, then y blocks, then helpers. Returns one profile per block."""
    if len(flats) != len(homes) or any(i not in range(len(sizes)) for i in homes):
        raise ValueError('each flat must have one valid home')
    if any(b <= 0 for b in sizes):
        raise ValueError('product blocks must have positive size')
    k = sum(sizes)
    n = 2 * k + helpers
    canonical = [(rref(flat, n, Counts()), home) for flat, home in zip(flats, homes)]
    result = []
    start = 0
    for i, b in enumerate(sizes):
        mask = (1 << b) - 1
        rows = []
        for flat, home in canonical:
            if home == i or flat is None:
                continue
            for row in flat:
                coefficients = row >> 1
                x = (coefficients >> start) & mask
                y = (coefficients >> (k + start)) & mask
                rows.append(x | (y << b))
        d, r, anchor = local_profile(rows, b)
        result.append(dict(size=b, foreign_rank=2 * b-d, private_dimension=d,
                           half_polar_rank=r, anchor=anchor))
        start += b
    return result


def dense_shear(b):
    """Mix the first two of three equal product blocks by a parity-preserving shear."""
    k = 3 * b
    _, flats = equality_family(k, 2)
    home = [i for i in range(3) for _ in range(1 << b)]
    bits = (1 << b) - 1
    x1, x2 = bits, bits << b
    y1, y2 = bits << k, bits << (k + b)

    def substitute(row):
        vector = row >> 1
        mixed = vector
        if parity(vector & x1):
            mixed ^= x2
        if parity(vector & y2):
            mixed ^= y1
        return (mixed << 1) | (row & 1)

    return [tuple(substitute(row) for row in flat) for flat in flats], home


def all_subspaces(n):
    current = {frozenset([0])}
    all_spaces = set(current)
    while current:
        enlarged = set()
        for space in current:
            for v in range(1 << n):
                if v not in space:
                    enlarged.add(space.union(u ^ v for u in space))
        all_spaces |= enlarged
        current = enlarged
    return all_spaces


def check_restrictions():
    """Independent point-set enumeration of all local kernels in dimensions 2 and 4."""
    checked = 0
    for b in (1, 2):
        n = 2*b
        spaces = all_subspaces(n)
        for ker in spaces:
            # A direct dot-product scan obtains every linear form annihilating ker.
            foreign = [u for u in range(1 << n) if all(not parity(u & v) for v in ker)]
            d, r, anchor = local_profile(foreign, b)
            assert len(ker) == 1 << d
            assert 2 * r >= 2 * (b - binary_rank(foreign))
            if d:
                assert {quadratic(anchor ^ u, b) for u in ker} == {0, 1}
            # The largest graph flat projects injectively to a coset on which
            # q is affine. Affineness on any coset of a direction is equivalent
            # to zero second differences at 0; all cosets have the same answer.
            max_size = max(len(U) for U in spaces if U <= ker and all(
                quadratic(x ^ y, b) == quadratic(x, b) ^ quadratic(y, b)
                for x, y in product(U, repeat=2)))
            assert max_size == 1 << (d-r)
            checked += 1
    return checked


def main():
    local_checks = check_restrictions()
    print('local subspaces checked:', local_checks)
    for b in (1, 2, 3, 6):
        k = 3*b
        flats, homes = dense_shear(b)
        profiles = foreign_profiles(flats, homes, [b]*3, 2)
        assert [p['foreign_rank'] for p in profiles] == [1, 1, 0]
        assert [p['half_polar_rank'] for p in profiles] == [b-1, b-1, b]
        checks = 0
        if b <= 2:
            for v in range(1 << (2*k)):
                witnesses = sum(satisfied(flats, v | (w << (2*k))) for w in range(4))
                assert witnesses == int(quadratic(v, k) == 0)
                checks += 1
        lower = sum(1 << p['half_polar_rank'] for p in profiles)
        print('block_size', b, 'clauses', len(flats), 'bound', lower,
              'input_bits', encoded_bits(flats, 2*k+2), 'visible_points_checked', checks)



def lift_local(encoded, start, size, k):
    """Lift an affine bit expression on a block to the full x,y input."""
    mask = encoded >> 1
    part = (1 << size) - 1
    full = ((mask & part) << start) | ((mask >> size) << (start + k))
    return (full << 1) | (encoded & 1)


def lift_helper(expr, k):
    return ((expr >> 1) << (2*k+1)) | (expr & 1)


def affine_bit(expr, point):
    return parity((expr >> 1) & point) ^ (expr & 1)


def compile_switch(sizes, switch, label_pair):
    """The middle reads its own block. Endpoints may also read an affine middle bit.

    label_pair[s][i] is the affine expression for block i's required parity, in
    the two helpers at switch s. Callers supply bijections to the even patterns.
    """
    k = sum(sizes)
    if len(sizes) != 3 or sizes[1] < 2 or not 0 < (switch >> 1) < (1 << (2*sizes[1])):
        raise ValueError('expected a nonconstant affine bit of the middle block of size >= 2')
    for labels in label_pair:
        words = {tuple(affine_bit(f, w) for f in labels) for w in range(4)}
        if words != {(0,0,0), (1,1,0), (1,0,1), (0,1,1)}:
            raise ValueError('labels must map the four witnesses bijectively onto even patterns')

    out, homes = [], []
    sigma = lift_local(switch, sizes[0], sizes[1], k)
    start = 0
    for i, size in enumerate(sizes):
        alpha = lift_helper(label_pair[0][i], k)
        beta = alpha ^ lift_helper(label_pair[1][i], k)
        if i == 1:
            mask = (1 << size) - 1
            # B(a,v) = linear part of switch(v).
            a = (((switch >> 1) & mask) << size) | ((switch >> 1) >> size)
            target = alpha ^ (beta if quadratic(a, size) ^ (switch & 1) else 0)
            for operand in range(1 << size):
                rows = []
                for j in range(size):
                    fixed = (1 << (start+j+1)) | ((operand >> j) & 1)
                    rows.append(fixed ^ (beta if (a >> j) & 1 else 0))
                dot = operand << (k+start+1)
                rows.append(dot ^ (beta if parity(operand & (a >> size)) else 0) ^ target ^ 1)
                out.append(tuple(rows))
                homes.append(i)
        else:
            for operand in range(1 << size):
                fixed = tuple((1 << (start+j+1)) | ((operand >> j) & 1) for j in range(size))
                dot = operand << (k+start+1)
                if beta >> 1:
                    for t in range(2):
                        out.append(fixed + (beta ^ t, dot ^ alpha ^ (sigma if t else 0) ^ 1))
                        homes.append(i)
                else:
                    out.append(fixed + (dot ^ alpha ^ (sigma if beta else 0) ^ 1,))
                    homes.append(i)
        start += size
    return out, homes


def maps_to_even_labels():
    patterns = (0, 3, 5, 6)
    result = []
    for permutation in permutations(patterns):
        labels = []
        for i in range(3):
            values = [(v >> i) & 1 for v in permutation]
            expr = values[0] | ((values[0] ^ values[1]) << 1) | ((values[0] ^ values[2]) << 2)
            assert [affine_bit(expr, w) for w in range(4)] == values
            labels.append(expr)
        result.append(labels)
    return result


def check_switch_bounds():
    # For each possible local label pair, compare the minimum graph cover
    # predicted by the theorem with a brute-force maximal-contained-flat bound.
    # Count both the independent switch (endpoint) and dependent switch (middle).
    pairs = list(product(range(2, 8), repeat=2))
    count = 0
    for endpoint in (False, True):
        b = 1 if endpoint else 2
        n = 2*b + 2 + int(endpoint)
        inventory = [(1 << dim, sum(1 << p for p in flat)) for dim, flat in affine_flats(n)]
        for f0, f1 in pairs:
            bad = 0
            for point in range(1 << n):
                v = point & ((1 << (2*b)) - 1)
                s = (point >> (n-1)) if endpoint else parity(v & 5) ^ 1
                w = (point >> (2*b)) & 3
                if quadratic(v, b) != affine_bit((f0, f1)[s], w):
                    bad |= 1 << point
            biggest = max(size for size, mask in inventory if not mask & ~bad)
            delta = endpoint and (f0 >> 1 != f1 >> 1)
            assert bad.bit_count() == (1 << (b+delta)) * biggest
            count += 1
    return count


def check_switch():
    sizes = (1, 2, 1)
    k = sum(sizes)
    switch = 2*5+1
    maps = maps_to_even_labels()
    checks = 0
    for pair in product(maps, repeat=2):
        raw, homes = compile_switch(sizes, switch, pair)
        expected = sum(1 << (size + int(i != 1 and (pair[0][i] >> 1) != (pair[1][i] >> 1)))
                       for i, size in enumerate(sizes))
        assert len(raw) == expected
        for v in range(1 << (2*k)):
            local_values = []
            start = 0
            for size in sizes:
                mask = (1 << size) - 1
                local_values.append(((v >> start) & mask) | (((v >> (k+start)) & mask) << size))
                start += size
            s = affine_bit(switch, local_values[1])
            expect_bits = tuple(quadratic(value, size) for value, size in zip(local_values, sizes))
            for w in range(4):
                assert satisfied(raw, v | (w << (2*k))) == (
                    expect_bits == tuple(affine_bit(f, w) for f in pair[s]))
                checks += 1
    print('global switch-map pairs',len(maps)**2, 'full visible/witness assignments', checks)
    print('exact local volume bounds from full flat inventories', check_switch_bounds())
    # Check every nonconstant middle switch and all 36 possible middle label
    # pairs at this size. Projecting endpoint coordinates to zero is harmless
    # for the middle group's predicate.
    middle_cases = 0
    example_per_label = {labels[1]: labels for labels in maps}
    for candidate_switch in range(2, 32):
        for f0, f1 in product(range(2, 8), repeat=2):
            chosen = (example_per_label[f0], example_per_label[f1])
            raw, homes = compile_switch(sizes, candidate_switch, chosen)
            middle = [flat for flat, home in zip(raw, homes) if home == 1]
            for local, w in product(range(16), range(4)):
                v = ((local & 3) << 1) | ((local >> 2) << (k+1))
                s = affine_bit(candidate_switch, local)
                assert satisfied(middle, v | (w << (2*k))) == (
                    quadratic(local, 2) == affine_bit((f0, f1)[s], w))
                middle_cases += 1
    print('middle assignments for all 30 switches and 36 label pairs', middle_cases)
    # p_1=w_1+s*w_2, p_2=w_2, p_3=w_1+(1+s)*w_2.
    b = 2
    k = 3*b
    raw, homes = compile_switch([b]*3, 2*((1 << b)-1), ([2, 4, 6], [6, 4, 2]))
    ranks = [binary_rank((r >> (2*k+1)) for r in flat) for flat in raw]
    assert ranks.count(2) == 4*(1 << b)
    essential = set()
    for v in range(1 << (2*k)):
        if not quadratic(v, k):
            continue
        for w in range(4):
            point = v | (w << (2*k))
            failed = [i for i, flat in enumerate(raw) if not satisfied([flat], point)]
            if len(failed) == 1:
                essential.add(failed[0])
    assert essential == set(range(len(raw)))
    print('switched example size', len(raw), 'rank two', ranks.count(2),
          'projection-essential', len(essential), 'emitted representation', metrics(raw, 2*k+2))


def parity_layer_section(b, p, q, packed):
    """An affine section producing p,q on equal group bits, odd patterns otherwise."""
    if not b or p == q or parity(p) or parity(q) or max(p, q) >= 16:
        raise ValueError('expected distinct even four-bit patterns')
    difference = p ^ q
    single = difference & -difference
    if p & single:
        p, q = q, p
    # The singleton receives b products, the other odd group receives b-1.
    full = packed & ((1 << (2*b)) - 1)
    small = packed >> (2*b)
    mask = (1 << (b-1)) - 1
    pattern = 0
    groups = []
    for i in range(4):
        if 1 << i == single:
            value = full
        elif difference & (1 << i):
            # Pad both operands with the same fixed parity-offset bit.
            offset = (p >> i) & 1
            x = (small & mask) | (offset << (b-1))
            y = (small >> (b-1)) | (offset << (b-1))
            value = x | (y << b)
        else:
            fixed = (p >> i) & 1
            value = fixed | (fixed << b)
        groups.append(value)
        pattern |= quadratic(value, b) << i
    expected = quadratic(full, b) == quadratic(small, b-1)
    return groups, pattern, expected


def check_parity_layers():
    patterns = [j for j in range(16) if not parity(j)]
    cases = 0
    b = 2
    for p, q in combinations(patterns, 2):
        points = [parity_layer_section(b, p, q, v) for v in range(1 << (4*b-2))]
        # Verify affine dependence of the ambient coordinates by reconstructing
        # the map pointwise from its value at zero and on coordinate generators.
        packed = [sum(a << (2*b*i) for i, a in enumerate(blocks)) for blocks, _, _ in points]
        basis = [packed[1 << i] ^ packed[0] for i in range(4*b-2)]
        for point, image in enumerate(packed):
            predicted = packed[0]
            for i, row in enumerate(basis):
                if point & (1 << i):
                    predicted ^= row
            assert predicted == image
        for mask in range(1 << len(patterns)):
            layer = {s for j,s in enumerate(patterns) if mask & (1 << j)}
            if not {p,q} <= layer:
                continue
            for _, pattern, expected in points:
                assert (pattern in layer) == expected
                cases += 1
    print('four-block parity-layer section assignments', cases)


if __name__ == '__main__':
    main()
    check_switch()
    check_parity_layers()
