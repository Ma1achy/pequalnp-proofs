"""Finite witnesses and independent checks for the weighted helper-square bounds."""

from itertools import combinations, product


def basis(vectors):
    pivots = {}
    for v in vectors:
        for i in sorted(pivots, reverse=True):
            if v >> i & 1:
                v ^= pivots[i]
        if v:
            i = v.bit_length() - 1
            for j, old in pivots.items():
                if old >> i & 1:
                    pivots[j] ^= v
            pivots[i] = v
    return tuple(pivots[i] for i in sorted(pivots, reverse=True))


def dual(u, k):
    # A coefficient mask r represents the symplectic normal B(dual(r),-).
    low = (1 << k) - 1
    return ((u & low) << k) | (u >> k)


def form(u, v, k):
    return (dual(u, k) & v).bit_count() & 1


def polar_rank(space, k):
    return len(basis(sum(form(u, v, k) << i for i, v in enumerate(space)) for u in space))


def odd(v, k):
    return ((v & (v >> k)) & ((1 << k) - 1)).bit_count() & 1


def square_det(u, v):
    return ((u & 1) & (v >> 1)) ^ ((u >> 1) & (v & 1))


def four_graph_piece(labels):
    a, b, c, d = labels
    u, v = b ^ a, c ^ a
    return u if a ^ b ^ c ^ d == 0 and square_det(u, v) else 0


def shape_checks():
    # For each ordered fiber family check minimality against the claimed tests.
    square = frozenset(range(4))
    line_normals = (1, 2, 3)
    seen = 0
    for num_lines, num_points in ((2, 0), (3, 0), (2, 1), (1, 2), (0, 4)):
        for normals in product(line_normals, repeat=num_lines):
            for bits in product(range(2), repeat=num_lines):
                lines = [frozenset(w for w in square if ((w & a).bit_count() & 1) == b)
                         for a, b in zip(normals, bits)]
                for points in product(range(4), repeat=num_points):
                    fibers = lines + [frozenset((p,)) for p in points]
                    covers = frozenset().union(*fibers) == square
                    minimal = covers and all(frozenset().union(*(fibers[:i] + fibers[i+1:])) != square
                                             for i in range(len(fibers)))
                    if num_lines == 0:
                        prediction = bool(four_graph_piece(points))
                    elif (num_lines, num_points) == (1, 2):
                        a, = normals
                        b, = bits
                        s, t = points
                        nonzero_kernel = next(u for u in (1, 2, 3) if (u & a).bit_count() % 2 == 0)
                        prediction = (a & s).bit_count() % 2 != b and s ^ t == nonzero_kernel
                    elif (num_lines, num_points) == (2, 1):
                        p, = points
                        prediction = normals[0] != normals[1] and all(p not in line for line in lines)
                    elif (num_lines, num_points) == (2, 0):
                        prediction = normals[0] == normals[1] and bits[0] != bits[1]
                    else:
                        prediction = len(set(normals)) == 3 and sum(bits) % 2 == 0
                    assert prediction == minimal, (normals, bits, points, fibers)
                    seen += 1
    return seen


def normal_checks():
    # All directions in 4D, all affine translates on q=1 and all smaller normal spaces.
    k, all_space = 2, range(16)
    spaces = {()}
    for v in all_space:
        spaces |= {basis((*s, v)) for s in spaces}
    assert len(spaces) == 67
    tested = 0
    for direction in spaces:
        fiber = {0}
        for u in direction:
            fiber |= {v ^ u for v in fiber}
        translations = {frozenset(x ^ a for x in fiber) for a in all_space}
        flats = [flat for flat in translations if all(odd(p, k) for p in flat)]
        if not flats:
            continue
        full = basis(v for v in all_space if all(form(v, u, k) == 0 for u in direction))
        assert polar_rank(full, k) == 2 * (len(full) - k)
        for normal in spaces:
            if len(basis((*normal, *full))) > len(full):
                continue
            t = len(full) - len(normal)
            rho = polar_rank(normal, k)
            assert len(normal) >= k - t + max(1, rho // 2)
            tested += len(flats)
    return tested


def tight(k):
    """Four graphs on visible domains with aggregate codimension exactly k-4."""
    scope = range(2, k - 2)
    per_domain = [sum(1 << j for j in scope if j % 4 == i) for i in range(4)]
    low = (1 << k) - 1
    groups = [0] * 4
    for visible in range(1 << (2 * k)):
        x, y = visible & low, visible >> k
        u = x & 3
        v = ((y & 1) << 1) | ((y >> 1) & 1)
        r = x >> (k - 2)
        labels = (0, u, v, u ^ v ^ r)
        active = [c for c, d in zip(labels, per_domain) if x & d == 0]
        covers = len(set(active)) == 4
        piece = four_graph_piece(labels) if len(active) == 4 else 0
        assert bool(piece) == covers
        if covers:
            assert odd(visible, k)
            groups[piece] += 1
    assert groups == [0] + [1 << (k - 1)] * 3
    normals = tuple(dual(1 << j, k) for j in scope)
    assert len(basis(normals)) == k - 4 and polar_rank(normals, k) == 0
    return sum(groups), groups[1:]


def main():
    print("Ordered helper-fiber shape checks:", shape_checks())
    print("Odd-flat/subspace normal checks:", normal_checks())
    for k in range(4, 9):
        count, blocks = tight(k)
        print(f"k={k} common codimension={k-4} odd points={count} split={blocks}")
    # Capacity obstruction at k=8: four domain normals span two symplectic pairs.
    k = 8
    normal = (1, 2, 1 << k, 2 << k)
    assert polar_rank(normal, k) == 4 > 2 * (len(normal) + 5 - k)
    print("k=8: a four-dimensional normal space of polar rank four cannot support an odd quartet.")


if __name__ == "__main__":
    main()
