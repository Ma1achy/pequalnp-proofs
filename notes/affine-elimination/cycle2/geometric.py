"""Check direction bounds, the three-flat quartet projector, and sharp families."""

from itertools import combinations, product
from pathlib import Path
from random import Random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify_inner_product import affine_flats
from flat_elimination import Counts, rref, satisfied


def q(k, point):
    return ((point >> k) & point).bit_count() & 1


def direction_capacity(k):
    groups = {}
    for dim, points in affine_flats(2 * k):
        key = frozenset(p ^ points[0] for p in points)
        if key not in groups:
            groups[key] = [dim, 0]
        groups[key][1] += int(all(q(k, p) for p in points))
    groups_with_odd = [0] * (2 * k + 1)
    for key, (dim, count) in groups.items():
        isotropic = all(q(k, x ^ y) == (q(k, x) ^ q(k, y)) for x in key for y in key)
        if isotropic:
            t = 1 << (k - dim)
            assert count == t * (t - 1) // 2
        else:
            assert count == 0
        groups_with_odd[dim] += int(count > 0)
    return len(groups), groups_with_odd


def direction_cover(k, d):
    """Partition each fixed-x odd level using a d-dimensional direction in the y bits."""
    mask = (1 << (d + 1)) - 1
    flats = []
    directions = set()
    for x in range(1, 1 << k):
        restricted = x & mask or 1
        direction = [z for z in range(mask + 1) if not ((z & restricted).bit_count() & 1)]
        directions.add(tuple(direction))
        remaining = {y for y in range(1 << k) if (y & x).bit_count() & 1}
        while remaining:
            y = min(remaining)
            ys = {y ^ z for z in direction}
            assert len(ys) == 1 << d and ys <= remaining
            remaining -= ys
            flats.append({x | (v << k) for v in ys})
    odd = {v for v in range(1 << (2 * k)) if q(k, v)}
    assert set.union(*flats) == odd
    assert sum(map(len, flats)) == len(odd)
    number, count = len(flats), len(directions)
    R = (1 << k) - 1
    assert number == R << (k - d - 1)
    assert count == (1 << (d + 1)) - 1
    assert (2 * number - R) * count >= R * R
    return number, count


def eval_form(packed, visible):
    return (packed & 1) ^ (((packed >> 1) & visible).bit_count() & 1)


def eval_map(f, visible):
    return eval_form(f[0], visible) | (eval_form(f[1], visible) << 1)


def compile_quartet(n, domains, maps):
    """Compile simultaneous coverage of the helper square by four affine graphs.

    Each map entry packs affine linear coefficients above the constant bit.
    Domain equations use the same packing and require the form to vanish.
    """
    domain = [row for D in domains for row in D]
    f0, f1, f2, f3 = maps
    a = tuple(s ^ t for s, t in zip(f0, f1))
    b0, b1 = (s ^ t for s, t in zip(f0, f2))
    c = [v ^ w ^ x ^ y for v, w, x, y in zip(f0, f1, f2, f3)]
    projected = []
    for u in (1, 2, 3):
        determinant = (b1 if u & 1 else 0) ^ (b0 if u & 2 else 0)
        rows = domain + c + [a[0] ^ (u & 1), a[1] ^ (u >> 1), determinant ^ 1]
        flat = rref(rows, n, Counts())
        if flat is not None:
            projected.append(flat)
    return projected


def check_quartets():
    for labels in product(range(4), repeat=4):
        maps = [(v & 1, v >> 1) for v in labels]
        out = compile_quartet(0, [()] * 4, maps)
        assert (not satisfied(out, 0)) == (len(set(labels)) == 4)
    rng = Random(77233)
    cases = 384
    for case in range(cases):
        n = 1 + case % 7
        maps = [[rng.randrange(1 << (n + 1)) for _ in range(2)] for _ in range(4)]
        domains = [[rng.randrange(1 << (n + 1)) for _ in range(rng.randrange(3))]
                   for _ in range(4)] if case % 2 else [()] * 4
        out = compile_quartet(n, domains, maps)
        for v in range(1 << n):
            active = {eval_map(f, v) for D, f in zip(domains, maps)
                      if all(eval_form(row, v) == 0 for row in D)}
            assert (not satisfied(out, v)) == (len(active) == 4)
    return cases


def check_invertible_core():
    # A point of F2^4 packs the two columns into its low and high two bits.
    core = {a | (b << 2) for a, b in product(range(1, 4), repeat=2) if a != b}
    hyperplane_counts = []
    for normal in range(1, 16):
        for offset in (0, 1):
            hyperplane_counts.append(sum((matrix & normal).bit_count() % 2 == offset
                                         for matrix in core))
    assert sorted(set(hyperplane_counts)) == [2, 4]
    return len(core), len(hyperplane_counts)


def check_sharp_quartet(k):
    x = [1 << (i + 1) for i in range(k)]
    y = [1 << (k + i + 1) for i in range(k)]
    a, b, c = (x[0], x[1]), (y[1], y[0]), (x[2], x[3])
    maps = [(0, 0), a, b, tuple(ai ^ bi ^ ci for ai, bi, ci in zip(a, b, c))]
    domains = [x[4 + j::4] for j in range(4)]
    out = compile_quartet(2 * k, domains, maps)
    assert len(out) == 3 and all(len(flat) == k + 1 for flat in out)
    cover = set()
    for v in range(1 << (2 * k)):
        expected = q(k, v) == 1 and (v & ((1 << k) - 1)) < 4
        active = {eval_map(f, v) for D, f in zip(domains, maps)
                  if all(eval_form(row, v) == 0 for row in D)}
        assert expected == (len(active) == 4) == (not satisfied(out, v))
        if expected:
            cover.add(v)
    assert len(cover) == 3 * (1 << (k - 1))
    fibers = {}
    for v in range(1 << (2 * k)):
        if any(eval_form(row, v) for D in domains for row in D):
            continue
        if eval_map(c, v):
            continue
        pa, pb = eval_map(a, v), eval_map(b, v)
        value = int(0 not in (pa, pb) and pa != pb)
        assert q(k, v) == value
        fibers.setdefault((pa, pb), []).append(v)
    assert len(fibers) == 16
    assert all(len(points) == 1 << (k - 2) for points in fibers.values())
    assert sum(q(k, points[0]) for points in fibers.values()) == 6
    return len(cover)


def block_compiler(k, s):
    """s nonempty product blocks, s-1 helpers, and s visible slice directions."""
    h = s - 1
    mask = (1 << h) - 1
    entries = []
    start = 0
    for block in range(s):
        b = k // s + int(block < k % s)
        x_mask = (1 << b) - 1
        v_mask = (x_mask | (x_mask << k)) << start
        helper_mask = mask if block == s - 1 else 1 << block
        for local_x, local_y in product(range(1 << b), repeat=2):
            bit = (local_x & local_y).bit_count() & 1
            if not helper_mask and bit == 0:
                continue
            v_bits = (local_x | (local_y << k)) << start
            entries.append((v_mask, v_bits, helper_mask, 1 ^ bit))
        start += b
    return entries


def check_direction_limit(k, s):
    entries = block_compiler(k, s)
    assert len(set(e[0] for e in entries)) == s
    for v in range(1 << (2 * k)):
        allowed = 0
        for w in range(1 << (s - 1)):
            if not any((v & mask) == bits and ((w & a).bit_count() & 1) == rhs
                       for mask, bits, a, rhs in entries):
                allowed += 1
        assert allowed == int(q(k, v) == 0)
    return len(entries)


if __name__ == "__main__":
    for k in (1, 2, 3):
        print("k, subspace directions, directions containing odd flats by dimension:",
              k, *direction_capacity(k))
    print("k | (flat count, direction count) at dimensions 0 through k-1")
    for k in range(1, 7):
        print(k, [direction_cover(k, d) for d in range(k)], sep=" | ")
    print("invertible matrices and affine hyperplanes:", check_invertible_core())
    print("constant quartets checked:", 4**4)
    print("seeded affine quartets checked:", check_quartets())
    print("sharp quartet coverage by k:", {k: check_sharp_quartet(k) for k in range(4, 9)})
    print("low-direction encoding counts by (k,s):",
          {(k, s): check_direction_limit(k, s) for k in range(1, 5)
           for s in range(1, min(k, 3) + 1)})
