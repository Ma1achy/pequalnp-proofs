"""Verify the minimal five-clause witness and checks used to exclude five point fibers."""

from collections import Counter
from itertools import product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import Counts, normalize, project, satisfied


def witness():
    # Variables x1,x2,x3,y1,y2,y3,w0,w1. Every pair of rows defines one forbidden flat.
    x1, x2, x3, y1, y2, y3, w0, w1 = (1 << (i+1) for i in range(8))
    return [(w0, w1), (w0 ^ x1, w1 ^ x2), (w0 ^ y2, w1 ^ y1),
            (w0 ^ x1 ^ y2, w1 ^ x2 ^ y1 ^ x3), (x3 ^ 1, w0 ^ y3 ^ x1 ^ y2)]


def q(v):
    return ((v >> 3) & v & 7).bit_count() & 1


def determinant(a,b):
    return ((a & 1) & (b >> 1)) ^ ((a >> 1) & (b & 1))


def check_witness():
    rows = witness()
    for a, b in product(range(4), repeat=2):
        d = determinant(a, b)
        assert (len({0, a, b, a ^ b}) == 4) == bool(d)
        special = d ^ (a & 1) ^ (b & 1)
        labels = {0, a, b, a ^ b ^ 2}
        for side in (0, 1):
            assert ({side, side + 2} <= labels) == (side == special)
    flats = normalize(rows, 8, Counts())
    stages = [len(flats)]
    for variable in (6, 7):
        flats = project(flats, variable, 8, Counts())
        stages.append(len(flats))
    counts = Counter()
    for v in range(64):
        witnesses = sum(satisfied(rows, v + 64*w) for w in range(4))
        counts[witnesses] += 1
        assert bool(witnesses) == (not q(v))
        assert satisfied(flats, v) == (not q(v))
    losses = []
    for i in range(5):
        reduced = rows[:i] + rows[i+1:]
        losses.append(sum(q(v) and any(satisfied(reduced, v + 64*w) for w in range(4))
                          for v in range(64)))
    assert losses == [19, 19, 19, 19, 16]
    return rows, stages, sorted(counts.items()), losses


def check_point_exclusions():
    # Fourier coefficients of the full-domain square-coverage predicate on 8 bits.
    rainbow = [p for p in range(256) if len({0, p & 3, (p>>2)&3, (p>>4)&3, p>>6}) == 4]
    assert len(rainbow) == 60
    coefficients = Counter()
    for mask in range(1,256):
        parts = [(mask >> (2*i)) & 3 for i in range(4)]
        s = sum(p != 0 for p in parts)
        rank = min(2, len(set(parts) - {0}))
        total = parts[0] ^ parts[1] ^ parts[2] ^ parts[3]
        calculated = -((-1)**s) * 3**(4-s) * (3 if total == 0 else -1) + 16*((1 << (2-rank))-1) - 1
        exact = sum((-1)**((p & mask).bit_count() % 2) for p in rainbow)
        assert calculated == exact
        coefficients[exact] += 1
    assert max(abs(x) for x in coefficients) == 12
    for normal in range(1,64):
        radical = ((normal & 7) << 3) | (normal >> 3)
        differences = [set(),set()]
        for v in range(64):
            side = (v & normal).bit_count() % 2
            differences[side].add(q(v) ^ q(v ^ radical))
        assert sorted(map(sorted, differences)) == [[0], [1]]
    return dict(sorted(coefficients.items()))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    rows, stages, counts, losses = check_witness()
    print("Forbidding rows", rows)
    print("Successive cover sizes", stages)
    print("Number of visible points by accepting witness count", counts)
    print("Odd inputs spuriously accepted by single deletion", losses)
    print("Nonzero-mask rainbow Fourier sums", check_point_exclusions())
