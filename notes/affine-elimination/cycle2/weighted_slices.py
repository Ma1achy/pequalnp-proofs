"""Check the moment separators used on common isotropic slices."""

from itertools import combinations_with_replacement, product
from math import comb
from fractions import Fraction
from random import Random


def moments(counts):
    return tuple(sum(comb(n, r) for n in counts) for r in (2, 3))


def table():
    coefficients = {4: (1, 0), 5: (1, 0), 6: (4, -1), 7: (5, -2), 8: (13, -5)}
    for count, (a, b) in coefficients.items():
        cover, missing = [], []
        for hist in combinations_with_replacement(range(count + 1), 4):
            if sum(hist) != count:
                continue
            pairs, triples = moments(hist)
            (cover if min(hist) else missing).append(a*pairs + b*triples)
        assert max(cover) < min(missing)
        print(count, (len(cover), len(missing)), max(cover), min(missing))
    missing = [moments((0, 0, 0, 9)), moments((0, 3, 3, 3))]
    covering = [moments((1, 1, 1, 6)), moments((1, 1, 2, 5))]
    mean1 = tuple(Fraction(4*a+23*b, 27) for a, b in zip(*missing))
    mean2 = tuple(Fraction(a+b, 2) for a, b in zip(*covering))
    assert mean1 == mean2 == (13, 15)


def span(rows):
    out = {0}
    for r in rows:
        out |= {x ^ r for x in out}
    return out


def event_check():
    # All 4-row equality systems on two visible bits, independently counted
    # on both classes of each nonzero normal. Duplicate rows allowed.
    totals = 0
    for equations in product(range(8), repeat=4):
        matches = [v for v in range(4) if all(((m >> 1) & v).bit_count() % 2 == (m & 1)
                                               for m in equations)]
        linear_span = span([m >> 1 for m in equations])
        for normal in range(1, 4):
            plus = sum((v & normal).bit_count() % 2 for v in matches)
            if 2*plus != len(matches):
                assert normal in linear_span
            totals += 1
    return totals


def wedge(x, y, k):
    mask = (1 << k) - 1
    return (((x & mask) & (y >> k)).bit_count()
            + ((y & mask) & (x >> k)).bit_count()) % 2


def space_check():
    rng = Random(81477)
    tested = 0
    for k in (2, 3):
        vspace = set(range(1 << (2*k)))
        for _ in range(80):
            W = span([rng.randrange(1 << (2*k)) for _ in range(rng.randrange(2*k+1))])
            perp = {x for x in vspace if all(wedge(x, u, k) == 0 for u in W)}
            rho = len(W).bit_length() - len(W & perp).bit_length()
            U = {0}
            generators = []
            for v in sorted(perp):
                if v not in U and all(wedge(v, u, k) == 0 for u in generators):
                    generators.append(v)
                    U |= {x ^ v for x in U}
            assert len(generators) == k-rho//2
            histogram = {}
            for point in vspace:
                normal = tuple(wedge(point, u, k) ^ ((u & (u >> k)).bit_count() % 2)
                               for u in generators)
                histogram[normal] = histogram.get(normal, 0) + 1
            assert len(histogram) == len(U) and len(set(histogram.values())) == 1
            tested += 1
    return tested


if __name__ == "__main__":
    print("t (covering, missing histograms) largest covering score, smallest missing score")
    table()
    print("Equal-pair/triple affine row-space implications:", event_check())
    print("Uniform polar-slice normal checks:", space_check())
