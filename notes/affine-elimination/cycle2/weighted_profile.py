"""Visible-domain capacity test for two-helper affine encodings of even inner product."""

from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import Counts, rref
from helper_blocks import equality_family
from rank_certificates import _helper_basis
from weighted_checks import dual, polar_rank


@dataclass
class Profile:
    candidate_shapes: int = 0
    inconsistent_domains: int = 0
    too_small_codimension: int = 0
    too_large_polar_rank: int = 0
    loose_point_capacity: int = 0
    weighted_point_capacity: int = 0


def _candidates(cylinders, lines, points):
    yield from (((d,), 1, 0) for d in cylinders)
    for line1, line2 in combinations(lines, 2):
        a, b = line1[0], line2[0]
        pair = (line1[1], line2[1])
        if a == b:
            yield pair, 1, 1
        else:
            for point in points:
                yield (*pair, point), 1, 2
    for three in combinations(lines, 3):
        if len({a for a, _ in three}) == 3:
            yield tuple(d for _, d in three), 1, 1
    for _, line in lines:
        for x, y in combinations(points, 2):
            yield (line, x, y), 1, 3
    for four in combinations(points, 4):
        yield four, 3, 5


def capacity(k, raw):
    """Upper bound on odd points covered, conditional on exactness of the encoding.

    First 2k coordinates are x,y in two blocks, and last two are helpers.
    A result less than (2**k-1)*2**(k-1) refutes exactness.
    """
    if k < 1:
        raise ValueError("k must be positive")
    n = 2 * k + 2
    helper_mask = 3 << (2 * k + 1)
    counts = Counts()
    cylinders, lines, points = [], [], []
    for flat in raw:
        rows = rref(flat, n, counts)
        if rows is None:
            continue
        helper_rows, domain = _helper_basis(rows, helper_mask)
        domain = tuple(domain)
        if not helper_rows:
            cylinders.append(domain)
        elif len(helper_rows) == 1:
            lines.append((helper_rows[0] & helper_mask, domain))
        else:
            points.append(domain)
    profile = Profile()
    for domains, g, t in _candidates(cylinders, lines, points):
        profile.candidate_shapes += 1
        profile.loose_point_capacity += g << (k - 1)
        rows = rref((row for domain in domains for row in domain), 2*k, counts)
        if rows is None:
            profile.inconsistent_domains += 1
            continue
        c = len(rows)
        if c < k + 1 - t:
            profile.too_small_codimension += 1
            continue
        space = tuple(dual(row >> 1, k) for row in rows)
        if polar_rank(space, k) > 2 * (c + t - k):
            profile.too_large_polar_rank += 1
            continue
        profile.weighted_point_capacity += min(g << (k - 1), 1 << (2*k - c))
    return profile


def example(k, symplectic):
    if k != 8:
        raise ValueError("eight-pair comparison")
    domains = (1, 2, 1 << k, 2 << k) if symplectic else tuple(1 << j for j in range(2, 6))
    u = (1, 2)
    v = (2 << k, 1 << k)
    labels = ((0, 0), u, v, (u[0] ^ v[0] ^ (1 << (k-2)), u[1] ^ v[1] ^ (1 << (k-1))))
    return [((2 * d), 2 * ((1 << (2*k)) ^ rhs[0]), 2 * ((2 << (2*k)) ^ rhs[1]))
            for d, rhs in zip(domains, labels)]


if __name__ == "__main__":
    for k in (3, 4, 5):
        _, raw = equality_family(k, 2)
        profile = capacity(k, raw)
        odd_count = ((1 << k) - 1) << (k - 1)
        assert profile.weighted_point_capacity >= odd_count
        print(f"k={k} balanced encoding: {profile}, odd points={odd_count}")
    for symplectic, expected in ((False, 384), (True, 0)):
        profile = capacity(8, example(8, symplectic))
        assert profile.weighted_point_capacity == expected
        print(f"k=8 symplectic-domain comparison ({symplectic=}): {profile}")
