"""Project a fixed helper block using private-point certificates for affine covers."""

from dataclasses import dataclass
from itertools import combinations, product
from math import comb
from random import Random

from flat_elimination import Counts, rref


@dataclass
class Stats:
    subset_limit: int
    subset_tests: int = 0
    pattern_tests: int = 0
    covering_patterns: int = 0
    emitted_conflicts: int = 0
    largest_witness_used: int = 0
    four_member_subsets: int = 0
    nonminimal_patterns_skipped: int = 0


def _helper_basis(rows, helper_mask):
    """Triangularize helper columns, carrying the visible expression in each row."""
    pivots = {}
    domain = []
    for row in rows:
        for leading in sorted(pivots, reverse=True):
            if row & leading:
                row ^= pivots[leading]
        helper_part = row & helper_mask
        if helper_part:
            leading = 1 << (helper_part.bit_length() - 1)
            pivots[leading] = row
        else:
            domain.append(row)
    return tuple(pivots.values()), domain


def _options(basis, domain, helper_mask, witnesses, n, counts):
    """For each feasible RHS pattern, give its visible flat and covered helpers."""
    linear_parts = [row & helper_mask for row in basis]
    visible_parts = [row ^ part for row, part in zip(basis, linear_parts)]
    fibers = [0] * (1 << len(basis))
    for index, w in enumerate(witnesses):
        pattern = sum(((part & w).bit_count() % 2) << i
                      for i, part in enumerate(linear_parts))
        fibers[pattern] |= 1 << index
    options = []
    for pattern, fiber in enumerate(fibers):
        rows = domain + [part ^ (pattern >> i & 1) for i, part in enumerate(visible_parts)]
        visible = rref(rows, n, counts)
        if visible is not None:
            options.append((visible, fiber))
    return options


def _square_subsets(guards):
    lines = tuple(options for rank, options in guards if rank == 1)
    points = tuple(options for rank, options in guards if rank == 2)
    for num_lines, num_points in ((2, 0), (3, 0), (2, 1), (1, 2), (0, 4)):
        if len(lines) < num_lines or len(points) < num_points:
            continue
        for a in combinations(lines, num_lines):
            for b in combinations(points, num_points):
                yield a + b


def _union(masks):
    result = 0
    for mask in masks:
        result |= mask
    return result


def project_rank_bounded(raw_flats, n, helpers, rank_limit, *, specialize_square=True):
    """Return an explicit, possibly redundant forbidden-flat cover and event counts."""
    helpers = tuple(helpers)
    h = len(helpers)
    if n < 0 or len(set(helpers)) != h or any(v < 0 or v >= n for v in helpers):
        raise ValueError("invalid helper coordinates")
    if not 0 <= rank_limit <= h:
        raise ValueError("rank limit must lie between zero and helper count")
    limit = sum(comb(h, j) for j in range(rank_limit + 1))
    stats = Stats(limit)
    raw_flats = [tuple(flat) for flat in raw_flats]
    if not any(raw_flats):
        return (((),) if raw_flats else ()), stats
    helper_mask = sum(1 << (v + 1) for v in helpers)
    witnesses = [sum(((value >> i) & 1) << (v + 1) for i, v in enumerate(helpers))
                 for value in range(1 << h)]
    full = (1 << len(witnesses)) - 1
    counts = Counts()
    guarded = []
    output = []
    for flat in raw_flats:
        rows = rref(flat, n, counts)
        if rows is None:
            continue
        basis, domain = _helper_basis(rows, helper_mask)
        if len(basis) > rank_limit:
            raise ValueError("helper coefficient rank exceeds supplied limit")
        if not basis:
            output.append(rows)
        else:
            options = _options(basis, domain, helper_mask, witnesses, n, counts)
            guarded.append((len(basis), options))
    square = specialize_square and h == 2 and rank_limit == 2
    if square:
        subsets = _square_subsets(guarded)
    else:
        all_options = [options for _, options in guarded]
        subsets = (s for size in range(2, min(limit, len(guarded)) + 1)
                   for s in combinations(all_options, size))
    for subset in subsets:
        size = len(subset)
        stats.subset_tests += 1
        stats.four_member_subsets += int(size == 4)
        for options in product(*subset):
            stats.pattern_tests += 1
            masks = tuple(fiber for _, fiber in options)
            if _union(masks) != full:
                continue
            stats.covering_patterns += 1
            if square and any(_union(masks[:i] + masks[i+1:]) == full for i in range(size)):
                stats.nonminimal_patterns_skipped += 1
                continue
            common = rref((row for visible, _ in options for row in visible), n, counts)
            if common is not None:
                output.append(common)
                stats.emitted_conflicts += 1
                stats.largest_witness_used = max(stats.largest_witness_used, size)
    return tuple(output), stats


def _allowed(raw, point):
    return not any(all(((point & (row >> 1)).bit_count() & 1) == (row & 1)
                       for row in flat) for flat in raw)


def _compare(raw, n, helpers, rank):
    projected, stats = project_rank_bounded(raw, n, helpers, rank)
    helper_mask = sum(1 << v for v in helpers)
    assert not any((row >> 1) & helper_mask for flat in projected for row in flat)
    expected = {p & ~helper_mask for p in range(1 << n) if _allowed(raw, p)}
    actual = {v for v in range(1 << n) if not v & helper_mask and _allowed(projected, v)}
    assert actual == expected
    return stats


def _three_variable_flats():
    """Recover every flat by iterating literal intersections as point sets."""
    universe = frozenset(range(8))
    reps = {universe: ()}
    for linear in range(1, 8):
        for bit in range(2):
            half = {x for x in universe if (linear & x).bit_count() % 2 == bit}
            for space, rows in list(reps.items()):
                sub = space & half
                if sub not in reps:
                    reps[sub] = rows + (2 * linear + bit,)
    assert len(reps) == 52
    return reps


def _square_census():
    # In an affine plane of order two, every pair of distinct points is a line.
    fibers = [frozenset(s) for size in (1, 2) for s in combinations(range(4), size)]
    census = {}
    for size in range(1, len(fibers) + 1):
        for family in combinations(fibers, size):
            if len(frozenset().union(*family)) != 4:
                continue
            if any(len(frozenset().union(*(family[:i] + family[i+1:]))) == 4
                   for i in range(size)):
                continue
            lines = sum(len(f) == 2 for f in family)
            shape = (lines, size - lines)
            census[shape] = census.get(shape, 0) + 1
    assert census == {(2, 0): 3, (3, 0): 4, (2, 1): 12, (1, 2): 6, (0, 4): 1}
    return census


def _square_comparison(num_lines, num_points):
    # Two helper bits, two visible RHS bits and one active-domain bit.
    normals = (1, 2, 3)
    visible = (4, 8, 12)
    domain_row = 2 * 16
    raw = []
    for i in range(num_lines):
        row = 2 * (normals[i % 3] | visible[i % 3]) + (i // 3 % 2)
        raw.append((domain_row, row))
    for i in range(num_points):
        x = 2 * (1 | visible[i % 3]) + (i & 1)
        y = 2 * (2 | visible[(i + 1) % 3]) + (i >> 1 & 1)
        raw.append((domain_row, x, y))
    oracle = {v for v in range(0, 32, 4) if any(_allowed(raw, v | w) for w in range(4))}
    traces = []
    for flag in (False, True):
        output, stats = project_rank_bounded(raw, 5, (0, 1), 2, specialize_square=flag)
        assert {v for v in range(0, 32, 4) if _allowed(output, v)} == oracle
        traces.append((stats.subset_tests, stats.four_member_subsets,
                       stats.pattern_tests, len(output)))
    assert traces[0][1] == comb(num_lines + num_points, 4)
    assert traces[1][1] == comb(num_points, 4)
    return traces


def checks():
    cases = 0
    for rank in range(3):
        admissible = []
        for space, rows in _three_variable_flats().items():
            if space:
                vis = next(iter(space)) & 4
                fiber_size = sum(p & 4 == vis for p in space)
                if 2 - (fiber_size.bit_length() - 1) > rank:
                    continue
            admissible.append(rows)
        for size in range(3):
            for subset in combinations(admissible, size):
                _compare(subset, 3, (0, 1), rank)
                cases += 1
    rng = Random(248133)
    for trial in range(256):
        n = rng.randrange(2, 6)
        h = rng.randrange(min(3, n) + 1)
        helpers = tuple(rng.sample(range(n), h))
        r = rng.randrange(h + 1)
        helper_mask = sum(1 << v for v in helpers)
        visible = ((1 << n) - 1) ^ helper_mask
        raw = []
        for _ in range(rng.randrange(6)):
            normals = [rng.randrange(1 << n) & helper_mask for _ in range(r)]
            rows = []
            for _ in range(rng.randrange(5)):
                normal = rng.randrange(1 << n) & visible
                for vector in normals:
                    if rng.randrange(2):
                        normal ^= vector
                rows.append(2 * normal + rng.randrange(2))
            raw.append(rows)
        _compare(raw, n, helpers, r)

    for h in (1, 2, 3):
        singletons = [tuple((1 << (i + 1)) | (point >> i & 1) for i in range(h))
                      for point in range(1 << h)]
        assert _compare(singletons, h, range(h), h).largest_witness_used == 1 << h
        for i in range(1 << h):
            assert _compare(singletons[:i] + singletons[i + 1:], h, range(h), h).emitted_conflicts == 0

    # All seven distinct F₂³ lines through zero. Each nonzero point is private.
    lines = [tuple(2 * a for a in range(1, 8) if (a & d).bit_count() % 2 == 0)
             for d in range(1, 8)]
    stats = _compare(lines, 3, range(3), 2)
    assert stats.emitted_conflicts == 1 and stats.largest_witness_used == stats.subset_limit == 7
    for i in range(7):
        assert _compare(lines[:i] + lines[i + 1:], 3, range(3), 2).emitted_conflicts == 0

    # Three active rank-one flats force a conflict on one value of visible x₂.
    triangle = [(2 | 1,), (4 | 1,), (2 | 4 | 8,)]
    stats = _compare(triangle, 3, (0, 1), 1)
    assert stats.largest_witness_used == 3
    try:
        project_rank_bounded([(2, 4)], 2, (0, 1), 1)
    except ValueError as error:
        assert "rank exceeds" in str(error)
    else:
        raise AssertionError("accepted an instance above the supplied rank limit")
    print(f"{cases} exhaustive low-dimensional families and 256 seeded projections passed.")
    print("Private-point witnesses checked at (h,r,size) = (2,1,3), (3,2,7), (3,3,8).")
    print("Minimal covers of a square by (lines, points):", _square_census())
    print("lines points | generic vs specialized (subsets, quadruples, patterns, output flats)")
    for lines, points in ((6, 4), (1, 5), (0, 4)):
        print(lines, points, *_square_comparison(lines, points))


if __name__ == "__main__":
    checks()
