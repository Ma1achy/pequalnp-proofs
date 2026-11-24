"""Check partially formal tour polynomials on every four-vertex fiber."""

from collections import Counter
from itertools import combinations, permutations


def submasks(mask):
    subset = mask
    while True:
        yield subset
        if subset == 0:
            return
        subset = (subset - 1) & mask


def four_vertex_data():
    vertices = range(4)
    edges = [(i, j) for i in vertices for j in vertices if i != j]
    bit = {edge: 1 << index for index, edge in enumerate(edges)}
    tours = []
    for tail in permutations(range(1, 4)):
        order = (0, *tail)
        tours.append(sum(bit[edge] for edge in zip(order, order[1:] + order[:1])))
    rows = [sum(bit[i, j] for j in vertices if i != j) for i in vertices]
    stars = [sum(value for edge, value in bit.items() if i in edge) for i in vertices]
    return tours, rows, stars


def allowed_guarded_arcs(pattern, guarded, rows):
    """Force the unique selected outgoing arc at each tail in the pattern."""
    allowed = guarded
    for row in rows:
        selected = pattern & row
        if selected:
            assert selected.bit_count() == 1
            allowed &= ~row
    return allowed


def check():
    tours, rows, stars = four_vertex_data()
    full = (1 << 12) - 1
    covers = [(0, 0)]
    for star in stars:
        covers += [(size + 1, covered | star) for size, covered in covers]

    for row, star in zip(rows, stars):
        assert len({tour & row for tour in tours}) == 3
        assert len({tour & star for tour in tours}) == 6

    fiber_count = 0
    allowed_flips = 0
    for formal in range(full + 1):
        guarded = full ^ formal
        patterns = {tour & formal for tour in tours}
        h = min(size for size, covered in covers if formal & covered == formal)
        assert len(patterns) <= 3 ** (2 * h)
        assert all(pattern.bit_count() <= 2 * h for pattern in patterns)
        restrictions = {pattern: allowed_guarded_arcs(pattern, guarded, rows)
                        for pattern in patterns}

        for present in submasks(guarded):
            surviving = [tour for tour in tours if tour & guarded & ~present == 0]
            counts = Counter(tour & formal for tour in surviving)
            generators = {(first | second) & formal
                          for first, second in combinations(surviving, 2)}

            for pattern, allowed in restrictions.items():
                graph = (present & allowed) | pattern
                k = counts[pattern]
                assert k == sum(tour & graph == tour for tour in tours)
                answers = [int(k == 1)] if k < 2 else [0, 1]
                for answer in answers:
                    if answer != k % 2:
                        assert any(pattern & g == g for g in generators)
                        assert pattern in generators
                        allowed_flips += 1
            fiber_count += 1

    assert fiber_count == 3 ** 12
    assert allowed_flips == 5525
    print(f"{fiber_count:,} fibers verified; "
          f"{allowed_flips:,} allowed coefficient flips certified")


if __name__ == "__main__":
    check()
