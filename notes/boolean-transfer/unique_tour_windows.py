"""Exhaustive checks of rooted unique-tour windows in loopless directed graphs."""

from collections import Counter
from itertools import permutations
from math import comb, factorial


NO_OWNER = 255


def arc(i, j, n):
    """One arc in a row-major loopless matrix, packed into an integer."""
    assert i != j
    return 1 << (i * (n - 1) + (j if j < i else j - 1))


def subsets(mask):
    subset = mask
    while True:
        yield subset
        if subset == 0:
            return
        subset = (subset - 1) & mask


def templates(n):
    for permutation in permutations(range(1, n)):
        order = (0, *permutation)
        tour = sum(arc(i, j, n) for i, j in zip(order, order[1:] + order[:1]))
        backward = sum(arc(order[j], order[i], n) for j in range(n) for i in range(j))
        yield tour, backward & ~tour


def greedy(n, arcs):
    current = 0
    visited = 1
    row_mask = (1 << (n - 1)) - 1
    for _ in range(n - 1):
        packed_row = (arcs >> (current * (n - 1))) & row_mask
        below = (1 << current) - 1
        neighbors = (packed_row & below) | ((packed_row & ~below) << 1)
        choices = neighbors & ~visited
        if choices.bit_count() != 1:
            return False
        current = choices.bit_length() - 1
        visited |= choices
    return bool(arcs & arc(current, 0, n))


def check_certificates(n, windows, owner, promised):
    """Check every signed literal cube that implies acceptance on the promise."""
    edge_count = n * (n - 1)
    graph_count = 1 << edge_count
    full = (1 << graph_count) - 1
    positive = sum(1 << graph for graph in range(graph_count) if owner[graph] != NO_OWNER)
    negative = sum(1 << graph for graph in range(graph_count)
                   if promised[graph] and owner[graph] == NO_OWNER)
    intervals = [sum(1 << (tour | opt) for opt in subsets(optional))
                 for tour, optional in windows]
    ones = [sum(1 << graph for graph in range(graph_count) if graph & (1 << j))
            for j in range(edge_count)]
    covered = [0] * len(windows)
    mass = [0] * len(windows)
    cubes = 0
    active_certificates = 0

    def visit(j, cylinder, present, fixed):
        nonlocal cubes, active_certificates
        if j < edge_count:
            bit = 1 << j
            visit(j + 1, cylinder, present, fixed)
            visit(j + 1, cylinder & ~ones[j], present, fixed | bit)
            visit(j + 1, cylinder & ones[j], present | bit, fixed | bit)
            return
        cubes += 1
        active = cylinder & positive
        if not active or cylinder & negative:
            return
        active_certificates += 1
        witness = (active & -active).bit_length() - 1
        index = owner[witness]
        tour, optional = windows[index]
        assert present & tour == tour
        assert active & ~intervals[index] == 0
        free_optional = optional.bit_count() - (optional & fixed).bit_count()
        assert active.bit_count() == 1 << free_optional
        covered[index] |= active
        mass[index] += active.bit_count()

    visit(0, full, 0, 0)
    assert cubes == 3 ** edge_count
    assert covered == intervals
    assert all(total >= interval.bit_count() for total, interval in zip(mass, intervals))
    return cubes, active_certificates


def check(n):
    edge_count = n * (n - 1)
    graph_count = 1 << edge_count
    all_edges = graph_count - 1
    windows = list(templates(n))
    tours = [tour for tour, _ in windows]
    h = comb(n, 2) - 1
    assert len(set(tours)) == factorial(n - 1)
    # Independent tour count for every ambient graph, by rooted cyclic order.
    count = bytearray(graph_count)
    for tour in tours:
        for extra in subsets(all_edges ^ tour):
            count[tour | extra] += 1

    owner = bytearray([NO_OWNER]) * graph_count
    promised = bytearray(graph_count)
    layers = Counter()
    comparisons = 0
    for index, (tour, optional) in enumerate(windows):
        assert tour.bit_count() == n and optional.bit_count() == h and not tour & optional
        for graph in subsets(tour | optional):
            promised[graph] = 1
            assert count[graph] == int(graph & tour == tour)
            comparisons += 1
        for extra in subsets(optional):
            graph = tour | extra
            assert owner[graph] == NO_OWNER
            owner[graph] = index
            layers[graph.bit_count() - n] += 1

    assert layers == {s: len(tours) * comb(h, s) for s in range(h + 1)}
    for graph, index in enumerate(owner):
        assert greedy(n, graph) == (index != NO_OWNER)
    if n >= 3:
        assert count[all_edges] > 0 and not greedy(n, all_edges)
    if n <= 4:
        cubes, active = check_certificates(n, windows, owner, promised)
        print(f'n={n}: {cubes:,} signed cubes, {active:,} active certificates')
    print(f'n={n}: {graph_count:,} ambient graphs, {comparisons:,} template subgraphs, '
          f'{sum(layers.values()):,} graphs in the disjoint positive intervals')


if __name__ == '__main__':
    for n in range(2, 6):
        check(n)
