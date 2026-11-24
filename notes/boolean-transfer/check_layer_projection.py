"""Check signed homogeneous-layer projections on actual spliced directed graphs.

Run `python3 check_layer_projection.py` for n=2..5, k=3..6. No dependencies.
Coordinates of source monomials are arcs of the (n+k)-vertex graph, including
cross-block arcs after the head swap. An absent arc is specialized to zero.
"""

from argparse import ArgumentParser
from itertools import permutations
from math import factorial


def arc_bit(size, u, v):
    return 1 << (size * u + v)


def splice_graph(n, k):
    """Return adjacency, source-to-input coordinates and the negative source arc."""
    size = n + k
    adjacency = [[] for _ in range(size)]
    visible = {}

    def redirected(v):
        if v == 0:
            return n
        if v == n:
            return 0
        return v

    for u in range(n):
        for v in range(n):
            if u != v:
                w = redirected(v)
                adjacency[u].append(w)
                visible[arc_bit(size, u, w)] = arc_bit(n, u, v)
    for i in range(k):
        for step in (-1, 1):
            adjacency[n + i].append(redirected(n + (i + step) % k))
    # The reverse arc from gadget vertex 1 to gadget vertex 0 becomes a cross arc.
    negative = arc_bit(size, n + 1, 0)
    assert 0 in adjacency[n + 1] and negative not in visible
    return adjacency, visible, negative


def tour_masks(adjacency):
    """Traverse the source graph from root 0, using every vertex exactly once."""
    size = len(adjacency)
    all_vertices = (1 << size) - 1

    def walk(u, visited, mask):
        if visited == all_vertices:
            if 0 in adjacency[u]:
                yield mask | arc_bit(size, u, 0)
            return
        for v in adjacency[u]:
            if not visited & (1 << v):
                yield from walk(v, visited | (1 << v), mask | arc_bit(size, u, v))

    return list(walk(0, 1, 0))


def decision_layer(tours, degree):
    """Canonical integer multilinear coefficients at the specified degree.

    Adding one more tour monomial T changes the union indicator P to P+T−PT.
    In the Boolean quotient, product of two squarefree monomials takes the union
    of their masks. Future unions never decrease support size, so terms larger
    than `degree` can be dropped at every step without changing this layer.
    """
    coefficients = {}
    for tour in tours:
        if tour.bit_count() > degree:
            continue
        updated = coefficients.copy()
        updated[tour] = updated.get(tour, 0) + 1
        for earlier, coeff in coefficients.items():
            union = earlier | tour
            if union.bit_count() <= degree:
                updated[union] = updated.get(union, 0) - coeff
        coefficients = {mask: value for mask, value in updated.items() if value}
    return {mask: value for mask, value in coefficients.items() if mask.bit_count() == degree}


def decision_layer_mod_two(tours, degree):
    """Execute the same Boolean OR update independently as symmetric differences."""
    support = set()
    for tour in tours:
        if tour.bit_count() > degree:
            continue
        delta = {tour}
        for earlier in support:
            union = earlier | tour
            if union.bit_count() <= degree:
                delta.symmetric_difference_update((union,))
        support ^= delta
    return {mask for mask in support if mask.bit_count() == degree}


def image_mask(mask, visible):
    image = 0
    for source, target in visible.items():
        if source & mask:
            image |= target
    return image


def project_integer(layer, visible, negative):
    result = {}
    for mask, coeff in layer.items():
        target = image_mask(mask, visible)
        sign = -1 if mask & negative else 1
        result[target] = result.get(target, 0) + sign * coeff
    return {mask: value for mask, value in result.items() if value}


def project_mod_two(support, visible):
    result = set()
    for mask in support:
        result.symmetric_difference_update((image_mask(mask, visible),))
    return result


def formal_hc(n):
    """Build the target from cyclic vertex orders independently of the source DFS."""
    result = {}
    for middle in permutations(range(1, n)):
        order = (0,) + middle + (0,)
        edges = sum(arc_bit(n, a, b) for a, b in zip(order, order[1:]))
        result[edges] = 1
    return result


def check(n, k):
    adjacency, visible, negative = splice_graph(n, k)
    tours = tour_masks(adjacency)
    assert len(set(tours)) == len(tours) == 2 * factorial(n - 1)
    assert all(mask.bit_count() == n + k for mask in tours)
    degree = n + 2 * k
    layer = decision_layer(tours, degree)
    mod_two_layer = decision_layer_mod_two(tours, degree)
    assert mod_two_layer == {mask for mask, coeff in layer.items() if coeff % 2}
    target = formal_hc(n)
    assert project_integer(layer, visible, negative) == target, (n, k, 'signed projection')
    assert project_mod_two(mod_two_layer, visible) == set(target), (n, k, 'F2 projection')
    all_positive = project_integer(layer, visible, 0)
    assert all(all_positive.get(mask) == -1 for mask in target), (n, k, 'all-positive control')
    assert all_positive != target
    return len(tours), len(layer), len(mod_two_layer), len(target)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=5)
    parser.add_argument('--max-k', type=int, default=6)
    args = parser.parse_args()
    if not __debug__:
        parser.error('run with Python assertions enabled')
    if args.max_n < 2 or args.max_k < 3:
        parser.error('need max-n >= 2 and max-k >= 3')
    print('n k source_tours integer_layer_terms F2_layer_terms target_terms')
    for n in range(2, args.max_n + 1):
        for k in range(3, args.max_k + 1):
            print(n, k, *check(n, k), flush=True)
