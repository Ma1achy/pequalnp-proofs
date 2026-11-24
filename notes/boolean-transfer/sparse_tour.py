"""Decide the directed-tour predicate restricted to graphs with at most m+k arcs.

A graph is supplied as m*(m-1) read-only bytes, each 0 or 1, in row-major order
with the diagonal omitted (m >= 1). Working memory of sparse_tour is O(k+log m)
bits in the bit model, excluding the read-only input. The exhaustive test harness
stores truth tables and uses an independent permutation-based oracle.
"""

from itertools import permutations
from math import comb


def _degree(graph, start, stride):
    count = 0
    for cell in range(start, start + stride):
        count += graph[cell]
    return count


def _successor(graph, m, vertex, choices):
    """Recompute the bit offset by scanning rows, then select the requested arc."""
    stride = m - 1
    start = offset = 0
    for _ in range(vertex):
        degree = _degree(graph, start, stride)
        offset += (degree-1).bit_length()
        start += stride
    degree = _degree(graph, start, stride)
    width = (degree-1).bit_length()
    rank = (choices >> offset) & ((1 << width)-1)
    # Codes past the last arc are unused, including those of non-power-of-two degrees.
    if rank >= degree:
        return -1
    for slot in range(stride):
        if graph[start+slot]:
            if rank == 0:
                return slot + int(slot >= vertex)  # Reinsert the omitted diagonal.
            rank -= 1
    raise AssertionError("successor rank outside row")


def sparse_tour(graph, m, k):
    """Return whether this graph has <=m+k arcs and a directed Hamiltonian cycle.

    On a graph with all outdegrees d_v >= 1, ceil(log2(d_v)) <= d_v-1.
    Thus at most k choice bits suffice on an admitted input. For each code,
    following the chosen successors from 0 returns to 0 for the first time
    exactly at step m iff that successor system contains one spanning tour.

    All graph accesses are sequential row scans, with no stored successor,
    offset or visited arrays. Counters and addresses take O(log(m+1)) bits.
    The code, its enumeration bound, and bit-extraction temporaries use O(k+1)
    bits. Each code makes at most m traversals of an O(m²)-cell prefix.
    """
    if m < 1 or k < 0 or len(graph) != m*(m-1):
        raise ValueError("expected a positive vertex count, nonnegative budget and loopless encoding")
    if any(byte not in (0, 1) for byte in graph):
        raise ValueError("each adjacency byte must be a bit")
    stride = m - 1
    total = width = 0
    for vertex in range(m):
        degree = _degree(graph, vertex*stride, stride)
        total += degree
        if total > m+k or degree == 0:
            return False
        width += (degree-1).bit_length()
    assert width <= k
    for choices in range(1 << width):
        vertex = 0
        for step in range(1, m+1):
            vertex = _successor(graph, m, vertex, choices)
            if vertex == -1:
                break
            if vertex == 0:
                if step == m:
                    return True
                break
    return False


def _oracle_tours(m):
    """Each cyclic vertex ordering rooted at 0 gives one tour incidence mask."""
    arcs = [(v, w) for v in range(m) for w in range(m) if v != w]
    masks = []
    for tail in permutations(range(1, m)):
        order = (0, *tail)
        tour = {(order[i], order[(i+1) % m]) for i in range(m)}
        if tour.issubset(arcs):
            masks.append(sum(1 << arcs.index(edge) for edge in tour))
    return masks


def _bytes(mask, variables):
    return bytes((mask >> i) & 1 for i in range(variables))


def _pad_root(graph, m, t):
    """Replace vertex 0 by the path (0, m, ..., m+t-1), keeping 0 as entry."""
    path = (0, *range(m, m+t))
    edges = set(zip(path, path[1:]))
    original_arcs = ((v, w) for v in range(m) for w in range(m) if v != w)
    for (v, w), present in zip(original_arcs, graph, strict=True):
        if present:
            edges.add((path[-1] if v == 0 else v, w))
    n = m+t
    return bytes((v, w) in edges for v in range(n) for w in range(n) if v != w)


def check_padding(m):
    """Compare independent tour counts before and after root-path padding."""
    variables = m*(m-1)
    original_tours = _oracle_tours(m)
    comparisons = 0
    for t in (0, 1, 2):
        padded_tours = _oracle_tours(m+t)
        for mask in range(1 << variables):
            padded = _pad_root(_bytes(mask, variables), m, t)
            assert sum(padded)-(m+t) == mask.bit_count()-m
            padded_mask = sum(bit << i for i, bit in enumerate(padded))
            assert sum(mask & tour == tour for tour in original_tours) == sum(
                padded_mask & tour == tour for tour in padded_tours
            )
            comparisons += 1
    return comparisons


def _anf(table):
    """Full F₂ subset Möbius transform, independent of the bounded-space solver."""
    result = bytearray(table)
    stride = 1
    while stride < len(result):
        for block in range(0, len(result), 2*stride):
            for low in range(block, block+stride):
                result[low+stride] ^= result[low]
        stride *= 2
    return result


def check(m):
    variables = m*(m-1)
    tour_masks = _oracle_tours(m)
    full = bytearray(any(g & tour == tour for tour in tour_masks) for g in range(1 << variables))
    full_anf = _anf(full)
    comparisons = prefix_coefficients = sharp_points = 0
    for k in range(max(variables-m, 0)+1):
        cutoff = m+k
        decisions = bytearray()
        for mask, contains in enumerate(full):
            answer = sparse_tour(_bytes(mask, variables), m, k)
            assert answer == (bool(contains) and mask.bit_count() <= cutoff)
            decisions.append(answer)
            comparisons += 1
        coefficients = _anf(decisions)
        differences = {mask for mask, (a, b) in enumerate(zip(coefficients, full_anf)) if a != b}
        assert all(mask.bit_count() > cutoff for mask in differences)
        prefix_coefficients += sum(comb(variables, d) for d in range(min(variables, cutoff)+1))
        if cutoff < variables:
            # On the next layer, all proper subsets agree so the coefficient
            # difference is exactly the truth-table difference at the set itself.
            next_layer = {g for g, value in enumerate(full) if value and g.bit_count() == cutoff+1}
            assert next_layer and {g for g in differences if g.bit_count() == cutoff+1} == next_layer
            sharp_points += len(next_layer)
        else:
            assert not differences
    return comparisons, prefix_coefficients, sharp_points


def main():
    if not __debug__:
        raise RuntimeError("run with Python assertions enabled")
    for m in (1, 2, 3, 4):
        cases, coefficients, differences = check(m)
        padded = check_padding(m)
        print(f"m={m}: {cases} graph/budget decisions, {coefficients} prefix coefficients,"
              f" {differences} first-disagreement coefficients, {padded} padding checks")
    # A four-tour with two extra arcs sits one above cutoff m+k=5.
    rows = bytes([1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0])
    mask = sum(bit << i for i, bit in enumerate(rows))
    assert sum(rows) == 6 and any(mask & t == t for t in _oracle_tours(4))
    assert not sparse_tour(rows, 4, 1) and sparse_tour(rows, 4, 2)
    print("Sharp six-arc witness on four vertices: rejected at k=1, accepted at k=2.")


if __name__ == "__main__":
    main()
