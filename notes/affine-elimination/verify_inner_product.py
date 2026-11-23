"""Independent exhaustive checks of flat covers and projected inner-product gadgets."""

import argparse
import json
from itertools import combinations, product


def submasks(mask):
    submask = mask
    while True:
        yield submask
        if submask == 0:
            return
        submask = (submask - 1) & mask


def affine_flats(dimension):
    """Yield (dimension, points) once per nonempty flat using unique RREF bases."""
    ambient = (1 << dimension) - 1
    for rank in range(dimension + 1):
        for pivots in combinations(range(dimension), rank):
            pivot_mask = sum(1 << pivot for pivot in pivots)
            free = ambient ^ pivot_mask
            options = [
                [1 << pivot | tail for tail in submasks(free & ~((2 << pivot) - 1))]
                for pivot in pivots
            ]
            for basis in product(*options):
                span = [0]
                for row in basis:
                    span += [point ^ row for point in span]
                for representative in submasks(free):
                    yield rank, tuple(representative ^ point for point in span)


def check_flats(k):
    split = 1 << k
    bad = {
        (x << k) | y for x in range(split) for y in range(split)
        if (x & y).bit_count() % 2
    }
    cover = [
        {(s << k) | y for y in range(split) if (s & y).bit_count() % 2}
        for s in range(1, split)
    ]
    assert set.union(*cover) == bad
    assert sum(map(len, cover)) == len(bad)
    flat_count = 0
    inside_by_dimension = [0] * (2 * k + 1)
    for dim, flat in affine_flats(2 * k):
        flat_count += 1
        if bad.issuperset(flat):
            inside_by_dimension[dim] += 1
    max_dim = max(i for i, count in enumerate(inside_by_dimension) if count)
    assert max_dim == k - 1
    assert len(bad) == len(cover) * (1 << max_dim)
    return flat_count, len(bad), inside_by_dimension


def gate_bits(i):
    x = 1 << (3 * i)
    return x, x << 1, x << 2


def projected_flats(k, remaining):
    """An explicit list of forbidden affine systems. Each row is (mask, rhs)."""
    local = []
    detached = []
    guards = []
    t_parity = 0
    empty = False
    for i in range(k):
        x, y, t = gate_bits(i)
        if remaining & t:
            t_parity |= t
            inputs = [bit for bit in (x, y) if remaining & bit]
            for bit in inputs:
                local.append([(t, 1), (bit, 0)])
            if len(inputs) == 2:
                local.append([(x, 1), (y, 1), (t, 0)])
        elif remaining & x and remaining & y:
            detached.append((x, y))
        elif remaining & (x | y):
            guards.append((remaining & (x | y), 0))
        else:
            empty = True
    if empty:
        return local
    for s in product(range(2), repeat=len(detached)):
        rows = list(guards)
        mask = t_parity
        for (x, y), value in zip(detached, s):
            rows.append((x, value))
            if value:
                mask |= y
        if mask:
            local.append(rows + [(mask, 1)])
    return local


def check_projections(k):
    model_set = set()
    for values in product(range(2), repeat=2 * k):
        bits = parity = 0
        for i in range(k):
            x, y, t = gate_bits(i)
            a, b = values[2 * i:2 * i + 2]
            if a:
                bits |= x
            if b:
                bits |= y
            if a & b:
                bits |= t
                parity ^= 1
        if parity == 0:
            model_set.add(bits)
    checks = 0
    for remaining in range(1 << (3 * k)):
        expected = {model & remaining for model in model_set}
        forbidden = projected_flats(k, remaining)
        for assignment in submasks(remaining):
            bad = any(all(
                (assignment & mask).bit_count() % 2 == rhs
                for mask, rhs in flat
            ) for flat in forbidden)
            assert (not bad) == (assignment in expected), (k, remaining, assignment)
            checks += 1
    return checks


def check_gate():
    for x, y in product(range(2), repeat=2):
        mux_extensions = [
            (t, u) for t, u in product(range(2), repeat=2)
            if (x or not t) and (not x or not u) and u == (t ^ y)
        ]
        assert mux_extensions == [(x & y, (x & y) ^ y)]
        wide_extensions = [
            (t, a, b) for t, a, b in product(range(2), repeat=3)
            if x == (t ^ a) and y == (t ^ b) and a + b + t <= 1
        ]
        assert wide_extensions == [(x & y, x ^ (x & y), y ^ (x & y))]


def check_mux(k):
    """Run the general eliminator on the 4k-variable gadget, retaining step metrics."""
    from flat_elimination import Counts, clause, encoded_bits, metrics, normalize, parity, project

    n = 4 * k
    raw = [parity(range(2 * k, 3 * k), 0)]
    for i in range(k):
        x, y, t, u = (i, i + k, i + 2 * k, i + 3 * k)
        raw.extend([clause(x + 1, -(t + 1)), clause(-(x + 1), -(u + 1)),
                    parity((u, t, y), 0)])
    counts = Counts()
    state = normalize(raw, n, counts)
    trace = [{"eliminated": None, **metrics(state, n), **counts.as_dict()}]
    order = [*range(3 * k, 4 * k), *range(2 * k, 3 * k), *range(2 * k)]
    for step, variable in enumerate(order, 1):
        counts = Counts()
        state = project(state, variable, n, counts)
        trace.append({"eliminated": variable, **metrics(state, n), **counts.as_dict()})
        if step == 2 * k:
            # Independent canonical comparison with the explicit disjoint cover.
            direct = []
            for x in range(1, 1 << k):
                rows = tuple((1 << (i + 1)) | ((x >> i) & 1) for i in range(k))
                direct.append((*rows, (x << (k + 1)) | 1))
            assert state == normalize(direct, n, Counts())
    assert not state
    if k > 1:
        prefix_sizes = [3 * k + 1 - j for j in range(k + 1)]
        prefix_sizes += [2 ** j + 2 * (k - j) for j in range(1, k)]
        prefix_sizes.append(2 ** k - 1)
    else:
        prefix_sizes = [3, 2, 1]
    assert [stage["flats"] for stage in trace[:2 * k + 1]] == prefix_sizes
    return {"k": k, "input_dense_bits": encoded_bits(raw, n), "stages": trace}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mux-trace", action="store_true", help="emit all mux stage metrics as JSON")
    args = parser.parse_args()
    mux_results = [check_mux(k) for k in range(1, 7)]
    if args.mux_trace:
        print(json.dumps(mux_results, indent=2))
        raise SystemExit
    check_gate()
    print("k | all nonempty flats | bad points | contained flats by dimension | cut/assignment checks")
    for k in (1, 2, 3):
        total, bad, histogram = check_flats(k)
        checks = check_projections(k)
        print(k, total, bad, histogram, checks, sep=" | ")

    print("k | mux input bits | flats after product elimination | peak flats | cut width | cut bits")
    for row in mux_results:
        k = row["k"]
        stages = row["stages"]
        cut = stages[2 * k]
        print(k, row["input_dense_bits"], cut["flats"], max(s["flats"] for s in stages),
              cut["max_clause_width"], cut["dense_encoded_bits"], sep=" | ")
