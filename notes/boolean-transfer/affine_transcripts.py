"""Check XOR/AND nonlinear input rank and weighted trellises for affine transcripts."""

from collections import defaultdict
from itertools import permutations
from random import Random


def parity(mask):
    return mask.bit_count() & 1


def insert(row, offset, basis):
    """Insert a binary equation (or span row with offset zero); report consistency."""
    while row:
        pivot = row.bit_length() - 1
        if pivot not in basis:
            basis[pivot] = (row, offset)
            return True
        known, constant = basis[pivot]
        row ^= known
        offset ^= constant
    return offset == 0


def rank(vectors):
    basis = {}
    for vector in vectors:
        insert(vector, 0, basis)
    return len(basis)


def in_span(vector, basis):
    while vector:
        entry = basis.get(vector.bit_length() - 1)
        if entry is None:
            return False
        vector ^= entry[0]
    return True


def normal_form(n, gates, output):
    """The XOR affine skeleton uses formal AND outputs in bits n,n+1,... ."""
    wires = [(1 << i, 0) for i in range(n)]
    operands = []
    for op, a, b in gates:
        if op == "const":
            value = (0, a)
        elif op == "xor":
            f, g = wires[a], wires[b]
            value = (f[0] ^ g[0], f[1] ^ g[1])
        elif op == "and":
            value = (1 << (n + len(operands)), 0)
            operands.append((wires[a], wires[b]))
        else:
            raise ValueError(op)
        wires.append(value)
    return operands, wires[output]


def run(n, gates, output, x):
    values = [(x >> i) & 1 for i in range(n)]
    for op, a, b in gates:
        if op == "const":
            value = a
        elif op == "xor":
            value = values[a] ^ values[b]
        elif op == "and":
            value = values[a] & values[b]
        else:
            raise ValueError(op)
        values.append(value)
    return values[output]


def affine_transcripts(n, gates, output):
    """Branch on the first operand of each remaining AND and on the output."""
    operands, end = normal_form(n, gates, output)
    xmask = (1 << n) - 1

    def substitute(form, earlier):
        row, bit = form
        linear = row & xmask
        previous = row >> n
        while previous:
            low = previous & -previous
            old, constant = earlier[low.bit_length() - 1]
            linear ^= old
            bit ^= constant
            previous ^= low
        return linear, bit

    leaves = []

    def visit(i, earlier, equations):
        if i == len(operands):
            row, bit = substitute(end, earlier)
            complete = equations.copy()
            if insert(row, bit ^ 1, complete):
                leaves.append(tuple(complete.values()))
            return
        left, right = operands[i]
        row, bit = substitute(left, earlier)
        right_sub = substitute(right, earlier)
        for choice in (0, 1):
            branch = equations.copy()
            if insert(row, bit ^ choice, branch):
                visit(i + 1, earlier + [right_sub if choice else (0, 0)], branch)

    visit(0, [], {})
    return leaves


def add_terms(destination, source, bit, take, positive):
    for support, coeff in source.items():
        if take:
            destination[support | bit] += coeff
        else:
            destination[support] += coeff
            if not positive:
                destination[support | bit] -= coeff


def cell_polynomial(n, equations, order, positive=False):
    """Use only extendible partial syndromes. No full rank-2^r table is enumerated."""
    assert sorted(order) == list(range(n))
    rows = [row for row, _ in equations]
    target = sum(b << j for j, (_, b) in enumerate(equations))
    columns = [sum(((row >> i) & 1) << j for j, row in enumerate(rows)) for i in order]
    suffix = [{} for _ in range(n + 1)]
    for i in reversed(range(n)):
        suffix[i] = suffix[i + 1].copy()
        insert(columns[i], 0, suffix[i])
    if not in_span(target, suffix[0]):
        return {}, 0
    dp = {0: {0: 1}}
    prefix = {}
    width = 0
    for k, (coordinate, column) in enumerate(zip(order, columns)):
        insert(column, 0, prefix)
        width_here = len(prefix) + len(suffix[k + 1]) - len(suffix[0])
        width = max(width, width_here)
        following = {}
        for syndrome, value in dp.items():
            for take in (0, 1):
                new = syndrome ^ (column if take else 0)
                if in_span(new ^ target, suffix[k + 1]):
                    bucket = following.setdefault(new, defaultdict(int))
                    add_terms(bucket, value, 1 << coordinate, take, positive)
        dp = {s: {u: c for u, c in p.items() if c} for s, p in following.items()}
        assert len(dp) == 1 << width_here
    return dp[target], width


def check_partition(n, gates, output, rng):
    cells = affine_transcripts(n, gates, output)
    truth = [run(n, gates, output, x) for x in range(1 << n)]
    forms, (final, _) = normal_form(n, gates, output)
    xmask = (1 << n) - 1
    rows = [row & xmask for pair in forms for row, _ in pair]
    tabulated = {}
    for x, value in enumerate(truth):
        syndrome = tuple(parity(row & x) for row in rows)
        residual = value ^ parity(final & xmask & x)
        assert tabulated.setdefault(syndrome, residual) == residual
    assert len(tabulated) == 1 << rank(rows)
    assert all(sum(all(parity(row & x) == b for row, b in cell) for cell in cells) == v
               for x, v in enumerate(truth))
    coeffs = truth.copy()
    for i in range(n):
        for s in range(1 << n):
            if s & (1 << i):
                coeffs[s] -= coeffs[s ^ (1 << i)]
    order = list(range(n))
    rng.shuffle(order)
    widths = []
    for positive in (False, True):
        result = defaultdict(int)
        for cell in cells:
            poly, w = cell_polynomial(n, cell, order, positive)
            widths.append(w)
            for u, c in poly.items():
                result[u] += c
        values = truth if positive else coeffs
        assert all(result[s] == v for s, v in enumerate(values))
    return len(cells), max(widths, default=0)


def hc_circuit(vertices):
    arcs = [(i, j) for i in range(vertices) for j in range(vertices) if i != j]
    gates = []
    def gate(op, a, b):
        gates.append((op, a, b))
        return len(arcs) + len(gates) - 1
    terms = []
    for middle in permutations(range(1, vertices)):
        tour = (0, *middle, 0)
        inputs = [arcs.index(pair) for pair in zip(tour, tour[1:])]
        wire = inputs[0]
        for other in inputs[1:]:
            wire = gate("and", wire, other)
        terms.append(wire)
    output = terms[0]
    for t in terms[1:]:
        output = gate("xor", gate("xor", output, t), gate("and", output, t))
    return len(arcs), gates, output


def scan_hc(vertices):
    n, gates, out = hc_circuit(vertices)
    truth = [run(n, gates, out, x) for x in range(1 << n)]
    structures = []
    for a in range(1 << n):
        if all(truth[x] ^ truth[x ^ a] == truth[0] ^ truth[a] for x in range(1 << n)):
            structures.append(a)
    assert structures == [0]
    forms, _ = normal_form(n, gates, out)
    assert rank([row & ((1 << n) - 1) for pair in forms for row, _ in pair]) == n
    print(f"HC({vertices}): {n} essential arc coordinates, nonlinear input rank {n}, "
          f"only constant-derivative direction 0.")


def main():
    rng = Random(952)
    for _ in range(100):
        n = rng.randrange(1, 6)
        gates = []
        for i in range(rng.randrange(1, 10)):
            op = rng.choice(("xor", "and", "const"))
            if op == "const":
                gates.append((op, rng.randrange(2), 0))
            else:
                gates.append((op, rng.randrange(n + i), rng.randrange(n + i)))
        check_partition(n, gates, n + len(gates) - 1, rng)
    # Dense input parities are consumed nonlinearly, with another free parity
    # added at the output. The input rank remains two.
    dense = [("xor", 0, 1), ("xor", 6, 2), ("xor", 2, 3), ("xor", 8, 4),
             ("xor", 9, 5), ("and", 7, 10), ("xor", 0, 11)]
    forms, _ = normal_form(6, dense, 12)
    assert rank([row & 63 for pair in forms for row, _ in pair]) == 2
    check_partition(6, dense, 12, rng)
    for vertices in (2, 3, 4):
        scan_hc(vertices)
        if vertices <= 3:
            n, gates, out = hc_circuit(vertices)
            print("  accepting transcripts / maximum trellis dimension:",
                  check_partition(n, gates, out, rng))
    # Distinct cells x0=1 and x1=1 both accept 11. Signed polynomials sum
    # to X0+X1, and positive generating polynomials count 11 exactly twice.
    cells = [((1, 1),), ((2, 1),)]
    for positive in (False, True):
        polys = [cell_polynomial(2, cell, (0, 1), positive)[0] for cell in cells]
        total = {s: sum(p.get(s, 0) for p in polys) for s in range(4)}
        assert total == ({0: 0, 1: 1, 2: 1, 3: 2} if positive else
                         {0: 0, 1: 1, 2: 1, 3: 0})
        assert (total[3] if positive else sum(total.values())) % 2 == 0
    # In HC(3), bits 0,3,4 form 0->1->2->0 and the complementary
    # bits form the reverse tour. The third cell repeats part of the first.
    forward = ((1, 1), (8, 1), (16, 1))
    reverse = ((2, 1), (4, 1), (32, 1))
    cover = [forward, reverse, forward + ((2, 0),)]
    polynomials = [cell_polynomial(6, cell, range(6), True)[0] for cell in cover]
    low = {s: sum(p.get(s, 0) for p in polynomials) for s in range(64) if s.bit_count() == 3}
    assert {s: v for s, v in low.items() if v} == {25: 2, 38: 1}
    assert cell_polynomial(2, ((1, 1), (1, 0)), (1, 0))[0] == {}
    # Coordinate fixed independently along the entire path: rank 24, width zero,
    # positive polynomial one monomial. No exponential full syndrome scan.
    p, w = cell_polynomial(24, [(1 << j, j % 2) for j in range(24)], range(24), True)
    assert w == 0 and p == {sum(1 << j for j in range(1, 24, 2)): 1}
    print("Passed 100 transcript partitions, overlap, contradiction and rank-24/width-0 tests.")


if __name__ == "__main__":
    main()
