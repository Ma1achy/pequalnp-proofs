"""Reproduce the exact monotone boundary, small rewrites and optional SAT instance for L-meta-1494.

python arc_window_search.py
python arc_window_search.py --cnf /tmp/incidence-63.cnf --size 63

The SAT encoding tests *unrestricted* monotone fan-in-two circuits on this
boundary, with free operand symbols false and true. In the forward direction
these symbols represent constants, invalid old wire reads, and nullary gates.
A unary gate is a doubled argument. A short program is padded by copies and
its last gate is the output. In the reverse direction constant-propagate every
gate: a constant operand makes the result a literal constant or a projection,
with no gate required. The final boundary contains both labels, so its output
is nonconstant. The remaining binary gates are legal and cost at most s.

At least one wire selector per side is enough: if multiple selectors are set,
all selected wires have exactly the same truth vector, so any one may be kept.
No claims about SAT or UNSAT follow from emitting the instance alone.
"""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path

N = 13
INC = tuple(sum(1 << ((w+d) % N) for d in (0, 1, 3, 9)) for w in range(N))
FULL = (1 << N)-1


def boundary():
    yes = [1 << p | 1 << (N+w) for w in range(N) for p in range(N) if INC[w] >> p & 1]
    no = []
    populations = Counter()
    forbidden = 0
    for points in range(1 << N):
        if any((line & points).bit_count() > 2 for line in INC):
            continue
        avoid = sum(1 << w for w, line in enumerate(INC) if not line & points)
        no.append(points | (avoid << N))
        populations[points.bit_count(), avoid.bit_count()] += 1
        forbidden += 1 << avoid.bit_count()
    assert len(yes) == len(set(yes)) == 52
    assert populations == {(0, 13): 1, (1, 9): 13, (2, 6): 78, (3, 4): 234, (4, 3): 234}
    assert forbidden == 25456
    assert all(a & b != a for a in no for b in no if a != b)
    assert all(a & b != a for a in yes for b in no)
    # No satisfying incident pair is redundant: the OR of all other pairs
    # rejects that pair and passes the other rows. Likewise, adding any one
    # maximal negative's monomial to incidence violates just that negative.
    # A genuine monotone extension inside the promise sandwich. Its extra
    # minimal true input has no lines and three points on the line numbered 0.
    triple = (1 << 0) | (1 << 1) | (1 << 3)
    def exact(row):
        return any(row & edge == edge for edge in yes)
    def extension(row):
        return exact(row) or row & triple == triple
    assert not exact(triple) and extension(triple)
    assert all(extension(row) for row in yes) and not any(extension(row) for row in no)
    print(f"positive pairs={len(yes)}, maximal negative rows={len(no)}, forbidden assignments={forbidden}")
    print("incidence OR the collinear point triple {0,1,3} passes all boundary rows and differs on that triple")
    return yes, no


def star_circuit(by_line, balanced):
    gates = []
    def gate(op, left, right):
        gates.append((op, left, right))
        return 2*N + len(gates)-1

    def join(wires):
        while len(wires) > 1:
            if balanced:
                wires = [gate('or', wires[j], wires[j+1]) for j in range(0, len(wires)-1, 2)] + (
                    wires[-1:] if len(wires) % 2 else [])
            else:
                wires = [gate('or', wires[0], wires[1])] + wires[2:]
        return wires[0]

    terms = []
    for i in range(N):
        nbrs = ([p for p in range(N) if INC[i] >> p & 1] if by_line else
                [N+w for w in range(N) if INC[w] >> i & 1])
        center = N+i if by_line else i
        terms.append(gate('and', center, join(nbrs)))
    join(terms)
    return gates


def values(inputs, gates, forced=None):
    wires = inputs.copy()
    for op, a, b in gates:
        if forced is not None and len(wires) == forced[0]:
            val = forced[1]
        else:
            val = wires[a] & wires[b] if op == 'and' else wires[a] | wires[b]
        wires.append(val)
    return wires


def local_rewrites(yes, no):
    rows = yes + no
    inputs = [sum(1 << j for j, row in enumerate(rows) if row >> i & 1) for i in range(2*N)]
    universe = (1 << len(rows))-1
    expected = (1 << len(yes))-1
    tried = 0
    for by_line in (True, False):
        for balanced in (True, False):
            gates = star_circuit(by_line, balanced)
            wires = values(inputs, gates)
            assert len(gates) == 64 and wires[-1] == expected
            users = Counter(i for _, a, b in gates for i in (a, b))
            for i, (_, a, b) in enumerate(gates):
                root = 2*N+i
                low = values(inputs, gates, (root, 0))[-1]
                high = values(inputs, gates, (root, universe))[-1]
                care = low ^ high
                aim = wires[root] & care
                # Replace one gate by a predecessor, or remove a singly-used
                # child together with its parent and replace both by one gate.
                for w in range(root):
                    tried += 1
                    assert wires[w] & care != aim
                for child in {a, b}:
                    if child < 2*N or users[child] != 1:
                        continue
                    allowed = [w for w in range(root) if w != child]
                    for l, r in combinations_with_replacement(allowed, 2):
                        tried += 2
                        assert (wires[l] & wires[r] & care) != aim
                        assert ((wires[l] | wires[r]) & care) != aim
    print(f"four 64-gate star constructions pass; {tried} restricted local reductions rejected")


def sat_counts(size, inputs, rows):
    # gate op, operand selectors, left/right/output row values
    variables = size*(1 + 2*(inputs+2) + 3*rows) + size*(size-1)
    clauses = size*(2 + (2*(inputs+2)+6)*rows) + 2*rows*size*(size-1) + rows
    return variables, clauses


def write_cnf(path, size, inputs, yes, no):
    rows = yes + no
    nv, nc = sat_counts(size, inputs, len(rows))
    used = 0
    clauses = 0
    def fresh(k):
        nonlocal used
        used += k
        return list(range(used-k+1, used+1))
    with Path(path).open("w") as out:
        print("p cnf", nv, nc, file=out)
        def clause(*lits):
            nonlocal clauses
            clauses += 1
            out.write(" ".join(map(str, lits)) + " 0\n")
        previous = []
        for _ in range(size):
            op, = fresh(1)
            sides = []
            for _ in (0, 1):
                selectors = fresh(inputs+2+len(previous))
                clause(*selectors)
                value = fresh(len(rows))
                sides.append(value)
                for j, choose in enumerate(selectors):
                    for r, row in enumerate(rows):
                        if j < inputs+2:
                            truth = (row >> j & 1) if j < inputs else j-inputs
                            clause(-choose, value[r] if truth else -value[r])
                        else:
                            other = previous[j-inputs-2][r]
                            clause(-choose, -value[r], other)
                            clause(-choose, value[r], -other)
            result = fresh(len(rows))
            for l, r, z in zip(*sides, result):
                clause(op, -z, l)
                clause(op, -z, r)
                clause(op, z, -l, -r)
                clause(-op, z, -l)
                clause(-op, z, -r)
                clause(-op, -z, l, r)
            previous.append(result)
        for i, z in enumerate(previous[-1]):
            clause(z if i < len(yes) else -z)
    assert (used, clauses) == (nv, nc)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--cnf", type=Path)
    parser.add_argument("--size", type=int, default=63)
    args = parser.parse_args()
    if not __debug__ or args.size < 1:
        parser.error("need positive size and assertions enabled")
    yes, no = boundary()
    local_rewrites(yes, no)
    variables, clauses = sat_counts(args.size, 2*N, len(yes)+len(no))
    print(f"unrestricted s={args.size} exact SAT encoding: {variables} variables, {clauses} clauses")
    if args.cnf:
        write_cnf(args.cnf, args.size, 2*N, yes, no)
