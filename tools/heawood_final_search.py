#!/usr/bin/env python3
"""Exact monotone Heawood synthesis on one orbit of private final-gate witnesses.

Usage: python heawood_final_search.py --op or --orbit 0 --seconds 60
Use --control to pin the known 27-gate star circuit in OR orbit 0.
Requires CaDiCaL on PATH, or pass its executable via --solver.
"""

import argparse
import itertools
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

if not __debug__:
    raise SystemExit('Run with Python assertions enabled (omit -O).')
sys.dont_write_bytecode = True

from heawood_final_orbits import EDGES, POSITIVE_ROWS, automorphisms, has_edge, negative_rows, orbit_table


class CNF:
    def __init__(self):
        self.vars = 0
        self.clauses = []

    def new(self):
        self.vars += 1
        return self.vars

    def one(self, choices):
        self.clauses.append(choices)
        self.clauses.extend([-a, -b] for a, b in itertools.combinations(choices, 2))

    def write(self, filename):
        with filename.open('w') as f:
            print('p cnf', self.vars, len(self.clauses), file=f)
            for clause in self.clauses:
                print(*clause, 0, file=f)


def star_control():
    gates = []

    def append(op, a, b):
        gates.append((op, min(a, b), max(a, b)))
        return 13 + len(gates)

    stars = []
    for p in range(7):
        x, y, z = [l for point, l in EDGES if point == p]
        stars.append(append('and', p, append('or', append('or', x, y), z)))

    def join(points):
        result = stars[points[0]]
        for p in points[1:]:
            result = append('or', result, stars[p])
        return result

    left = join([0, 2, 3])
    right = join([1, 4, 5, 6])
    gates.append(('or', left, right))
    assert len(gates) == 27
    return gates


def encode(budget, op, anchors, rows, pin=None):
    cnf = CNF()
    wires = [[cnf.new() for _ in rows] for _ in range(14+budget)]
    for v in range(14):
        for j, assignment in enumerate(rows):
            bit = wires[v][j]
            cnf.clauses.append([bit if assignment & (1 << v) else -bit])
    selectors = []
    for g in range(budget):
        i = 14+g
        left, right = ([cnf.new() for _ in range(i)] for _ in range(2))
        is_or = cnf.new()
        cnf.one(left)
        cnf.one(right)
        final = g == budget-1
        orientation = cnf.new() if final else None
        # Every essential nonconstant gate has two distinct predecessors after
        # removing constants and aliases. Short prefixes can be padded with
        # unused binary gates. The two sorted final operands may own either private row.
        for x in range(i):
            for y in range(x+1):
                cnf.clauses.append([-left[x], -right[y]])
        if final:
            # No primary is bounded above by the target (try its singleton),
            # or bounds it from above (try an edge missing that primary).
            for x in range(14):
                cnf.clauses.extend([[-left[x]], [-right[x]]])
            cnf.clauses.append([is_or if op == 'or' else -is_or])
        for j, _ in enumerate(rows):
            a, b = cnf.new(), cnf.new()
            out = wires[i][j]
            for choices, read in [(left, a), (right, b)]:
                for x, selector in enumerate(choices):
                    value = wires[x][j]
                    cnf.clauses.extend([[-selector, -value, read], [-selector, value, -read]])
            cnf.clauses.extend([
                [is_or, -a, -b, out], [is_or, a, -out], [is_or, b, -out],
                [-is_or, a, b, -out], [-is_or, -a, out], [-is_or, -b, out],
            ])
            if final:
                cnf.clauses.append([out if j < len(POSITIVE_ROWS) else -out])
                if j in anchors:
                    # For AND, a private row has value false at its owning input.
                    left_true = (j == anchors[0]) == (op == 'or')
                    a_lit = a if left_true else -a
                    b_lit = -b if left_true else b
                    cnf.clauses.extend([[-orientation, a_lit], [-orientation, b_lit],
                                        [orientation, -a_lit], [orientation, -b_lit]])
        if pin:
            action, x, y = pin[g]
            cnf.clauses.extend([[left[x]], [right[y]], [is_or if action == 'or' else -is_or]])
        selectors.append((left, right, is_or))
    return cnf, selectors


def verify(gates, op, anchors, rows):
    action, left, right = gates[-1]
    assert action == op and 14 <= left < right
    ownership = {}
    for m in range(1 << 14):
        w = [bool(m & (1 << i)) for i in range(14)]
        for operation, x, y in gates:
            assert x != y and 0 <= x < len(w) and 0 <= y < len(w)
            w.append(w[x] or w[y] if operation == 'or' else w[x] and w[y])
        assert w[-1] == has_edge(m), f'wrong output at {m}'
        if m in (rows[anchors[0]], rows[anchors[1]]):
            assert w[left] != w[right]
            ownership[m] = w[left]
    assert ownership[rows[anchors[0]]] != ownership[rows[anchors[1]]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--op', choices=('and', 'or'), default='or')
    parser.add_argument('--orbit', type=int, default=0)
    parser.add_argument('--gates', type=int, default=26)
    parser.add_argument('--control', action='store_true')
    parser.add_argument('--solver', default=shutil.which('cadical'))
    parser.add_argument('--seconds', type=int, default=60)
    parser.add_argument('--cnf', type=Path, help='also keep the DIMACS instance at this path')
    args = parser.parse_args()
    if not args.solver or args.seconds < 1 or args.gates < 1:
        parser.error('supply a CaDiCaL executable and positive gate/time budgets')
    if args.control and (args.op, args.orbit) != ('or', 0):
        parser.error('the pinned control uses OR orbit 0')
    neg = negative_rows()
    rows = POSITIVE_ROWS + neg
    matrix = orbit_table(POSITIVE_ROWS if args.op == 'or' else neg, automorphisms(),
                         {m: i for i, m in enumerate(rows)})
    if not 0 <= args.orbit < len(matrix):
        parser.error('orbit index out of range')
    anchors = matrix[args.orbit]['signature_indices']
    pin = star_control() if args.control else None
    budget = len(pin) if pin else args.gates
    cnf, selectors = encode(budget, args.op, anchors, rows, pin)
    print(f'{args.op} orbit {args.orbit}, anchor rows {anchors}, total gates {budget}, '
          f'{cnf.vars} variables, {len(cnf.clauses)} clauses', flush=True)
    with tempfile.TemporaryDirectory(prefix='heawood-sat-') as tmp:
        instance = args.cnf if args.cnf else Path(tmp) / 'instance.cnf'
        cnf.write(instance)
        proc = subprocess.run([args.solver, '-t', str(args.seconds), str(instance)],
                              capture_output=True, text=True)
    if proc.returncode == 10:
        model = {int(i) for line in proc.stdout.splitlines() if line.startswith('v ') for i in line[2:].split()}
        def selected(choices):
            x, = (i for i, v in enumerate(choices) if v in model)
            return x
        gates = [('or' if selector in model else 'and', selected(left), selected(right))
                 for left, right, selector in selectors]
        verify(gates, args.op, anchors, rows)
        print(f'SAT; verified on all {1 << 14} assignments. Gates {gates}')
    elif proc.returncode == 20:
        print('UNSAT reported for this shard; no proof log was requested.')
    elif proc.returncode == 0:
        print('UNKNOWN; no SAT model or UNSAT result.')
    else:
        raise SystemExit(f'CaDiCaL error {proc.returncode}: {proc.stderr}')


if __name__ == '__main__':
    main()
