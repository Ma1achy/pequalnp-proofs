"""A total CNF circuit generator for directed Hamiltonian cycles. Standard Python."""

import argparse
from dataclasses import dataclass
from itertools import permutations, product
from math import factorial
from pathlib import Path
from random import Random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import Counts, clause, encoded_bits, normalize, project, satisfied


def truth(op, args):
    if op == "zero":
        return 0
    if op == "one":
        return 1
    if op == "copy":
        return args[0]
    if op == "and":
        return args[0] & args[1]
    if op == "or":
        return args[0] | args[1]
    if op == "mux":
        return args[2] if args[0] else args[1]
    raise ValueError(op)


@dataclass(frozen=True)
class Gate:
    output: int
    op: str
    inputs: tuple

    def forbidden(self):
        # One ordinary clause excludes the wrong gate output at each input tuple.
        assert len(set(self.inputs)) == len(self.inputs) and all(v < self.output for v in self.inputs)
        for values in product((0, 1), repeat=len(self.inputs)):
            wrong = 1 ^ truth(self.op, values)
            literals = [-(v+1) if bit else v+1 for v, bit in zip((*self.inputs, self.output),
                                                                   (*values, wrong))]
            yield clause(*literals)


class Generator:
    def __init__(self, m):
        if m < 2:
            raise ValueError("at least two vertices are required")
        self.m = m
        self.schedule = [j-1 for i in range(1, m-1) for j in range(i, 0, -1)]
        self.gates = []
        self.n = len(self.schedule)
        self.zero = self.gate("zero")
        self.one = self.gate("one")
        slots = [[self.one if pos == v else self.zero for v in range(m-1)] for pos in range(m-1)]
        for sel, j in enumerate(self.schedule):
            left, right = slots[j], slots[j+1]
            slots[j] = [self.mux(sel, a, b) for a, b in zip(left, right)]
            slots[j+1] = [self.mux(sel, b, a) for a, b in zip(left, right)]
        self.edges = tuple((i, j) for i in range(m) for j in range(m) if i != j)
        values = []
        for i, j in self.edges:
            if i == 0:
                values.append(slots[0][j-1])
            elif j == 0:
                values.append(slots[-1][i-1])
            else:
                edge = self.zero
                for left, right in zip(slots, slots[1:]):
                    adjacent = self.binary("and", left[i-1], right[j-1])
                    edge = self.binary("or", edge, adjacent)
                values.append(edge)
        self.outputs = tuple(self.gate("copy", v) for v in values)

    def gate(self, op, *inputs):
        new = self.n
        self.n += 1
        self.gates.append(Gate(new, op, inputs))
        return new

    def mux(self, sel, a, b):
        return a if a == b else self.gate("mux", sel, a, b)

    def binary(self, op, a, b):
        if a == b:
            return a
        zero_element = self.zero if op == "and" else self.one
        unit = self.one if op == "and" else self.zero
        if zero_element in (a, b):
            return zero_element
        if a == unit:
            return b
        if b == unit:
            return a
        return self.gate(op, a, b)

    def raw(self):
        return tuple(flat for gate in self.gates for flat in gate.forbidden())

    def evaluate(self, controls):
        if len(controls) != len(self.schedule):
            raise ValueError("wrong control count")
        values = list(controls)
        for gate in self.gates:
            values.append(truth(gate.op, [values[i] for i in gate.inputs]))
        return frozenset(edge for edge, v in zip(self.edges, self.outputs) if values[v])


def edges(order):
    return frozenset(zip(order, order[1:] + order[:1]))


def direct_tour(m, controls):
    """Independent list oracle, inserting each new vertex and traversing adjacent boundaries."""
    order = list(range(1, m))
    index = 0
    for last in range(1, len(order)):
        for right in reversed(range(1, last+1)):
            if controls[index]:
                order[right-1], order[right] = order[right], order[right-1]
            index += 1
    return edges([0] + order)


def controls_for(tour):
    """Insert vertex j into the position it occupies among the tour labels ≤j."""
    controls = []
    for vertex in range(2, len(tour)+1):
        prior = [u for u in tour if u <= vertex]
        left_shifts = vertex-1-prior.index(vertex)
        controls.extend([1]*left_shifts + [0]*(vertex-1-left_shifts))
    return controls


def check_image(g, exhaustive, rng):
    covered = set()
    controls_list = product((0, 1), repeat=len(g.schedule)) if exhaustive else (
        tuple(rng.randrange(2) for _ in g.schedule) for _ in range(64))
    cases = 0
    for controls in controls_list:
        got = g.evaluate(controls)
        assert got == direct_tour(g.m, controls)
        covered.add(got)
        cases += 1
    targets = permutations(range(1, g.m)) if exhaustive else (
        tuple(rng.sample(range(1, g.m), g.m-1)) for _ in range(64))
    tours = set()
    for target in targets:
        cycle = edges((0,) + target)
        assert g.evaluate(controls_for(target)) == cycle
        tours.add(cycle)
    if exhaustive:
        assert covered == tours and len(tours) == factorial(g.m-1)
    return cases, len(covered)


def check_gates(g):
    cases = 0
    # Bits indexed in lexicographic operand order, independent of truth().
    tables = {"zero": 0, "one": 1, "copy": 0b10, "and": 0b1000,
              "or": 0b1110, "mux": 0b10101100}
    for gate in g.gates:
        flats = tuple(gate.forbidden())
        for values in product((0, 1), repeat=len(gate.inputs)+1):
            assignment = sum(x << v for x, v in zip(values, (*gate.inputs, gate.output)))
            allowed = not any(all(((row >> 1) & assignment).bit_count() % 2 == (row & 1)
                                  for row in flat) for flat in flats)
            index = 0
            for bit in values[:-1]:
                index = 2*index + bit
            assert allowed == (values[-1] == ((tables[gate.op] >> index) & 1))
            cases += 1
    assert len(set(g.outputs)) == g.m*(g.m-1)
    assert not (set(g.outputs) & {v for gate in g.gates for v in gate.inputs})
    return cases


def check_projected_image(g):
    current = normalize(g.raw(), g.n, Counts())
    for helper in reversed(range(g.outputs[0])):
        current = project(current, helper, g.n, Counts())
    tours = {edges((0,) + p) for p in permutations(range(1, g.m))}
    for bits in product((0, 1), repeat=len(g.edges)):
        visible = sum(bit << v for bit, v in zip(bits, g.outputs))
        selected = frozenset(e for e, bit in zip(g.edges, bits) if bit)
        assert satisfied(current, visible) == (selected in tours)
    return 1 << len(g.edges)


def reverse_projection(g):
    raw = g.raw()
    counts = Counts()
    current = normalize(raw, g.n, counts)
    initial = len(current)
    pairs = max_graphs = max_width = 0
    xors, reductions = counts.row_xors, counts.rref_calls
    containment = counts.containment_tests
    max_encoded = encoded_bits(current, g.n)
    for v in reversed(range(g.n)):
        counts = Counts()
        before = current
        current = project(before, v, g.n, counts)
        assert counts.empty_flats_discarded == counts.graph_pairs
        assert len(current) == len(before) - counts.graph_flats
        assert set(current).issubset(before)
        assert len(current) <= initial <= len(raw)
        max_graphs = max(max_graphs, counts.graph_flats)
        max_width = max(max_width, counts.max_candidate_width_before_rref)
        max_encoded = max(max_encoded, encoded_bits(current, g.n))
        pairs += counts.graph_pairs
        xors += counts.row_xors
        reductions += counts.rref_calls
        containment += counts.containment_tests
    assert current == () and max_graphs <= 8 and max_width <= 7
    return (len(raw), initial, encoded_bits(raw, g.n), max_encoded, pairs, max_graphs, max_width,
            xors, reductions, containment)


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--flat-through", type=int, default=6)
    ap.add_argument("--exhaustive-through", type=int, default=6)
    args = ap.parse_args()
    seed = 49271
    rng = Random(seed)
    print("seed", seed)
    print("m controls vars image-checks distinct-seen gate-checks projected-checks, flat trace")
    for m in range(2, max(8, args.flat_through, args.exhaustive_through)+1):
        g = Generator(m)
        controls, distinct = check_image(g, m <= args.exhaustive_through, rng)
        gates = check_gates(g)
        image_cases = check_projected_image(g) if m <= 3 else 0
        trace = reverse_projection(g) if m <= args.flat_through else ()
        print(m, len(g.schedule), g.n, controls, distinct, gates, image_cases, trace, flush=True)
