"""Compile affine-clause elimination into an arithmetic program for visible choices.

A path contributes a factor for each visible variable assigned one. Distinct
helper witnesses give distinct terms before coefficients are collected.
"""

from collections import Counter
from dataclasses import dataclass
from itertools import permutations, product
from pathlib import Path
from random import Random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import clause, satisfied
from syndrome import _basis_and_coordinates, _buckets, syndrome_prefixes


@dataclass
class Program:
    # Gate zero is the multiplicative identity. None at output denotes additive zero.
    gates: list
    output: int | None
    ranks: list
    weighted_gates_per_layer: list

    def evaluate(self, zero, one, weights, add, multiply):
        if self.output is None:
            return zero
        values = [one]
        for op, left, right in self.gates[1:]:
            if op == "weight":
                result = multiply(values[left], weights[right])
            else:
                result = add(values[left], values[right])
            values.append(result)
        return values[self.output]


def affine_bit(descriptor, syndrome, bit):
    coords, current_coeff, rhs = descriptor
    return ((coords & syndrome).bit_count() & 1) ^ (current_coeff & bit) ^ rhs


def compile_program(flats, n, order, visible):
    order = tuple(order)
    visible = set(visible)
    if n < 0 or sorted(order) != list(range(n)) or not visible.issubset(order):
        raise ValueError("invalid universe, order, or visible-variable set")
    initial_ok, buckets = _buckets([tuple(flat) for flat in flats], n, order)
    gates = [("one", None, None)]
    old_table = [0 if initial_ok else None]
    basis = ()
    ranks = [0]
    weighted_counts = []
    for variable, bucket in zip(order, buckets):
        bit_mask = 1 << variable
        forms = list(basis) + [row >> 1 for flat in bucket for row in flat]
        residuals = [f & ~bit_mask for f in forms]
        next_basis, coordinates, _ = _basis_and_coordinates(residuals)
        rhs_values = [0] * len(basis) + [row & 1 for flat in bucket for row in flat]
        descriptors = [(c, int(bool(f & bit_mask)), rhs)
                       for c, f, rhs in zip(coordinates, forms, rhs_values)]
        index_map = descriptors[:len(basis)]
        pos = len(basis)
        predicates = []
        for flat in bucket:
            predicates.append(descriptors[pos:pos + len(flat)])
            pos += len(flat)
        next_table = []
        layer_weights = 0
        for t in range(1 << len(next_basis)):
            children = []
            for b in (0, 1):
                prev = sum(affine_bit(desc, t, b) << j for j, desc in enumerate(index_map))
                child = old_table[prev]
                if child is None or any(all(affine_bit(row, t, b) == 0 for row in flat)
                                        for flat in predicates):
                    continue
                if b and variable in visible:
                    gates.append(("weight", child, variable))
                    child = len(gates) - 1
                    layer_weights += 1
                children.append(child)
            if len(children) == 2:
                gates.append(("sum", *children))
                next_table.append(len(gates) - 1)
            else:
                next_table.append(children[0] if children else None)
        weighted_counts.append(layer_weights)
        ranks.append(len(next_basis))
        basis, old_table = next_basis, next_table
    assert len(old_table) == 1
    return Program(gates, old_table[0], ranks, weighted_counts)


def monomials(program, visible):
    # Exponential oracle for small tests. A bit mask represents a multilinear monomial.
    weights = {v: v for v in visible}

    def shift(poly, variable):
        assert all(not mask & (1 << variable) for mask in poly)
        return Counter({mask | (1 << variable): count for mask, count in poly.items()})

    return program.evaluate(Counter(), Counter({0: 1}), weights, Counter.__add__, shift)


def minimum(program, costs):
    # Structurally impossible states have been pruned; an impossible output is None.
    return program.evaluate(None, 0, costs, min, int.__add__)


def encoded_tours(m):
    edges = [(i, j) for i in range(m) for j in range(m) if i != j]
    ids = {edge: index for index, edge in enumerate(edges)}
    models = []
    for rest in permutations(range(1, m)):
        tour = (0,) + rest
        models.append(sum(1 << ids[tour[i-1], tour[i]] for i in range(m)))
    # For checking small m, use a direct truth table of a row/degree encoding
    # with extra negative clauses for each proper cycle. All are ordinary clauses.
    raw = []
    for position in range(2):
        for vertex in range(m):
            group = [i + 1 for i, edge in enumerate(edges) if edge[position] == vertex]
            raw.append(clause(*group))
            for j in range(len(group)):
                for i in range(j):
                    raw.append(clause(-group[i], -group[j]))
    for length in range(2, m):
        for vertices in permutations(range(m), length):
            if vertices[0] != min(vertices):
                continue
            raw.append(clause(*[-1 - ids[vertices[i-1], vertices[i]] for i in range(length)]))
    return edges, models, raw


def test_program():
    rng = Random(7013401)
    random_assignments = 0
    for _ in range(180):
        n = rng.randrange(8)
        raw = [tuple(rng.randrange(1 << (n+1)) for _ in range(rng.randrange(1, 4)))
               for _ in range(rng.randrange(8))]
        order = rng.sample(range(n), n)
        visible = set(rng.sample(range(n), rng.randrange(n+1)))
        program = compile_program(raw, n, order, visible)
        mask = sum(1 << v for v in visible)
        expected = Counter(x & mask for x in range(1 << n) if satisfied(raw, x))
        random_assignments += 1 << n
        assert monomials(program, visible) == expected
        costs = {v: rng.randrange(-6, 9) for v in visible}
        oracle = min((sum(costs[v] for v in visible if term & (1 << v))
                      for term in expected), default=None)
        assert minimum(program, costs) == oracle
        assert program.ranks == [len(layer.basis) for layer in syndrome_prefixes(raw, n, order)]
        assert all(g <= (1 << r if v in visible else 0)
                   for g, r, v in zip(program.weighted_gates_per_layer, program.ranks[1:], order))

    print(f"180 random programs, {random_assignments} full assignments")
    print("m edges witnesses_per_tour orders max_rank max_weight_gates")
    for m in (2, 3, 4):
        edges, models, raw = encoded_tours(m)
        count = len(edges)
        visible = set(range(count))
        # An unconstrained hidden bit doubles each coefficient and leaves min unchanged.
        n = count + 1
        orders = [list(range(n)), list(reversed(range(n))), rng.sample(range(n), n)]
        stats = []
        for order in orders:
            pg = compile_program(raw, n, order, visible)
            assert monomials(pg, visible) == Counter({point: 2 for point in models})
            for _ in range(16):
                costs = {i: rng.randrange(3) for i in visible}
                expected = min(sum(costs[i] for i in visible if x & (1 << i)) for x in models)
                assert minimum(pg, costs) == expected
            assert pg.evaluate(0, 1, [1]*count, lambda a,b:(a+b)%2, lambda a,b:(a*b)%2)==0
            stats.append((max(pg.ranks), sum(pg.weighted_gates_per_layer)))
        print(m, count, 2, len(orders), max(r for r,_ in stats), max(g for _,g in stats))


if __name__ == "__main__":
    test_program()
