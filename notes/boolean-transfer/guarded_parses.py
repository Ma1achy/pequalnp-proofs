#!/usr/bin/env python3
"""Check guarded positive-polynomial extraction from small shared NNF circuits.

For each assignment A⊆B to the guarded bits, specialize the circuit, replace
the remaining positive literals by variables and the remaining negatives by
one, turn OR/AND into ordinary addition/multiplication, and multiply by x^A.
Sum those polynomials over the nonnegative integers. The evaluator uses no
literal traces. A separate parse enumerator checks the output coefficientwise.
"""

from collections import Counter
from math import comb

from boolean_jet import tour_masks


def subsets(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub-1) & mask


class NNF:
    def __init__(self, arity):
        self.arity = arity
        self.gates = [("lit", i, sign) for sign in (True, False) for i in range(arity)]

    def neg(self, i):
        return self.arity+i

    def add(self, op, a, b):
        self.gates.append((op, a, b))
        return len(self.gates)-1

    def fold(self, op, wires):
        result, *rest = wires
        for wire in rest:
            result = self.add(op, result, wire)
        return result


def bool_value(c, output, data):
    values = []
    for op, a, b in c.gates:
        if op == "lit":
            values.append(bool(data >> a & 1) == b)
        else:
            values.append(values[a] and values[b] if op == "and" else values[a] or values[b])
    return values[output]


def literal_parses(c, output):
    """Unfold each AND occurrence independently; count identical parses separately."""
    values = []
    for op, a, b in c.gates:
        if op == "lit":
            values.append([((a+1) if b else -(a+1),)])
        elif op == "or":
            values.append(values[a] + values[b])
        else:
            values.append([left + right for left in values[a] for right in values[b]])
    return values[output]


def signature(parse, arity):
    counts = tuple(parse.count(i+1) for i in range(arity))
    pos = sum(1 << i for i, count in enumerate(counts) if count)
    neg = sum(1 << i for i in range(arity) if -(i+1) in parse)
    repeat = sum(1 << i for i, count in enumerate(counts) if count > 1)
    return counts, pos, neg, repeat


def guarded_circuit(c, output, guard):
    """Build an ordinary +/* DAG. Input-variable wires are shared across assignments."""
    arity = c.arity
    gates = [("v", i) for i in range(arity)] + [("c", 0), ("c", 1)]

    def emit(op, a, b):
        gates.append((op, a, b))
        return len(gates)-1

    total = arity
    for assignment in subsets(guard):
        clone = []
        for op, a, b in c.gates:
            if op == "lit" and guard >> a & 1:
                ref = arity + int(bool(assignment >> a & 1) == b)
            elif op == "lit":
                ref = a if b else arity+1
            else:
                ref = emit("*" if op == "and" else "+", clone[a], clone[b])
            clone.append(ref)
        term = clone[output]
        for i in range(arity):
            if assignment >> i & 1:
                term = emit("*", term, i)
        total = emit("+", total, term)
    return gates, total


def polynomial(gates, output, arity, degree):
    """Sparse ordinary polynomials with positive integer coefficients, truncated at degree."""
    values = []
    unit = (0,)*arity
    for gate in gates:
        op, a = gate[:2]
        if op == "c":
            value = Counter({unit: a}) if a else Counter()
        elif op == "v":
            value = Counter({tuple(int(i == a) for i in range(arity)): 1})
        elif op == "+":
            value = values[a] + values[gate[2]]
        else:
            value = Counter()
            for x, cx in values[a].items():
                for y, cy in values[gate[2]].items():
                    e = tuple(u+v for u, v in zip(x, y))
                    if sum(e) <= degree:
                        value[e] += cx*cy
        values.append(value)
    return values[output]


def trace_polynomial(traces, guard, degree):
    result = Counter()
    for counts, pos, neg, _ in traces:
        if guard & pos & neg:
            continue
        for extra in subsets(guard & ~(pos | neg)):
            chosen = (guard & pos) | extra
            exponent = tuple((chosen >> i & 1) if guard >> i & 1 else a for i, a in enumerate(counts))
            if sum(exponent) <= degree:
                result[exponent] += 1
    return result


def make_case(n, name):
    arity = n*(n-1)
    c = NNF(arity)
    terms = []
    for tour in tour_masks(n):
        edges = [i for i in range(arity) if tour >> i & 1]
        term = c.fold("and", edges)
        if name in ("repeats", "relaxed"):
            term = c.add("and", term, edges[0])
        if name == "exact":
            for i in range(arity):
                if not tour >> i & 1:
                    term = c.add("and", term, c.neg(i))
                    term = c.add("and", term, c.neg(i))
        terms.append(term)
    root = c.fold("or", terms)
    if name == "overlap":
        # One shared input wire to AND stands for independent parse choices.
        root = c.add("and", root, root)
    if name == "low-conflict":
        false_branch = c.fold("and", [0, 1, c.neg(0), c.neg(1)]) if n == 3 else c.add("and", 0, c.neg(0))
        root = c.add("or", root, false_branch)
    if name == "relaxed":
        tour = tour_masks(n)[0]
        edges = [i for i in range(arity) if tour >> i & 1]
        root = c.add("or", root, c.fold("and", edges + [c.neg(edges[0])]))
    return c, root


def cover_checks(arity, tours, traces, relaxed, support):
    """Compare finite guard covers and the exact probability of covering repeat labels."""
    full = (1 << arity)-1
    base = min(relaxed, key=lambda g: (g.bit_count(), g))
    outside = full ^ base
    choices = {t: min((r & outside for _, p, n, r in traces if p == t and not n & t),
                      key=lambda r: (r.bit_count(), r)) for t in tours}
    repeats = max(r.bit_count() for r in choices.values())
    count = 0
    for budget in range(repeats, outside.bit_count()+1):
        family = [base | sub for sub in subsets(outside) if sub.bit_count() == budget]
        union = set().union(*(support[g] for g in family))
        assert union == tours
        assert len(family)*max(len(support[g]) for g in family) >= len(tours)
        for tour, repeated in choices.items():
            eligible = [g for g in family if not repeated & ~g]
            expected = comb(outside.bit_count()-repeated.bit_count(), budget-repeated.bit_count())
            assert len(eligible) == expected and all(tour in support[g] for g in eligible)
        total_hits = sum(len(support[g]) for g in family)
        assert total_hits*comb(outside.bit_count(), repeats) >= len(tours)*len(family)*comb(budget, repeats)
        count += 1
    return count


def check(n, name):
    c, root = make_case(n, name)
    arity = c.arity
    tours = set(tour_masks(n))
    parses = literal_parses(c, root)
    traces = [signature(parse, arity) for parse in parses]
    for graph in range(1 << arity):
        feasible = any(not pos & ~graph and not neg & graph for _, pos, neg, _ in traces)
        expected = graph in tours if name == "exact" else any(t & graph == t for t in tours)
        assert feasible == bool_value(c, root, graph) == expected
    bad = [(pos & neg) for _, pos, neg, _ in traces
           if pos.bit_count() <= n and not any(t & pos == t for t in tours)]
    assert all(bad)
    inconsistent = [p & neg for _, p, neg, _ in traces if p & neg]
    relaxed, support = set(), {}
    strict_count = 0
    for guard in range(1 << arity):
        ordinary, out = guarded_circuit(c, root, guard)
        generated = polynomial(ordinary, out, arity, n)
        assert generated == trace_polynomial(traces, guard, n)
        if any(not guard & conflict for conflict in bad):
            continue
        relaxed.add(guard)
        assert all(sum(e) == n and max(e) == 1 for e in generated)
        covered = {sum(bit << i for i, bit in enumerate(e)) for e in generated}
        clean = {p for _, p, neg, r in traces if p in tours and not p & neg and not r & ~guard}
        syntactic = {p for _, p, neg, r in traces if p in tours and not p & neg & guard and not r & ~guard}
        assert clean <= covered <= tours and covered == syntactic
        support[guard] = covered
        if all(guard & conflict for conflict in inconsistent):
            assert clean == covered
            strict_count += 1
        if name == "relaxed" and guard == 0:
            assert not clean and covered == {tour_masks(n)[0]}
    if name == "low-conflict":
        ordinary, out = guarded_circuit(c, root, 0)
        assert any(sum(term) < n for term in polynomial(ordinary, out, arity, n))
    if name == "overlap" and n == 3:
        assert len(parses) == 4 and sum(p.bit_count() == 6 for _, p, _, _ in traces) == 2
    if name == "repeats" and n == 3:
        guards = [t & -t for t in sorted(tours)]
        assert all(len(support[g]) == 1 for g in guards) and set.union(*(support[g] for g in guards)) == tours
    return len(parses), 1 << arity, len(relaxed), strict_count, cover_checks(arity, tours, traces, relaxed, support)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    cases = [check(n, name) for n in (2, 3)
             for name in ("plain", "exact", "repeats", "overlap", "low-conflict", "relaxed")]
    print("checked 12 circuits on all loopless graphs of orders 2 and 3")
    print("literal parses / guard polynomials / relaxed guards / strong guards / cover budgets:",
          *map(sum, zip(*cases)))
    # Even an entirely consistent, repeat-free OR can count the same tour twice.
    dup, q = make_case(3, "plain")
    ordinary, out = guarded_circuit(dup, dup.add("or", q, q), 0)
    weights = polynomial(ordinary, out, dup.arity, 3)
    assert len(weights) == 2 and set(weights.values()) == {2}
    print("duplicating the output OR gives coefficient two on each tour")
    print("two one-bit guards each cover exactly half the 3-tours in the repeated-literal example")
    print("an inconsistent parse contributes a tour under a relaxed guard with no clean accepting trace")
