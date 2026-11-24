"""Verify unique extensions for positive exact-one-of-three Boolean gate gadgets."""

from itertools import product


class Formula:
    """Every clause contains three distinct, unnegated Boolean variables."""

    def __init__(self):
        self.variables = set()
        self.clauses = []
        self.variables.update(("z", "t", "u", "v", "w"))
        self.add("z", "t", "u")
        self.add("z", "t", "v")
        self.add("u", "v", "w")
        self.add("z", "u", "v")

    def fresh(self, name):
        assert name not in self.variables
        self.variables.add(name)
        return name

    def add(self, a, b, c):
        assert len({a, b, c}) == 3
        assert {a, b, c} <= self.variables
        self.clauses.append((a, b, c))

    def wire(self, name):
        rail = self.fresh(name), self.fresh(name + "_bar")
        self.add(*rail, "u")
        return rail

    def and_gate(self, left, right, name):
        a, a_bar = left
        _, b_bar = right
        out, out_bar = self.wire(name)
        q00, q01, q10, q11 = (self.fresh(f"{name}_{bits}")
                               for bits in ("00", "01", "10", "11"))
        self.add(q00, q01, a)
        self.add(q10, q11, a_bar)
        self.add(q01, q11, b_bar)
        self.add(q11, out_bar, "u")
        return out, out_bar

    def not_gate(self, wire, name):
        out = self.wire(name)
        self.add(wire[0], out[0], "u")
        return out

    def accept(self, out):
        self.add(out[0], "u", "v")


def exhaustive_models(formula, fixed):
    """Visit every completion directly, independently of the circuit semantics."""
    unknown = sorted(formula.variables - fixed.keys())
    for choices in product((0, 1), repeat=len(unknown)):
        assignment = fixed | dict(zip(unknown, choices))
        if all(sum(assignment[v] for v in clause) == 1 for clause in formula.clauses):
            yield assignment


def count_models(formula, fixed):
    """Count extensions by propagation and exhaustive, disjoint case splits."""
    def count(assignment):
        while True:
            shortest = None
            changed = False
            for clause in formula.clauses:
                weight = sum(assignment[v] for v in clause if v in assignment)
                unknown = [v for v in clause if v not in assignment]
                if weight > 1 or (not unknown and weight == 0):
                    return 0
                if not unknown:
                    continue
                if weight == 1 or len(unknown) == 1:
                    for v in unknown:
                        assignment[v] = 1 - weight
                    changed = True
                elif shortest is None or len(unknown) < len(shortest):
                    shortest = unknown
            if not changed:
                break
        if shortest is None:
            assert formula.variables == assignment.keys()
            return 1
        v = shortest[0]
        return count(assignment | {v: 0}) + count(assignment | {v: 1})

    assert fixed.keys() <= formula.variables and set(fixed.values()) <= {0, 1}
    return count(dict(fixed))


def check_graph(formula, inputs, out, expected, *, exhaustive=False):
    """Fix only signal values; complements, pins and all helpers are free."""
    configurations = list(product((0, 1), repeat=len(inputs)))
    for values in configurations:
        fixed = dict(zip((w[0] for w in inputs), values))
        assert count_models(formula, fixed) == 1
        for y in (0, 1):
            boundary = fixed | {out[0]: y}
            correct = int(y == expected(*values))
            assert count_models(formula, boundary) == correct, (values, y)
            if exhaustive:
                assert sum(1 for _ in exhaustive_models(formula, boundary)) == correct
    formula.accept(out)
    for values in configurations:
        fixed = dict(zip((w[0] for w in inputs), values))
        assert count_models(formula, fixed) == expected(*values)
    assert count_models(formula, {}) == sum(expected(*v) for v in configurations)


def check_reduced_graphs():
    """Compose both encoders and decode actual directed tours into input bits."""
    from unique_tour_gadget import build_graph, hamiltonian_successors

    cases = {
        "input": {(True,)},
        "not": {(False,)},
        "and": {(True, True)},
        "repeated": {(True,)},
        "contradiction": set(),
    }
    for name, expected in cases.items():
        formula = Formula()
        a = formula.wire("a")
        inputs = ["a"]
        if name == "and":
            b = formula.wire("b")
            inputs.append("b")
            out = formula.and_gate(a, b, "o")
        elif name == "repeated":
            out = formula.and_gate(a, a, "o")
        elif name == "contradiction":
            out = formula.and_gate(a, formula.not_gate(a, "na"), "o")
        elif name == "not":
            out = formula.not_gate(a, "o")
        else:
            out = a
        formula.accept(out)
        variables = sorted(formula.variables)
        indices = {v: i for i, v in enumerate(variables)}
        clauses = [[indices[v] + 1 for v in clause] for clause in formula.clauses]
        graph = build_graph(len(variables), clauses)
        witnesses = []
        for tour in hamiltonian_successors(graph.outgoing):
            assignment = graph.decode(tour)
            witnesses.append(tuple(assignment[indices[v]] for v in inputs))
        assert set(witnesses) == expected and len(witnesses) == len(expected)
    print("Five verifier-to-graph compositions preserved all accepting assignments.")


def main():
    pin = Formula()
    unique = {"z": 1, "t": 0, "u": 0, "v": 0, "w": 1}
    assert list(exhaustive_models(pin, {})) == [unique]
    assert count_models(pin, {}) == 1
    assert (len(pin.variables), len(pin.clauses)) == (5, 4)

    f = Formula()
    a, b = f.wire("a"), f.wire("b")
    assert (len(f.variables), len(f.clauses)) == (9, 6)
    out = f.and_gate(a, b, "o")
    assert (len(f.variables), len(f.clauses)) == (15, 11)
    check_graph(f, (a, b), out, lambda x, y: x & y, exhaustive=True)
    assert len(f.clauses) == 12

    f = Formula()
    a = f.wire("a")
    out = f.not_gate(a, "o")
    assert (len(f.variables), len(f.clauses)) == (9, 7)
    check_graph(f, (a,), out, lambda x: 1 ^ x, exhaustive=True)

    f = Formula()
    a = f.wire("a")
    out = f.and_gate(a, a, "o")
    check_graph(f, (a,), out, lambda x: x, exhaustive=True)

    f = Formula()
    a, b = f.wire("a"), f.wire("b")
    common = f.and_gate(a, b, "common")
    neg = f.not_gate(common, "neg")
    out = f.and_gate(a, neg, "o")
    check_graph(f, (a, b), out, lambda x, y: x & (1 ^ y))

    f = Formula()
    a, b = f.wire("a"), f.wire("b")
    common = f.and_gate(a, b, "common")
    repeated = f.and_gate(common, common, "repeated")
    neg = f.not_gate(common, "neg")
    out = f.and_gate(repeated, neg, "o")
    check_graph(f, (a, b), out, lambda x, y: 0)
    print("Unique pin verified; all AND, NOT and repeated-input truth-table counts passed.")
    print("Two composed DAGs passed with outputs free, fixed and pinned to acceptance.")
    check_reduced_graphs()


if __name__ == "__main__":
    main()
