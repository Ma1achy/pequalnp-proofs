"""Check the treewidth-to-canonical-polynomial transfer. Python standard library only."""

from collections import defaultdict
from itertools import combinations, permutations
from random import Random


# A vertex is (operation, predecessor tuple). Each input has one shared vertex.
def gate_value(op, inputs):
    if op == "false":
        return False
    if op == "true":
        return True
    if op == "not":
        return not inputs[0]
    a, b = inputs
    if op == "and":
        return a and b
    if op == "or":
        return a or b
    if op == "xor":
        return a != b
    raise ValueError(op)


def evaluate(circuit, assignment, output):
    values = []
    next_input = 0
    for op, preds in circuit:
        if op == "input":
            value = bool(assignment & (1 << next_input))
            next_input += 1
        else:
            value = gate_value(op, [values[i] for i in preds])
        values.append(value)
    return int(values[output])


def mask(vertices):
    return sum(1 << i for i in vertices)


def subsets(bits):
    current = bits
    while True:
        yield current
        if current == 0:
            break
        current = (current - 1) & bits


def decomposition(circuit, moral=False):
    """Build a tree decomposition of the undirected gate graph by min-fill elimination."""
    adjacent = {v: set() for v in range(len(circuit))}
    for v, (_, preds) in enumerate(circuit):
        for p in preds:
            assert 0 <= p < v
            adjacent[v].add(p)
            adjacent[p].add(v)
        if moral:
            for a, b in combinations(set(preds), 2):
                adjacent[a].add(b)
                adjacent[b].add(a)

    def score(v):
        neighbors = adjacent[v]
        fill = sum(b not in adjacent[a] for a, b in combinations(neighbors, 2))
        return fill, len(neighbors), v

    order, bags = [], []
    while adjacent:
        v = min(adjacent, key=score)
        neighbors = adjacent.pop(v)
        order.append(v)
        bags.append(neighbors | {v})
        for u in neighbors:
            adjacent[u].discard(v)
            adjacent[u].update(neighbors - {u})
    rank = {v: i for i, v in enumerate(order)}
    root = len(order) - 1
    parents = [min((rank[u] for u in bag if u != v), default=root)
               for v, bag in zip(order, bags)]
    parents[root] = None
    return bags, parents, order


def verify_decomposition(circuit, bags, parents):
    """A vertex's bags are connected iff they induce exactly one rooted subtree."""
    for v, (_, preds) in enumerate(circuit):
        containing = {i for i, bag in enumerate(bags) if v in bag}
        assert containing
        assert sum(parents[i] not in containing for i in containing) == 1
        for p in preds:
            assert any(p in bags[i] for i in containing)


# Each state polynomial is an integer coefficient dictionary on squarefree supports.
# Multiplication rejects repeated variables, even if their products would cancel later.
def multiply(a, b, modulus):
    product = defaultdict(int)
    for u, c in a.items():
        for v, d in b.items():
            assert not (u & v), "independent factor homes must have disjoint input variables"
            product[u | v] += c * d
    return clean(product, modulus)


def clean(poly, modulus):
    if modulus:
        return {s: c % modulus for s, c in poly.items() if c % modulus}
    return {s: c for s, c in poly.items() if c}


def lowest_part(poly):
    if not poly:
        return {}
    degree = min(s.bit_count() for s in poly)
    return {s: coeff for s, coeff in poly.items() if s.bit_count() == degree}


def table_polynomial(circuit, output, modulus=0, positive_lowest=False):
    """Use weights (1-X,X), or (1,X) and the minimum nonzero degree over N."""
    assert not (positive_lowest and modulus)

    original, parents, order = decomposition(circuit)
    verify_decomposition(circuit, original, parents)
    bags = [bag.union(*(set(circuit[v][1]) for v in bag)) for bag in original]
    verify_decomposition(circuit, bags, parents)
    largest = max(map(len, bags))
    assert largest <= 3 * max(map(len, original))
    # A directly constructed decomposition of the factor graph can be smaller.
    # For larger test cases use it only after checking the expanded bags' bound.
    homes = [[v] for v in order]
    if largest > 12:
        candidate, candidate_parents, candidate_order = decomposition(circuit, moral=True)
        if max(map(len, candidate)) < largest:
            bags, parents, order = candidate, candidate_parents, candidate_order
            verify_decomposition(circuit, bags, parents)
            largest = max(map(len, bags))
            rank = {v: i for i, v in enumerate(order)}
            homes = [[] for _ in order]
            for v, (_, preds) in enumerate(circuit):
                home = min(rank[u] for u in (v, *preds))
                homes[home].append(v)
    bits = [mask(bag) for bag in bags]
    separators = [bits[i] & bits[p] if p is not None else 0 for i, p in enumerate(parents)]
    children = [[] for _ in order]
    for i, p in enumerate(parents):
        if p is not None:
            assert i < p
            children[p].append(i)
    inputs = [v for v, (op, _) in enumerate(circuit) if op == "input"]
    variables = {v: 1 << i for i, v in enumerate(inputs)}
    messages = []
    # Charge at most two operations to make the shared complement 1-X_i.
    gates = 2 * len(inputs)
    for i, local in enumerate(homes):
        for v in local:
            assert set(circuit[v][1]) | {v} <= bags[i]
        table = defaultdict(lambda: defaultdict(int))
        for state in subsets(bits[i]):
            if output in local and not state & (1 << output):
                continue
            product = {0: 1}
            for v in local:
                op, preds = circuit[v]
                on = bool(state & (1 << v))
                if op == "input":
                    variable = variables[v]
                    weight = ({variable: 1} if on else
                              {0: 1} if positive_lowest else {0: 1, variable: -1})
                    product = multiply(product, weight, modulus)
                    gates += 1
                elif gate_value(op, [bool(state & (1 << u)) for u in preds]) != on:
                    product = {}
                    break
            if not product:
                continue
            for child in children[i]:
                factor = messages[child].get(state & separators[child], {})
                product = multiply(product, factor, modulus)
                gates += 1
            bucket = table[state & separators[i]]
            for monomial, coeff in product.items():
                bucket[monomial] += coeff
            gates += 1
        entries = {sep: clean(value, modulus) for sep, value in table.items()}
        # With nonnegative weights no surviving lowest-degree terms cancel.
        if positive_lowest:
            entries = {sep: lowest_part(value) for sep, value in entries.items()}
        messages.append(entries)
    bound = (1 << largest) * (2 * len(bags) + len(inputs) - 1) + 2 * len(inputs)
    assert gates <= bound
    return messages[-1].get(0, {}), (max(map(len, original)) - 1, largest - 1)


def mobius(values):
    """Independent multilinear interpolation from a complete Boolean truth table over Z."""
    coeffs = values.copy()
    bit = 1
    while bit < len(coeffs):
        for s in range(len(coeffs)):
            if s & bit:
                coeffs[s] -= coeffs[s ^ bit]
        bit <<= 1
    return {s: c for s, c in enumerate(coeffs) if c}


def check(circuit, output):
    n = sum(op == "input" for op, _ in circuit)
    values = [evaluate(circuit, a, output) for a in range(1 << n)]
    expected = mobius(values)
    positive, _ = table_polynomial(circuit, output, positive_lowest=True)
    assert positive == lowest_part({s: 1 for s, v in enumerate(values) if v})
    integer, widths = table_polynomial(circuit, output)
    assert expected == integer
    for modulus in (2, 3):
        result, _ = table_polynomial(circuit, output, modulus)
        assert result == clean(expected, modulus)
    return integer, widths


def hc_circuit(n, exact=False):
    arcs = [(u, v) for u in range(n) for v in range(n) if u != v]
    circuit = [("input", ()) for _ in arcs]

    def reduce(op, indices):
        wire = indices[0]
        for v in indices[1:]:
            circuit.append((op, (wire, v)))
            wire = len(circuit) - 1
        return wire

    ends = []
    for middle in permutations(range(1, n)):
        p = (0,) + middle + (0,)
        ends.append(reduce("and", [arcs.index(e) for e in zip(p, p[1:])]))
    out = reduce("or", ends)
    if exact:
        # A graph containing a tour is exactly that tour iff each vertex
        # has at most one outgoing arc.
        collisions = []
        for u in range(n):
            outgoing = [i for i, (src, _) in enumerate(arcs) if src == u]
            for a, b in combinations(outgoing, 2):
                collisions.append(reduce("and", [a, b]))
        if collisions:
            collision = reduce("or", collisions)
            circuit.append(("not", (collision,)))
            out = reduce("and", [out, len(circuit) - 1])
    return circuit, out, arcs


def spanning_masks(arcs, n):
    """Independent target: test each n-arc set's out-degrees and successor orbit."""
    result = {}
    for indices in combinations(range(len(arcs)), n):
        successor = dict(arcs[i] for i in indices)
        if len(successor) < n:
            continue
        orbit = set()
        v = 0
        while v not in orbit:
            orbit.add(v)
            v = successor[v]
        if len(orbit) == n and v == 0:
            result[mask(indices)] = 1
    return result


def main():
    x = ("input", ())
    for c, out in [([("false", ())], 0), ([("true", ())], 0), ([x, x], 0),
                   ([x, ("xor", (0, 0))], 1), ([x, ("not", (0,))], 1)]:
        check(c, out)
    assert check([x, ("and", (0, 0))], 1)[0] == {1: 1}
    # Two independent input leaves give XY. Identifying them afterwards yields X^2.
    assert check([x, x, ("and", (0, 1))], 2)[0] == {3: 1}
    random = Random(20261124)
    for _ in range(100):
        n = random.randrange(1, 6)
        c = [x] * n
        for _ in range(random.randrange(1, 11)):
            op = random.choice(["not", "and", "or", "xor", "true", "false"])
            arity = 0 if op in ("true", "false") else 1 if op == "not" else 2
            c.append((op, tuple(random.randrange(len(c)) for _ in range(arity))))
        check(c, random.randrange(len(c)))
    print("Passed 7 boundary/fanout and 100 random cases over Z, F2 and F3.")
    for n in (2, 3, 4):
        circuit, out, arcs = hc_circuit(n)
        result, widths = check(circuit, out)
        positive, _ = table_polynomial(circuit, out, positive_lowest=True)
        layer = {s: c for s, c in result.items() if s.bit_count() == n}
        assert layer == positive == spanning_masks(arcs, n)
        print(f"HC({n}): degrees {min(s.bit_count() for s in result)}.."
              f"{max(s.bit_count() for s in result)}, {len(layer)} tour monomials, "
              f"decomposition widths {widths[0]} / {widths[1]}.")
    for n in (2, 3, 4):
        circuit, out, arcs = hc_circuit(n, exact=True)
        result, widths = table_polynomial(circuit, out, positive_lowest=True)
        assert result == spanning_masks(arcs, n)
        print(f"Exact-tour({n}): lowest positive layer equals HC, "
              f"decomposition widths {widths[0]} / {widths[1]}.")


if __name__ == "__main__":
    main()
