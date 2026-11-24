"""Boolean ANF jets, transfer on low-support repeats, and directed tour checks. Stdlib only."""

from bisect import bisect_left
from itertools import combinations, permutations
from math import comb, factorial
from random import Random


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def zeta_full(values, n):
    """Subset zeta transform over F2; its own inverse."""
    out = list(values)
    for bit in (1 << i for i in range(n)):
        for s in range(len(out)):
            if s & bit:
                out[s] ^= out[s ^ bit]
    return out


def evaluations(gates, assignment):
    """Topologically indexed constants, variables, sums and products, including reuse."""
    value = []
    for gate in gates:
        op = gate[0]
        if op == "c":
            value.append(gate[1])
        elif op == "v":
            value.append((assignment >> gate[1]) & 1)
        elif op == "+":
            value.append(value[gate[1]] ^ value[gate[2]])
        elif op == "*":
            value.append(value[gate[1]] & value[gate[2]])
        else:
            raise ValueError(op)
    return value[-1]


def jet(gates, n, d):
    """Compute low-support ANF through ball evaluations, with sorted-mask indexing."""
    if n < 0 or d < 0:
        raise ValueError("n and d must be nonnegative")
    masks = sorted(sum(1 << i for i in subset)
                   for r in range(min(n, d) + 1) for subset in combinations(range(n), r))
    coeffs = [evaluations(gates, s) for s in masks]
    schedule = [[] for _ in range(n)]
    for j, s in enumerate(masks):
        for bit in bits(s):
            i = bisect_left(masks, s ^ bit)
            schedule[bit.bit_length()-1].append((j, i))
    for edges in schedule:
        for j, i in edges:
            coeffs[j] ^= coeffs[i]
    return masks, coeffs


def oracle_weights(w, d):
    """All inputs with nonzero weights for evaluating the Boolean jet on w."""
    t = w.bit_count()
    if d >= t:
        return [w]
    active = list(bits(w))
    return [sum(sub) for r in range(d+1) if not ((d-r) & ~(t-r-1))
            for sub in combinations(active, r)]


def union_product(a, b, truncation):
    """ANFs are packed as incidence masks, indexing by variable subset."""
    out = 0
    for x in bits(a):
        i = x.bit_length()-1
        for y in bits(b):
            j = y.bit_length()-1
            out ^= 1 << (i | j)
    return out & truncation


def ball_checks():
    products = lookups = 0
    for n in range(4):
        order = 1 << n
        graphs = [sum(v << i for i, v in enumerate(zeta_full([(a >> i) & 1 for i in range(order)], n)))
                  for a in range(1 << order)]
        for d in range(n+1):
            ball = sum(1 << s for s in range(order) if s.bit_count() <= d)
            for a, g in enumerate(graphs):
                an = g & ball
                for w in range(order):
                    evaluation = sum((an >> u) & 1 for u in range(order) if u & w == u) % 2
                    expected = sum((a >> u) & 1 for u in oracle_weights(w, d)) % 2
                    assert evaluation == expected
                    lookups += 1
                for b, h in enumerate(graphs):
                    assert union_product(an, h & ball, ball) == graphs[a & b] & ball
                    products += 1
    return products, lookups


def random_dags():
    rng = Random(314159)
    cases = 0
    for n in range(1, 7):
        for _ in range(32):
            gates = [("v", i) for i in range(n)] + [("c", 0), ("c", 1)]
            for _ in range(15):
                a = rng.randrange(len(gates))
                b = a if rng.randrange(3) == 0 else rng.randrange(len(gates))
                gates.append((rng.choice(("+", "*")), a, b))
            truth = [evaluations(gates, s) for s in range(1 << n)]
            full = zeta_full(truth, n)
            for d in range(n+1):
                masks, out = jet(gates, n, d)
                assert out == [full[s] for s in masks]
                cases += 1
    return cases


def reduce_monomial(exp, chosen):
    return tuple(min(e, 1) if j in chosen else e for j, e in enumerate(exp))


def partial_reduction_check():
    """Check support preservation with cancellations over F2, including high-degree junk."""
    rng = Random(271828)
    cases = 0
    for n in range(1, 8):
        for _ in range(64):
            d = rng.randrange(n+1)
            poly = set()
            for _ in range(36):
                term = tuple(rng.randrange(5) if rng.randrange(2) else 0 for _ in range(n))
                poly.symmetric_difference_update([term])
            chosen = {j for term in poly if sum(e != 0 for e in term) <= d
                      for j, e in enumerate(term) if e > 1}
            computed = set()
            expected = set()
            for term in poly:
                partial = reduce_monomial(term, chosen)
                if sum(partial) == d:
                    computed.symmetric_difference_update([partial])
                canonical = reduce_monomial(term, range(n))
                if sum(canonical) == d:
                    expected.symmetric_difference_update([canonical])
            assert computed == expected
            cases += 1
    return cases


def _specialize(gates, chosen):
    """Shannon-reduce chosen coordinates, sharing both literals across all copies."""
    if not chosen:
        return gates, len(gates)-1
    partial = [("c", 1)]
    literals = []
    for variable in chosen:
        positive = len(partial)
        partial.append(("v", variable))
        negative = len(partial)
        partial.append(("+", 0, positive))
        literals.append((negative, positive))
    terms = []
    for pattern in range(1 << len(chosen)):
        fixes = {var: (pattern >> j) & 1 for j, var in enumerate(chosen)}
        first = len(partial)
        for gate in gates:
            op = gate[0]
            if op == "v" and gate[1] in fixes:
                partial.append(("c", fixes[gate[1]]))
            elif op in ("v", "c"):
                partial.append(gate)
            else:
                partial.append((op, first+gate[1], first+gate[2]))
        term = len(partial)-1
        for j, options in enumerate(literals):
            partial.append(("*", term, options[(pattern >> j) & 1]))
            term = len(partial)-1
        terms.append(term)
    total = terms[0]
    for term in terms[1:]:
        partial.append(("+", total, term))
        total = len(partial)-1
    return partial, total


def compile_layer(gates, chosen, degree):
    """Emit an F2 DAG with the stated finite bound for homogeneous_degree(P_chosen(g))."""
    if not gates or degree < 0:
        raise ValueError("expected a nonempty gate list and nonnegative degree")
    chosen = tuple(sorted(set(chosen)))
    partial, total = _specialize(gates, chosen)
    b = len(chosen)
    assert len(partial) <= (1 << b)*(len(gates)+b+1) + 2*b
    output = [("c", 0)]
    parts = []
    one = None

    def operation(op, left, right):
        # Index zero is the shared polynomial zero, including for absent layers.
        if op == "+":
            if left == 0:
                return right
            if right == 0:
                return left
            if left == right:
                return 0
        elif left == 0 or right == 0:
            return 0
        output.append((op, left, right))
        return len(output)-1

    for gate in partial:
        op = gate[0]
        layer = [0]*(degree+1)
        if op == "c":
            if gate[1]:
                if one is None:
                    one = len(output)
                    output.append(("c", 1))
                layer[0] = one
        elif op == "v":
            if degree:
                layer[1] = len(output)
                output.append(gate)
        else:
            left, right = parts[gate[1]], parts[gate[2]]
            for j in range(degree+1):
                if op == "+":
                    layer[j] = operation("+", left[j], right[j])
                else:
                    term = operation("*", left[0], right[j])
                    for i in range(1, j+1):
                        summand = operation("*", left[i], right[j-i])
                        term = operation("+", term, summand)
                    layer[j] = term
        parts.append(layer)
    assert len(output) <= 1 + (degree+1)**2 * len(partial)
    return output, parts[total][degree]


def formal_expansion(gates, out, n):
    """Tiny-instance checker: preserve positive exponents and F2 cancellations."""
    values = []
    for gate in gates[:out+1]:
        if gate[0] == "c":
            value = {(0,)*n} if gate[1] else set()
        elif gate[0] == "v":
            value = {tuple(int(i == gate[1]) for i in range(n))}
        elif gate[0] == "+":
            value = values[gate[1]] ^ values[gate[2]]
        else:
            value = set()
            for a in values[gate[1]]:
                for b in values[gate[2]]:
                    value.symmetric_difference_update([tuple(x+y for x, y in zip(a, b))])
        values.append(value)
    return values[out]


def compiler_checks():
    # The two directed 3-tours use disjoint triples of edges. Artificial powers
    # preserve all cube values but suppress one of the formal degree-three terms.
    gates = [("v", i) for i in range(6)]
    gates.extend([("*", 0, 0), ("*", 6, 6), ("*", 7, 1), ("*", 8, 2),
                  ("*", 3, 4), ("*", 10, 5), ("+", 9, 11), ("*", 9, 11), ("+", 12, 13)])
    source = formal_expansion(gates, len(gates)-1, 6)
    target = {(1,1,1,0,0,0), (0,0,0,1,1,1)}
    assert len({e for e in source if sum(e) == 3}) == 1
    dag, out = compile_layer(gates, (0,), 3)
    assert formal_expansion(dag, out, 6) == target
    bound = 1 + 4**2 * (2*(len(gates)+1+1) + 2)
    assert len(dag) <= bound
    return len(gates), len(dag), bound


def compiler_regressions():
    rng = Random(173205)
    families = [[("c", 0)], [("c", 1)], [("v", 0)], [("v", 2), ("+", 0, 0)]]
    for _ in range(16):
        gates = [("v", i) for i in range(3)] + [("c", 0), ("c", 1)]
        for _ in range(8):
            gates.append((rng.choice(("+", "*")), rng.randrange(len(gates)), rng.randrange(len(gates))))
        families.append(gates)
    cases = 0
    for gates in families:
        source = formal_expansion(gates, len(gates)-1, 3)
        for mask in range(8):
            chosen = {i for i in range(3) if mask >> i & 1}
            reduced = set()
            for term in source:
                reduced.symmetric_difference_update([reduce_monomial(term, chosen)])
            for degree in range(4):
                dag, out = compile_layer(gates, chosen, degree)
                b = len(chosen)
                assert len(dag) <= 1 + (degree+1)**2 * ((1 << b)*(len(gates)+b+1) + 2*b)
                exact = {term for term in reduced if sum(term) == degree}
                assert formal_expansion(dag, out, 3) == exact
                cases += 1
    return cases


def tour_masks(m):
    arcs = {(v, w): i for i, (v, w) in enumerate(
        (p, q) for p in range(m) for q in range(m) if p != q)}
    return [sum(1 << arcs[order[i], order[(i+1) % m]] for i in range(m))
            for tail in permutations(range(1, m)) for order in [(0, *tail)]]


def tour_checks():
    out = []
    for m in range(3, 8):
        tours = tour_masks(m)
        unions = {p | q for p, q in combinations(tours, 2) if (p | q).bit_count() == m+3}
        assert len(unions) == factorial(m-1)*comb(m, 3)//2
        if m <= 5:
            assert all(sum(t & u == t for t in tours) == 2 for u in unions)
        if m <= 4:
            variables = m*(m-1)
            counts = [sum(t & u == t for t in tours) for u in range(1 << variables)]
            exists = zeta_full([int(x > 0) for x in counts], variables)
            parity = zeta_full([x % 2 for x in counts], variables)
            assert {s for s, v in enumerate(parity) if v} == set(tours)
            first_terms = {s for s, (x, y) in enumerate(zip(exists, parity))
                           if x != y and s.bit_count() <= m+3}
            assert first_terms == unions
        out.append((m, len(tours), len(unions)))
    return out


def examples():
    for n in range(1, 9):
        chain = [("c", 1)]
        curr = 0
        for i in range(n):
            v = len(chain)
            chain.extend([("v", i), ("+", 0, v), ("*", curr, v+1)])
            curr = len(chain)-1
        for d in range(n+1):
            masks, coeffs = jet(chain, n, d)
            assert all(coeffs) and len(masks) == sum(comb(n, i) for i in range(d+1))
        w = (1 << n)-1
        assert set(oracle_weights(w, n-1)) == set(range(w))
    f = [("v", 0)]
    for _ in range(30):
        f.append(("*", len(f)-1, len(f)-1))
    assert jet(f, 1, 1) == ([0, 1], [0, 1])


if __name__ == "__main__":
    pairs, queries = ball_checks()
    print("Truncated product checks", pairs)
    print("Query-weight checks", queries)
    print("Seeded DAG and cutoff checks", random_dags())
    print("Seeded partial-reduction checks", partial_reduction_check())
    print("Three-vertex tour example: input gates, compiled gates, bound", compiler_checks())
    print("Formal compiled outputs and finite size bounds", compiler_regressions())
    print("Tour vertices, tours, first correcting monomials", tour_checks())
    examples()
    print("Dense small-circuit and oracle examples passed.")
