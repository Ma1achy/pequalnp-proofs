"""Compile the truncated sum of Boolean-interpolation differences over F₂.

Input is a topologically ordered arithmetic DAG in boolean_jet.py's format,
with its last gate as output. No promise is inspected during compilation.
Run directly with Python 3 and no third-party packages.
"""

from itertools import combinations, product
from math import comb
from random import Random

from boolean_jet import _specialize, compile_layer, evaluations, formal_expansion, reduce_monomial


def retained_sizes(n, r):
    """Sizes k whose interpolation operator R_K occurs an odd number of times.

    Delta_J is the product over i in J of (R_i + id). The coefficient of
    R_K is the number modulo two of its supersets of size at most r.
    """
    if n < 0 or r < 0:
        raise ValueError("variable count and truncation must be nonnegative")
    r = min(r, n)
    return [k for k in range(r + 1) if sum(comb(n-k, j-k) for j in range(k, r+1)) % 2]


def _check_input(gates, n):
    if not gates:
        raise ValueError("expected a nonempty arithmetic circuit")
    for i, gate in enumerate(gates):
        if len(gate) == 2 and gate[0] == "c" and gate[1] in (0, 1):
            continue
        if len(gate) == 2 and gate[0] == "v" and 0 <= gate[1] < n:
            continue
        if len(gate) == 3 and gate[0] in ("+", "*") and all(0 <= v < i for v in gate[1:]):
            continue
        raise ValueError(f"invalid gate {i}: {gate!r}")


def combine_interpolations(gates, n, r):
    """Emit the ordinary F₂ DAG for Σ_{|J|≤r} Delta_J P."""
    _check_input(gates, n)
    circuit = []
    outputs = []
    for size in retained_sizes(n, r):
        for coordinates in combinations(range(n), size):
            copy, out = _specialize(gates, coordinates)
            offset = len(circuit)
            for gate in copy:
                if gate[0] in ("+", "*"):
                    circuit.append((gate[0], offset + gate[1], offset + gate[2]))
                else:
                    circuit.append(gate)
            outputs.append(offset + out)
    total = outputs[0]  # Every maximal subset of size min(r,n) has coefficient one.
    for out in outputs[1:]:
        circuit.append(("+", total, out))
        total = len(circuit)-1
    assert total == len(circuit)-1
    return circuit


def size_bound(s, n, m, r):
    """Count constant/variable gates, all specialization copies, sums, and layers."""
    sizes = retained_sizes(n, r)
    count = sum(comb(n, k) for k in sizes)
    def interpolate(k):
        return s if k == 0 else (1 << k) * (s+k+1) + 2*k
    before = sum(comb(n, k)*interpolate(k) for k in sizes) + count - 1
    return before, 1+(m+1)**2 * before


def compile_sparse_layer(gates, n, m, r):
    """Return (DAG,output index) for formal homogeneousComponent_m of the truncated sum."""
    if m < 0:
        raise ValueError("degree must be nonnegative")
    circuit = combine_interpolations(gates, n, r)
    result, out = compile_layer(circuit, (), m)
    before, after = size_bound(len(gates), n, m, r)
    assert len(circuit) == before and len(result) <= after
    return result, out


def clipped(poly, chosen):
    out = set()
    for term in poly:
        out.symmetric_difference_update([reduce_monomial(term, chosen)])
    return out


def direct_differences(poly, n, r):
    """Independent formal oracle. Apply one difference at a time, then XOR those terms."""
    acc = set()
    for j in range(min(r, n)+1):
        for subset in combinations(range(n), j):
            difference = poly
            for i in subset:
                difference = difference ^ clipped(difference, (i,))
            acc ^= difference
    return acc


def degree_layer(poly, degree):
    return {term for term in poly if sum(term) == degree}


def promised(poly, m, r):
    return all(sum(e > 1 for e in term) <= r for term in poly
               if sum(e != 0 for e in term) <= m)


def test_case(gates, n, m, r):
    poly = formal_expansion(gates, len(gates)-1, n)
    truncated = direct_differences(poly, n, r)
    middle = combine_interpolations(gates, n, r)
    assert formal_expansion(middle, len(middle)-1, n) == truncated
    compiled, out = compile_sparse_layer(gates, n, m, r)
    actual = formal_expansion(compiled, out, n)
    assert actual == degree_layer(truncated, m)
    expected = degree_layer(clipped(poly, range(n)), m)
    if promised(poly, m, r):
        assert actual == expected
    return actual, expected, len(compiled)


def monomial(exp):
    gates = [("c", 1)]
    latest = 0
    for i, power in enumerate(exp):
        if not power:
            continue
        var = len(gates)
        gates.append(("v", i))
        for _ in range(power):
            gates.append(("*", latest, var))
            latest = len(gates)-1
    return gates


def regressions():
    cases = under_promise = 0
    for n in range(4):
        for exp in product(range(4), repeat=n):
            gates = monomial(exp)
            for m in range(n+2):
                for r in range(n+1):
                    test_case(gates, n, m, r)
                    under_promise += promised({exp}, m, r)
                    cases += 1
    # Include the zero polynomial, repeated reads and exact cancellations.
    test_case([("c", 0)], 0, 0, 3)
    test_case([("v", 0), ("*", 0, 0), ("+", 1, 1)], 1, 1, 0)
    rng = Random(741859)
    dag_cases = 0
    for _ in range(32):
        n = 3
        dag = [("v", i) for i in range(n)] + [("c", 0), ("c", 1)]
        for _ in range(7):
            i = rng.randrange(len(dag))
            j = i if rng.randrange(3) == 0 else rng.randrange(len(dag))
            dag.append((rng.choice(("+", "*")), i, j))
        for r in range(n+1):
            for m in range(1, n+1):
                test_case(dag, n, m, r)
                dag_cases += 1
    return cases, under_promise, dag_cases


def distributed_tours():
    # The loopless directed three-vertex graph has two disjoint directed 3-tours.
    # Replace each cubic tour monomial t by t*(x_i+x_j+x_k); their cube values agree.
    dag = [("v", i) for i in range(6)]

    def emit(op, i, j):
        dag.append((op, i, j))
        return len(dag)-1

    def inflate(i, j, k):
        tour = emit("*", emit("*", i, j), k)
        coordinates = emit("+", emit("+", i, j), k)
        return emit("*", tour, coordinates)

    a = inflate(0, 1, 2)
    b = inflate(3, 4, 5)
    emit("+", emit("+", a, b), emit("*", a, b))
    for assignment in range(64):
        assert evaluations(dag, assignment) == (assignment & 7 == 7 or assignment & 56 == 56)
    poly = formal_expansion(dag, len(dag)-1, 6)
    low = [term for term in poly if sum(e>0 for e in term) <= 3]
    high = poly - set(low)
    assert len(low) == 6 and len(high) == 9
    assert {i for term in low for i, power in enumerate(term) if power > 1} == set(range(6))
    assert promised(poly, 3, 1) and not promised(poly, 6, 1)
    result, expected, count = test_case(dag, 6, 3, 1)
    assert result == expected == {(1, 1, 1, 0, 0, 0), (0, 0, 0, 1, 1, 1)}
    assert not degree_layer(poly, 3)
    return len(dag), count, size_bound(len(dag), 6, 3, 1)


def counterexamples():
    # The first family loses the desired degree-m term. All r+1 variables repeat.
    for r in range(4):
        n = r+1
        observed, wanted, _ = test_case(monomial((2,)*n), n, n, r)
        assert not observed and wanted == {(1,)*n}
    # Checking only support exactly m misses lower-support spurious degree-m terms.
    observed, wanted, _ = test_case(monomial((2, 2)), 2, 3, 1)
    assert observed == {(1, 2), (2, 1)} and not wanted


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    cases, promised_cases, dags = regressions()
    print("Monomial/degree/truncation cases", cases, "under the hypothesis", promised_cases)
    print("Seeded DAG/degree/truncation cases", dags, "seed", 741859)
    print("Three-vertex tour gates: source, output, (exact pre-layer, output bound)", distributed_tours())
    counterexamples()
    print("Four missing-term counterexamples and one spurious-layer counterexample passed.")
