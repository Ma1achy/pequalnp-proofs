#!/usr/bin/env python3
"""Nested arithmetic-oracle DAGs over F₂[x]/(x)^(D+1), with shared wires.

A Q gate substitutes earlier wires into a fixed, formal multivariate oracle.
An H gate first takes its indicated Hasse derivative in the *oracle's formal
arguments*, then substitutes earlier wires. Arbitrary derivatives of internal
wires are not operations of this model. Returns every wire, including those
read repeatedly. Run directly with Python 3; no third-party packages.
"""
from math import comb
from random import Random

from boolean_jet import tour_masks, zeta_full


def product(left, right, cutoff):
    """Ordinary formal multiplication with total-degree truncation."""
    result = set()
    for u in left:
        for v in right:
            term = tuple(i+j for i, j in zip(u, v))
            if sum(term) <= cutoff:
                result.symmetric_difference_update((term,))
    return result


def decision_anf(m):
    n = m*(m-1)
    tours = tour_masks(m)
    truth = [int(any(g & t == t for t in tours)) for g in range(1 << n)]
    support = zeta_full(truth, n)
    return {tuple(bit >> i & 1 for i in range(n)) for bit, value in enumerate(support) if value}


def square_power(poly, j):
    """Independent of the low-degree simulator: square in the full formal ring."""
    for _ in range(j):
        poly = product(poly, poly, 2*max(map(sum, poly), default=0))
    return poly


def hasse(poly, alpha):
    """D^[alpha]Q(z) is the coefficient of t^alpha in Q(z+t)."""
    result = set()
    for term in poly:
        if all(k <= e and comb(e, k) % 2 for e, k in zip(term, alpha)):
            result.add(tuple(e-k for e, k in zip(term, alpha)))
    return result


def scalar(poly, values):
    return sum(all(e == 0 or b for e, b in zip(term, values)) for term in poly) % 2


def substitute(poly, args, one, cutoff):
    powers = [{0: one, 1: a} for a in args]

    def power(i, e):
        if e not in powers[i]:
            half = power(i, e//2)
            square = product(half, half, cutoff)
            powers[i][e] = product(square, args[i], cutoff) if e % 2 else square
        return powers[i][e]

    result = set()
    for term in poly:
        value = one
        for i, e in enumerate(term):
            if e:
                value = product(value, power(i, e), cutoff)
                if not value:
                    break
        result ^= value
    return result


def validate(gates, n, arity):
    if n < 0 or arity < 0 or not gates:
        raise ValueError("expected a nonempty DAG and nonnegative dimensions")
    for i, gate in enumerate(gates):
        op = gate[0]
        if op == "v" and len(gate) == 2 and 0 <= gate[1] < n:
            continue
        if op == "c" and len(gate) == 2 and gate[1] in (0, 1):
            continue
        if op in ("+", "*") and len(gate) == 3:
            args = gate[1:]
        elif op == "Q" and len(gate) == 2 and len(gate[1]) == arity:
            args = gate[1]
        elif (op == "H" and len(gate) == 3 and len(gate[1]) == arity
              and min(gate[1], default=0) >= 0 and len(gate[2]) == arity):
            args = gate[2]
        else:
            raise ValueError(f"invalid gate {i}: {gate!r}")
        if any(not 0 <= a < i for a in args):
            raise ValueError(f"illegal forward reference at gate {i}")


def evaluate(gates, n, cutoff, oracle, arity):
    validate(gates, n, arity)
    if cutoff < 0 or any(len(term) != arity or min(term, default=0) < 0 for term in oracle):
        raise ValueError("invalid cutoff or oracle polynomial")
    one = {(0,)*n}
    values = []
    for gate in gates:
        op = gate[0]
        if op == "v":
            value = {tuple(int(i == gate[1]) for i in range(n))} if cutoff else set()
        elif op == "c":
            value = one if gate[1] else set()
        elif op == "+":
            value = values[gate[1]] ^ values[gate[2]]
        elif op == "*":
            value = product(values[gate[1]], values[gate[2]], cutoff)
        else:
            target = oracle if op == "Q" else hasse(oracle, gate[1])
            value = substitute(target, [values[i] for i in gate[-1]], one, cutoff)
        values.append(value)
    return values


def replace_calls(gates, n, arity, base, j):
    """Compile Q=P^(2^j) calls into per-gate constants, preserving wire indices.

    Correct modulo total degrees >D provided D<2^j and every positive oracle
    Hasse order is <2^j. Each ordinary call uses P evaluated at the scalar
    parts of its own argument wires, including previous calls.
    """
    validate(gates, n, arity)
    if j < 0 or any(len(term) != arity for term in base):
        raise ValueError("invalid exponent or base polynomial")
    compiled, constants = [], []
    for gate in gates:
        op = gate[0]
        if op == "v":
            c = 0
        elif op == "c":
            c = gate[1]
        elif op == "+":
            c = constants[gate[1]] ^ constants[gate[2]]
        elif op == "*":
            c = constants[gate[1]] & constants[gate[2]]
        else:
            order = sum(gate[1]) if op == "H" else 0
            if order >= 1 << j:
                raise ValueError("Hasse order reaches the Frobenius exponent")
            c = 0 if order else scalar(base, [constants[i] for i in gate[-1]])
            gate = ("c", c)
        compiled.append(gate)
        constants.append(c)
    return compiled


def shared_network(arity, s, rng):
    gates = [("v", 0), ("v", 1), ("c", 0), ("c", 1), ("+", 0, 3), ("*", 4, 1)]
    # Two nested calls. The all-ones point contains a tour and has scalar 1.
    gates += [("Q", (4,)*arity), ("Q", (6,)*arity), ("*", 6, 7), ("+", 5, 8)]
    for _ in range(15):
        wire = lambda: rng.randrange(len(gates))
        op = rng.choice(("+", "*", "Q", "H"))
        if op in ("+", "*"):
            gates.append((op, wire(), wire()))
        else:
            args = tuple(wire() for _ in range(arity))
            if op == "Q":
                gates.append((op, args))
            else:
                alpha = [0]*arity
                for _ in range(rng.randrange(s)):
                    alpha[rng.randrange(arity)] += 1
                gates.append((op, tuple(alpha), args))
    return gates


def check_shared():
    rng = Random(61103)
    runs = wires = 0
    for m in (2, 3):
        arity = m*(m-1)
        base = decision_anf(m)
        for j in (1, 2, 3):
            s = 1 << j
            q = square_power(base, j)
            assert q == {tuple(e*s for e in term) for term in base}
            assert all(scalar(q, tuple(mask >> i & 1 for i in range(arity))) ==
                       int(any(mask & t == t for t in tour_masks(m))) for mask in range(1 << arity))
            for _ in range(8):
                gates = shared_network(arity, s, rng)
                compiled = replace_calls(gates, 2, arity, base, j)
                assert len(compiled) == len(gates) and all(g[0] not in ("H", "Q") for g in compiled)
                for d in range(s):
                    source = evaluate(gates, 2, d, q, arity)
                    target = evaluate(compiled, 2, d, set(), 0)
                    assert source == target
                    runs += 1
                    wires += len(gates)
    print(f"{runs} shared-DAG/cutoff comparisons; all {wires} wire jets agree")


def check_thresholds():
    base = decision_anf(3)
    first_tour = tour_masks(3)[0]
    pivot = (first_tour & -first_tour).bit_length()-1
    # On this arc line, the three-city decision ANF is exactly z_pivot.
    args = tuple(0 if i == pivot else 1 + int(first_tour >> i & 1) for i in range(6))
    gates = [("v", 0), ("c", 0), ("c", 1), ("Q", args)]
    for j in (1, 2, 3):
        s = 1 << j
        q = square_power(base, j)
        compiled = replace_calls(gates, 1, 6, base, j)
        assert evaluate(gates, 1, s-1, q, 6)[-1] == evaluate(compiled, 1, s-1, set(), 0)[-1]
        assert evaluate(gates, 1, s, q, 6)[-1] == {(s,)}
        assert not evaluate(compiled, 1, s, set(), 0)[-1]
        for order in range(1, s+1):
            alpha = tuple(order if i == pivot else 0 for i in range(6))
            derivative = gates[:-1] + [("H", alpha, args)]
            actual = evaluate(derivative, 1, 0, q, 6)[-1]
            assert actual == ({(0,)} if order == s else set())
    print("degree and positive Hasse-order thresholds attained at 2, 4 and 8")


def check_reconstruction():
    arity = 6
    base = decision_anf(3)
    pivot = 0
    # Raise just one arc to the fourth power. This second cube representative
    # has only one surviving degree-three tour before interpolation.
    different = {tuple(4*e if i == pivot else e for i, e in enumerate(term)) for term in base}
    for mask in range(1 << arity):
        point = tuple(mask >> i & 1 for i in range(arity))
        assert scalar(different, point) == scalar(base, point)
    tours = {tuple(t >> i & 1 for i in range(arity)) for t in tour_masks(3)}
    assert len(tours) == 2 and len([term for term in different if sum(term) == 3]) == 1
    # Shannon interpolation in that single argument uses two nonadaptive
    # oracle gates. The six original variables are shared across both calls.
    dag = [("v", i) for i in range(arity)] + [("c", 0), ("c", 1)]
    at_zero = (6, 1, 2, 3, 4, 5)
    at_one = (7, 1, 2, 3, 4, 5)
    dag += [("Q", at_zero), ("Q", at_one), ("+", 7, 0), ("*", 10, 8),
            ("*", 0, 9), ("+", 11, 12)]
    assert evaluate(dag, arity, 6, different, arity)[-1] == base
    assert evaluate(dag, arity, 3, different, arity)[-1] == tours
    # The same two calls on the globally fourth-powered representative have
    # no degree-three output. The second scalar evaluation also equals zero.
    assert not evaluate(dag, arity, 3, square_power(base, 2), arity)[-1]
    print("two-call interpolation recovers both directed 3-tours from a different cube representative")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("run with assertions enabled")
    check_shared()
    check_thresholds()
    check_reconstruction()
