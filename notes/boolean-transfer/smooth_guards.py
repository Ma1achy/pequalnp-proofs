#!/usr/bin/env python3
"""Lift pinned guard values through total degree m in formal F2[t_1,...,t_d].

The input guards are outputs of a shared +,* straight-line circuit. At a point
a of full Jacobian row rank, a chosen first-order tangent in the kernel extends
to every finite order. Only the chosen pivot coordinates receive corrections.
This expands tiny instances for testing; expansion size need not be polynomial.
Run with python3 smooth_guards.py from any working directory.
"""

from itertools import permutations, product as cartesian
from random import Random

from boolean_jet import formal_expansion, tour_masks
from oracle_transfer import product


def linear_combination(mask, polys):
    result = set()
    for i, poly in enumerate(polys):
        if mask >> i & 1:
            result ^= poly
    return result


def units(dim):
    return [tuple(int(i == j) for i in range(dim)) for j in range(dim)]


def jets(gates, z, dim, bound):
    """Evaluate formal polynomial wires modulo all monomials of degree > bound."""
    out = []
    for op, *args in gates:
        if op == 'v':
            value = {u for u in z[args[0]] if sum(u) <= bound}
        elif op == 'c':
            value = {(0,) * dim} if args[0] else set()
        elif op == '+':
            value = out[args[0]] ^ out[args[1]]
        elif op == '*':
            value = product(out[args[0]], out[args[1]], bound)
        else:
            raise ValueError(op)
        out.append(value)
    return out


def jacobian(gates, guards, a):
    """First-order product rule at a; gradients are bitmasks of coordinates."""
    wires = []
    for op, *args in gates:
        if op == 'v':
            i = args[0]
            pair = a[i], 1 << i
        elif op == 'c':
            pair = args[0], 0
        else:
            av, ad = wires[args[0]]
            bv, bd = wires[args[1]]
            if op == '+':
                pair = av ^ bv, ad ^ bd
            elif op == '*':
                pair = av & bv, (bd if av else 0) ^ (ad if bv else 0)
            else:
                raise ValueError(op)
        wires.append(pair)
    return [wires[g][0] for g in guards], [wires[g][1] for g in guards]


def pivot_inverse(rows, n):
    """Reduce J alongside I; return each pivot and its row of (J_P)^(-1)."""
    rows = list(rows)
    transforms = [1 << i for i in range(len(rows))]
    pivots = []
    for col in range(n):
        k = len(pivots)
        candidate = next((i for i in range(k, len(rows)) if rows[i] >> col & 1), None)
        if candidate is None:
            continue
        rows[k], rows[candidate] = rows[candidate], rows[k]
        transforms[k], transforms[candidate] = transforms[candidate], transforms[k]
        for i in range(len(rows)):
            if i != k and rows[i] >> col & 1:
                rows[i] ^= rows[k]
                transforms[i] ^= transforms[k]
        pivots.append(col)
    if len(pivots) != len(rows):
        raise ValueError("Jacobian lacks full row rank at this point")
    return list(zip(pivots, transforms))


def lift(gates, guards, a, tangent, dim, bound):
    """Extend a + tangent to order bound, preserving every G_i(a)."""
    if bound < 1 or len(tangent) != len(a) or any(t < 0 or t >= 1 << dim for t in tangent):
        raise ValueError("invalid tangent or order")
    constants, rows = jacobian(gates, guards, a)
    pivots = pivot_inverse(rows, len(a))
    variables = [{u} for u in units(dim)]
    linear = [linear_combination(mask, variables) for mask in tangent]
    if any(linear_combination(row, linear) for row in rows):
        raise ValueError("non-tangent first-order substitution")
    one = {(0,) * dim}
    z = [(one if bit else set()) ^ p for bit, p in zip(a, linear)]
    corrections = {}
    for degree in range(2, bound + 1):
        values = jets(gates, z, dim, degree)
        residuals = [values[g] ^ (one if c else set()) for g, c in zip(guards, constants)]
        assert all(sum(u) == degree for p in residuals for u in p)
        corrections[degree] = 0
        for coord, inverse_row in pivots:
            delta = linear_combination(inverse_row, residuals)
            corrections[degree] += len(delta)
            z[coord] ^= delta
    evaluated = jets(gates, z, dim, bound)
    assert all(evaluated[g] == (one if c else set()) for g, c in zip(guards, constants))
    return z, corrections


def direct_composition(gates, z, dim, outputs):
    """Materialize the substituted circuit; independently expand with no cutoff."""
    composite = [('c', 0), ('c', 1)] + [('v', i) for i in range(dim)]
    coordinates = []
    for poly in z:
        terms = []
        for powers in sorted(poly):
            factors = [2 + j for j, exponent in enumerate(powers) for _ in range(exponent)]
            term = 1
            for f in factors:
                composite.append(('*', term, f))
                term = len(composite) - 1
            terms.append(term)
        total = 0
        for term in terms:
            composite.append(('+', total, term))
            total = len(composite) - 1
        coordinates.append(total)
    wires = []
    for op, *args in gates:
        if op == 'v':
            wire = coordinates[args[0]]
        elif op == 'c':
            wire = args[0]
        else:
            composite.append((op, wires[args[0]], wires[args[1]]))
            wire = len(composite) - 1
        wires.append(wire)
    return [formal_expansion(composite, wires[g], dim) for g in outputs]


def frobenius_test():
    # G=x+w+x²; its inverse series is x=w+w²+w⁴+w⁸+...
    gates = [('v', 0), ('v', 1), ('*', 0, 0), ('+', 0, 1), ('+', 3, 2)]
    for m in range(1, 9):
        z, corrections = lift(gates, [4], [0, 0], [1, 1], 1, m)
        powers = [1 << i for i in range(m.bit_length())]
        assert z == [{(p,) for p in powers}, {(1,)}]
        assert {j for j, count in corrections.items() if count} == set(powers[1:])
        assert direct_composition(gates, z, 1, [4]) == [{(2 * powers[-1],)}]


def square_tail_system():
    # Coordinates 1 and 2 pivot after the deliberately unused coordinate 0.
    # G0=x1+x3+x2+(x1*x2+x4)^2,
    # G1=1+x3+x2+x4+(x1*x3*x4+x2^3+G0)^2.
    # The remaining outputs test a product and the seventh power of G0+G1.
    g = [('v', i) for i in range(5)] + [('c', 1)]
    def add(op, l, r):
        g.append((op, l, r))
        return len(g) - 1
    h0 = add('+', add('*', 1, 2), 4)
    g0 = add('+', add('+', add('+', 1, 3), 2), add('*', h0, h0))
    h1 = add('+', add('*', add('*', 1, 3), 4), add('*', add('*', 2, 2), 2))
    h1 = add('+', h1, g0)
    g1 = add('+', add('+', add('+', add('+', 5, 3), 2), 4), add('*', h1, h1))
    joint = add('*', g0, g1)
    s = add('+', g0, g1)
    square = add('*', s, s)
    seventh = add('*', add('*', square, s), add('*', square, square))
    return g, [g0, g1], [joint, seventh]


def mixed_system():
    # G0=x0+x1*x2 and G1=x1+x0*x3 have a genuinely point-dependent Jacobian.
    g = [('v', i) for i in range(4)]
    g += [('*', 1, 2), ('+', 0, 4), ('*', 0, 3), ('+', 1, 6)]
    return g, [5, 7]


def verify_direct(gates, z, outputs, dim, bound):
    untruncated = direct_composition(gates, z, dim, outputs)
    clipped = jets(gates, z, dim, bound)
    for g, full in zip(outputs, untruncated):
        assert {u for u in full if sum(u) <= bound} == clipped[g]
    return any(sum(u) > bound for poly in untruncated for u in poly)


def systems_test():
    g, guards, downstream = square_tail_system()
    rng = Random(520771)
    points = list(cartesian((0, 1), repeat=5))
    direct = 0
    for idx, a in enumerate(points):
        constants, rows = jacobian(g, guards, a)
        assert rows == [0b01110, 0b11100]
        # First pivot in column 1, second in column 2. Choose free coordinates
        # 0,3,4 and solve for the two pivot derivatives to specify the tangent.
        f, s, t = [rng.randrange(4) for _ in range(3)]
        tangent = [f, t, s ^ t, s, t]
        z, _ = lift(g, guards, a, tangent, 2, 5)
        assert all(all(sum(u) <= 1 for u in z[k]) for k in (0, 3, 4))
        values = jets(g, z, 2, 5)
        expected = [constants[0] & constants[1], constants[0] ^ constants[1]]
        assert [values[q] for q in downstream] == [{(0, 0)} if c else set() for c in expected]
        if idx in (3, 11, 20, 28):
            verify_direct(g, z, guards, 2, 5)
            direct += 2
    g, guards = mixed_system()
    a = (1, 1, 1, 0)
    assert jacobian(g, guards, a)[1] == [0b0111, 0b1010]
    assert jacobian(g, guards, (0, 0, 0, 0))[1] != jacobian(g, guards, a)[1]
    try:
        lift(g, guards, a, [1, 0, 0, 0], 2, 2)
    except ValueError as error:
        assert "non-tangent" in str(error)
    else:
        raise AssertionError("expected a first-order obstruction")
    for m in range(2, 7):
        z, corrections = lift(g, guards, a, [3, 2, 1, 2], 2, m)
        assert corrections[2] and (1, 1) in (z[0] | z[1])
        assert verify_direct(g, z, guards, 2, m)
        direct += 2
    return len(points), direct


def singular_test():
    # G=x², a=0, tangent x=t. Degree two is t² for either quadratic
    # correction c*t² and stays t² after arbitrary higher-order corrections.
    gates = [('v', 0), ('*', 0, 0)]
    assert jacobian(gates, [1], [0]) == ([0], [0])
    for c in (0, 1):
        z = [{(1,)} | ({(2,)} if c else set())]
        assert jets(gates, z, 1, 2)[1] == {(2,)}
        full, = direct_composition(gates, z, 1, [1])
        assert full == ({(2,), (4,)} if c else {(2,)})
    try:
        lift(gates, [1], [0], [1], 1, 2)
    except ValueError as error:
        assert "rank" in str(error)
    else:
        raise AssertionError("expected a rank failure")


def fixed_baseline_case(m, rank, rng, rhs):
    """Solve dense affine crossing-weight equations, then expand the host h_m."""
    cities = list(range(m))
    arcs = [(v, w) for v in cities for w in cities if v != w]
    tails = rng.sample(cities, rank)
    pivots = [(v, rng.choice([w for w in cities if w != v])) for v in tails]
    endpoints = {v for e in pivots for v in e}
    fillers = rng.sample(sorted(set(cities) - endpoints), rank)
    core = sorted(set(cities) - set(tails + fillers))
    root = core[0]
    core_arcs = [(v, w) for v in core for w in core if v != w]
    dim = len(core_arcs)
    assert len(core) == m - 2 * rank and len(core) >= 2
    one = {(0,) * dim}
    weights = {e: set() for e in arcs}
    for (v, w), monomial in zip(core_arcs, units(dim)):
        weights[fillers[-1] if v == root else v, w] = {monomial}
    path = [root] + [v for pair in zip(tails, fillers) for v in pair]
    for e in zip(path, path[1:]):
        weights[e] = one.copy()
    assert all(not weights[e] for e in pivots)

    # Give the pivot minor full rank and choose every other entry independently.
    # In rank two the non-diagonal minor also exercises row operations.
    minor = [1] if rank == 1 else [0b11, 0b01]
    equations = []
    residuals = []
    for i, pivot_row in enumerate(minor):
        selected = {e for e in arcs if e not in pivots and rng.randrange(2)}
        selected.update(e for j, e in enumerate(pivots) if pivot_row >> j & 1)
        equations.append(selected)
        residual = one.copy() if rhs >> i & 1 else set()
        for e in selected:
            residual ^= weights[e]
        residuals.append(residual)
    for j, row in pivot_inverse(minor, rank):
        weights[pivots[j]] = linear_combination(row, residuals)
    for i, selected in enumerate(equations):
        lhs = set()
        for e in selected:
            lhs ^= weights[e]
        assert lhs == (one if rhs >> i & 1 else set())

    total = surviving = 0
    projected = set()
    for tail in permutations(cities[1:]):
        order = (cities[0],) + tail
        tour = list(zip(order, order[1:] + order[:1]))
        total += 1
        if all(weights[e] for e in tour):
            surviving += 1
            assert all(e not in pivots for e in tour)
            value = one
            for e in tour:
                value = product(value, weights[e], m)
            assert len(value) == 1 and value.isdisjoint(projected)
            projected ^= value
    expected = {tuple(mask >> j & 1 for j in range(dim)) for mask in tour_masks(len(core))}
    assert projected == expected
    active_pivots = sum(bool(weights[e]) for e in pivots)
    affine_pivots = sum((0,) * dim in weights[e] and len(weights[e]) > 1 for e in pivots)
    return total, surviving, active_pivots, affine_pivots


def fixed_baseline_tests():
    rng = Random(449321)
    instances = total = surviving = active = affine = 0
    for m, rank in ((5, 1), (6, 1), (6, 2), (7, 1), (7, 2)):
        for i in range(12):
            counts = fixed_baseline_case(m, rank, rng, i % (1 << rank))
            instances += 1
            total += counts[0]
            surviving += counts[1]
            active += counts[2]
            affine += counts[3]
    assert affine > 0
    return instances, total, surviving, active, affine


if __name__ == '__main__':
    frobenius_test()
    points, direct = systems_test()
    singular_test()
    print(f"8 Frobenius orders, {points} square-tail baselines, 5 mixed-Jacobian "
          f"orders, {direct + 8 + 2} independent full guard expansions, "
          "2 obstructed quadratic corrections passed")
    cases, total, surviving, active, affine = fixed_baseline_tests()
    print(f"{cases} affine crossing systems, {total} host tours, {surviving} "
          f"surviving tours, {active} nonzero pivot weights ({affine} with both "
          "constant and variable parts): all projections equal the core polynomial")
