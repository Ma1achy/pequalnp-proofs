"""Reproduce all checks and measurements with python3 syndrome_checks.py."""

import json
import random
from itertools import combinations, permutations

from flat_elimination import encoded_bits, satisfied
from syndrome import solve, syndrome_prefixes


def check_prefixes(flats, n, order):
    full_mask = (1 << n) - 1
    universe = range(1 << n)
    satisfying = [a for a in universe if satisfied(flats, a)]
    past = 0
    points_checked = 0
    for i, layer in enumerate(syndrome_prefixes(flats, n, order)):
        if i:
            past |= 1 << order[i - 1]
        suffix = full_mask ^ past
        untouched = []
        touched = []
        for flat in flats:
            scope = 0
            for row in flat:
                scope |= row >> 1
            (touched if not scope or scope & past else untouched).append(flat)
        expected = {a & suffix for a in satisfying}
        expected_touched = {a & suffix for a in universe if satisfied(touched, a)}
        for y in universe:
            if y & past:
                continue
            touched_bit = layer.allows_touched(y)
            assert touched_bit == (y in expected_touched), (i, y, flats, order)
            assert (touched_bit and satisfied(untouched, y)) == (y in expected)
            points_checked += 1
    return points_checked


def all_plane_flats():
    # Whole plane, all 6 lines, all 4 points, and the inconsistent equation.
    return ([()] + [((mask << 1) | rhs,) for mask in (1, 2, 3) for rhs in (0, 1)]
            + [(2 | (x & 1), 4 | (x >> 1)) for x in range(4)] + [(1,)])


def profile(flats, n):
    layers = list(syndrome_prefixes(flats, n))
    r = max(len(layer.basis) for layer in layers)
    # Encode carried flats with the shared dense codec, gamma(rank+1), the
    # dense basis masks, and one semantic bit per table entry. The order is
    # fixed here; these are layer encodings, excluding interpreter overhead.
    state_bits = []
    max_forbidden_width = 0
    scopes = []
    for flat in flats:
        scope = 0
        for row in flat:
            scope |= row >> 1
        scopes.append(scope)
    for layer in layers:
        past = (1 << layer.step) - 1
        untouched = [flat for flat, scope in zip(flats, scopes) if scope and not scope & past]
        rank = len(layer.basis)
        state_bits.append(encoded_bits(untouched, n) + 2 * (rank + 1).bit_length() - 1
                          + n * rank + len(layer.table))
        max_forbidden_width = max(max_forbidden_width,
                                  max(map(len, untouched), default=0),
                                  rank if 0 in layer.table else 0)
    return dict(variables=n, input_bits=encoded_bits(flats, n),
                max_logical_state_bits=max(state_bits),
                max_equivalent_forbidden_width=max_forbidden_width,
                max_input_clause_width=max(map(len, flats), default=0),
                max_coefficient_bits=int(any(row >> 1 for flat in flats for row in flat)),
                max_input_packed_row_bits=max((row.bit_length() for flat in flats for row in flat), default=0),
                max_basis_row_bits=max((row.bit_length() for layer in layers for row in layer.basis), default=0),
                max_coordinate_boundary=max(layer.coordinate_frontier for layer in layers),
                max_rank=r, max_syndrome_table_entries=1 << r,
                first_projection_bad_syndromes=layers[1].table.count(0),
                table_entries_by_prefix=[len(layer.table) for layer in layers],
                basis_xors=sum(layer.basis_xors for layer in layers),
                branches_evaluated=sum(layer.branches_evaluated for layer in layers),
                row_parities_evaluated=sum(layer.row_parities_evaluated for layer in layers),
                satisfiable=bool(layers[-1].table[0]))


def dense_case(k):
    # (z or P) and (~z or Q), with disjoint nonempty parities P and Q.
    p = sum(1 << i for i in range(1, k + 1, 2))
    q = sum(1 << i for i in range(2, k + 1, 2))
    return [(2, p << 1), (3, q << 1)]


def or_case(k):
    # (z or x1 ... or xk) and ~z.
    return [tuple(1 << (i + 1) for i in range(k + 1)), (3,)]


def main():
    plane = all_plane_flats()
    exhaustive_cases = 0
    prefix_points = 0
    for length in range(len(plane) + 1):
        for flats in combinations(plane, length):
            for order in permutations(range(2)):
                prefix_points += check_prefixes(flats, 2, order)
                exhaustive_cases += 1
    seed = 381431223
    rng = random.Random(seed)
    random_cases = 400
    for _ in range(random_cases):
        n = rng.randrange(7)
        order = rng.sample(range(n), n)
        flats = [tuple(rng.randrange(1 << (n + 1)) for _ in range(rng.randrange(n + 3)))
                 for _ in range(rng.randrange(10))]
        prefix_points += check_prefixes(flats, n, order)
    for n in range(4):
        assert solve([], n)
        assert not solve([()], n)
        assert solve([(1,)], n)
    results = {}
    for name, make, sizes in [('dense_disjoint_parities', dense_case, (4, 16, 64, 256)),
                              ('projected_or', or_case, (4, 8, 12, 16))]:
        results[name] = []
        for k in sizes:
            result = profile(make(k), k + 1)
            assert result['max_rank'] == (2 if name == 'dense_disjoint_parities' else k)
            assert result['max_coordinate_boundary'] == k
            assert result['first_projection_bad_syndromes'] == 1
            assert result['satisfiable']
            if k <= 8:
                prefix_points += check_prefixes(make(k), k + 1, range(k + 1))
            results[name].append(result)
    print(json.dumps(dict(exhaustive_two_variable_formula_order_pairs=exhaustive_cases,
                          random_seed=seed, random_cases=random_cases,
                          suffix_points_checked=prefix_points,
                          profiles=results), indent=2))


if __name__ == '__main__':
    main()
