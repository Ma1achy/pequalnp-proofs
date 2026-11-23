"""Streamed row constraints and global column parities for permutation matrices."""

from dataclasses import dataclass
from itertools import permutations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import encoded_bits, satisfied
from syndrome import solve, syndrome_prefixes


@dataclass(frozen=True)
class Encoding:
    size: int
    variables: int
    flats: tuple
    columns: tuple


def matching_encoding(m):
    if m < 1:
        raise ValueError('matrix size must be positive')
    columns = [0] * m
    row_factors = []
    for i in range(m):
        start = i * (2*m-1)
        for j in range(m):
            edge = 1 << (start + 2*j)
            left = 0 if j == 0 else edge >> 1
            right = 0 if j == m-1 else edge << 1
            # s_0 is fixed to zero; s_m=1 is folded into the last equation.
            rhs = int(j == m-1)
            row_factors.append((((left ^ edge ^ right) << 1) | (1 ^ rhs),))
            if left:
                row_factors.append(((left << 1) | 1, (edge << 1) | 1))
            columns[j] |= edge
    # Odd column equality is violated when its parity is zero.
    col_factors = tuple((col << 1,) for col in columns)
    return Encoding(m, m*(2*m-1), tuple(row_factors) + col_factors, col_factors)


def availability_encoding(m):
    """Visible availability bits precede each existential selected-edge bit."""
    base = matching_encoding(m)
    interior = []
    edge_tests = []
    available = []
    for i in range(m):
        for j in range(m):
            pos = i*(3*m-1) + 3*j
            available.append(pos)
            interior.append(pos+1)
            if j < m-1:
                interior.append(pos+2)
            edge_tests.append(((1 << (pos+2)) | 1, 1 << (pos+1)))

    def lift(row):
        new = row & 1
        vector = row >> 1
        while vector:
            low = vector & -vector
            new |= 1 << (1 + interior[low.bit_length()-1])
            vector ^= low
        return new

    local = [tuple(lift(row) for row in f) for f in base.flats[:-m]]
    cols = tuple((lift(col[0]),) for col in base.columns)
    result = Encoding(m, m*(3*m-1), tuple(local + edge_tests) + cols, cols)
    return result, available


def check_availability():
    for m in (1,2,3,4,5):
        encoding, available = availability_encoding(m)
        r, local_scope = independent_width_check(encoding)
        assert len(encoding.flats) == 3*m*m
        assert sum(map(len, encoding.flats)) == 5*m*m-m
        checked = 0
        if m <= 3:
            perms = permutation_masks(m)
            for g in range(1 << (m*m)):
                fixed = tuple(((1 << (pos+1)) | (1 ^ ((g >> j) & 1)),)
                              for j,pos in enumerate(available))
                answer = solve(encoding.flats + fixed, encoding.variables)
                assert answer == any((g & p) == p for p in perms)
                checked += 1
        print('availability m', m, 'vars', encoding.variables, 'clauses',len(encoding.flats),
              'dense_bits', encoded_bits(encoding.flats, encoding.variables), 'peak_rank', r,
              'local_scope', local_scope, 'graphs_checked', checked)


def lift_edges(m, edge_mask):
    """The unique interior flags computed by the prefix XOR recurrences."""
    point = 0
    for i in range(m):
        flag = 0
        for j in range(m):
            edge = (edge_mask >> (i*m+j)) & 1
            variable = i*(2*m-1)+2*j
            point |= edge << variable
            flag ^= edge
            if j+1 < m:
                point |= flag << (variable+1)
    return point


def permutation_masks(m):
    return {sum(1 << (i*m+j) for i,j in enumerate(p)) for p in permutations(range(m))}


def independent_width_check(instance):
    n = instance.variables
    columns = instance.columns
    local = instance.flats[:-len(columns)]
    scopes = []
    for flat in local:
        scope = 0
        for row in flat:
            scope |= row >> 1
        scopes.append(scope)
    local_peak = 0
    ranks = []
    for step, layer in enumerate(syndrome_prefixes(instance.flats, n)):
        past = (1 << step) - 1
        support = 0
        for scope in scopes:
            if scope & past:
                support |= scope & ~past
        touched_column_forms = sum(bool((col[0] >> 1) & past) and bool((col[0] >> 1) & ~past)
                                   for col in columns)
        assert support.bit_count() <= 2
        assert len(layer.basis) <= support.bit_count()+touched_column_forms <= instance.size+2
        local_peak = max(local_peak, support.bit_count())
        ranks.append(len(layer.basis))
    return max(ranks), local_peak


def check_prefixes(instance, solutions):
    modelset = {lift_edges(instance.size, mask) for mask in solutions}
    n = instance.variables
    checked = 0
    for layer in syndrome_prefixes(instance.flats, n):
        past = (1 << layer.step)-1
        untouched = [f for f in instance.flats if not any((row >> 1) & past for row in f)]
        expected = {v & ~past for v in modelset}
        for compact in range(1 << (n-layer.step)):
            v = compact << layer.step
            assert (layer.allows_touched(v) and satisfied(untouched, v)) == (v in expected)
            checked += 1
    return checked


def main():
    for m in (1,2,3,4,5,6,8):
        instance = matching_encoding(m)
        flats = instance.flats
        assert len(flats) == 2*m*m
        assert sum(map(len, flats)) == 3*m*m-m
        assert sum((row >> 1).bit_count() for flat in flats for row in flat) == 6*m*m-4*m
        semantics = prefixes = full = 0
        if m <= 4:
            wanted = permutation_masks(m)
            for x in range(1 << (m*m)):
                assert satisfied(flats, lift_edges(m,x)) == (x in wanted)
                semantics += 1
        if m <= 3:
            models = {lift_edges(m,x) for x in wanted}
            for point in range(1 << instance.variables):
                assert satisfied(flats, point) == (point in models)
                full += 1
            prefixes = check_prefixes(instance, wanted)
        rank, local_scope = independent_width_check(instance)
        assert rank == (m+2 if m >= 3 else (2 if m == 2 else 0))
        print('m',m,'vars',instance.variables,'clauses',len(flats),
              'dense_bits',encoded_bits(flats, instance.variables),'peak_rank',rank,
              'peak_row_suffix_coordinates',local_scope,'visible_patterns',semantics,
              'full_assignments',full,'prefix_suffix_checks',prefixes)


if __name__ == '__main__':
    main()
    check_availability()
