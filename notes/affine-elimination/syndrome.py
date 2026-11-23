"""Exact existential projection on a table of affine boundary values.

Input uses flat_elimination.py's row encoding: (coefficient_mask << 1) | rhs.
A flat is forbidden where every one of its equations is satisfied. Variable
indices stay fixed even when a nontrivial elimination order is supplied.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Layer:
    step: int
    basis: tuple[int, ...]
    table: bytes
    coordinate_frontier: int
    new_factors: int
    branches_evaluated: int
    row_parities_evaluated: int
    basis_xors: int

    def allows_touched(self, suffix_assignment):
        """Evaluate the projected touched factors, excluding all untouched factors."""
        syndrome = sum(((row & suffix_assignment).bit_count() & 1) << j
                       for j, row in enumerate(self.basis))
        return bool(self.table[syndrome])


def _basis_and_coordinates(vectors):
    """Return an echelon basis, every input row's coordinates, and XOR count."""
    by_pivot = {}
    xors = 0
    for row in vectors:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in by_pivot:
                by_pivot[pivot] = row
                break
            row ^= by_pivot[pivot]
            xors += 1
    pivots = sorted(by_pivot, reverse=True)
    basis = tuple(by_pivot[pivot] for pivot in pivots)
    coordinates = []
    for row in vectors:
        coordinate = 0
        for j, (pivot, basis_row) in enumerate(zip(pivots, basis)):
            if row & (1 << pivot):
                coordinate |= 1 << j
                row ^= basis_row
                xors += 1
        assert row == 0
        coordinates.append(coordinate)
    return basis, coordinates, xors


def _buckets(flats, n, order):
    buckets = [[] for _ in order]
    initial_ok = True
    for flat in flats:
        scope = 0
        for row in flat:
            if not isinstance(row, int) or row < 0 or row.bit_length() > n + 1:
                raise ValueError("row outside the specified variable universe")
            scope |= row >> 1
        if not scope:
            # In this case every left-hand side is the constant zero.
            initial_ok = initial_ok and any(row & 1 for row in flat)
            continue
        first = next(i for i, variable in enumerate(order) if scope & (1 << variable))
        buckets[first].append(flat)
    return initial_ok, buckets


def syndrome_prefixes(flats, n, order=None):
    """Yield prefix states. At step n the sole table entry is the SAT answer.

    Use solve() for decision without retaining previous tables. A different order
    may have a different cost. The algorithm never searches for an order.
    """
    if n < 0:
        raise ValueError("negative variable count")
    order = tuple(range(n) if order is None else order)
    if sorted(order) != list(range(n)):
        raise ValueError("order must be a permutation of the variable indices")
    initial_ok, buckets = _buckets([tuple(flat) for flat in flats], n, order)
    basis = ()
    table = bytes([initial_ok])
    yield Layer(0, basis, table, 0, 0, 0, 0, 0)

    for step, (variable, arriving) in enumerate(zip(order, buckets), start=1):
        bit = 1 << variable
        forms = list(basis) + [row >> 1 for flat in arriving for row in flat]
        residuals = [mask & ~bit for mask in forms]
        next_basis, coords, xors = _basis_and_coordinates(residuals)
        # A descriptor gives the residual-syndrome mask and value at b=1
        # added by the removed column. For a flat row, fold in its RHS too.
        descriptors = [(coord, bool(mask & bit))
                       for coord, mask in zip(coords[:len(basis)], basis)]
        row_index = len(basis)
        predicates = []
        for flat in arriving:
            predicate = []
            for row in flat:
                predicate.append((coords[row_index], bool(forms[row_index] & bit), row & 1))
                row_index += 1
            predicates.append(predicate)
        next_table = bytearray(1 << len(next_basis))
        parity_tests = 0
        branches = 0
        for t in range(len(next_table)):
            for b in (0, 1):
                branches += 1
                previous = 0
                for j, (coord, active) in enumerate(descriptors):
                    value = ((t & coord).bit_count() & 1) ^ (active and b)
                    previous |= value << j
                    parity_tests += 1
                if not table[previous]:
                    continue
                forbidden = False
                for predicate in predicates:
                    forbidden = True
                    for coord, active, rhs in predicate:
                        value = ((t & coord).bit_count() & 1) ^ (active and b)
                        parity_tests += 1
                        if value != rhs:
                            forbidden = False
                            break
                    if forbidden:
                        break
                if not forbidden:
                    next_table[t] = 1
                    break

        basis = next_basis
        table = bytes(next_table)
        support = 0
        for mask in basis:
            support |= mask
        yield Layer(step, basis, table, support.bit_count(), len(arriving),
                    branches, parity_tests, xors)


def solve(flats, n, order=None):
    for layer in syndrome_prefixes(flats, n, order):
        pass
    return bool(layer.table[0])
