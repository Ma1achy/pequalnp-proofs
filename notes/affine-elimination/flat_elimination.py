"""Exact projection of a conjunction of affine clauses over F₂.

Each clause forbids one affine flat. In each integer row, bit 0 is the
right-hand side and bit i+1 is the coefficient of variable i. Empty row sets
describe the whole space. None denotes an inconsistent (empty) flat internally.
"""

from dataclasses import asdict, dataclass
from itertools import combinations


@dataclass
class Counts:
    """Event counts, not timings or a claim of instruction-level accounting."""

    rref_calls: int = 0
    pivot_tests: int = 0
    row_xors: int = 0
    input_rows_to_rref: int = 0
    empty_flats_discarded: int = 0
    duplicate_flats_discarded: int = 0
    containment_tests: int = 0
    contained_flats_discarded: int = 0
    parallel_merges: int = 0
    grouping_passes: int = 0
    cylinder_flats: int = 0
    graph_flats: int = 0
    graph_pairs: int = 0
    candidates_emitted: int = 0
    candidate_rows_emitted: int = 0
    max_candidate_width_before_rref: int = 0
    max_rref_basis_rows: int = 0
    max_consistent_flats_before_simplification: int = 0
    max_consistent_rows_before_simplification: int = 0

    def as_dict(self):
        return asdict(self)


def clause(*signed_lits):
    """Return the unique falsifying flat. Literals use signed, 1-based DIMACS IDs."""
    if any(lit == 0 for lit in signed_lits):
        raise ValueError("0 is not a DIMACS literal")
    return tuple((1 << abs(lit)) | int(lit < 0) for lit in signed_lits)


def parity(variables, rhs):
    """Forbid violation of the XOR equation on zero-based variable IDs."""
    if rhs not in (0, 1):
        raise ValueError("expected a bit on the right")
    row = 1 ^ rhs
    for variable in variables:
        if variable < 0:
            raise ValueError("negative variable index")
        row ^= 1 << (variable + 1)
    return (row,)


def rref(rows, n, counts):
    """Reduced equations, highest variable index first, or None if inconsistent."""
    counts.rref_calls += 1
    basis = {}
    for row in rows:
        counts.input_rows_to_rref += 1
        if row < 0 or row.bit_length() > n + 1:
            raise ValueError("row outside the specified variable universe")
        for pivot in sorted(basis, reverse=True):
            counts.pivot_tests += 1
            if row & pivot:
                row ^= basis[pivot]
                counts.row_xors += 1
        if row <= 1:
            if row:
                counts.empty_flats_discarded += 1
                return None
            continue
        pivot = 1 << (row.bit_length() - 1)
        for old_pivot, old_row in basis.items():
            counts.pivot_tests += 1
            if old_row & pivot:
                basis[old_pivot] ^= row
                counts.row_xors += 1
        basis[pivot] = row
        counts.max_rref_basis_rows = max(counts.max_rref_basis_rows, len(basis))
    return tuple(basis[pivot] for pivot in sorted(basis, reverse=True))


def _contained(inner, outer, counts):
    """Test whether all outer equations follow from the consistent inner system."""
    counts.containment_tests += 1
    for row in outer:
        for generator in inner:
            pivot = 1 << (generator.bit_length() - 1)
            counts.pivot_tests += 1
            if row & pivot:
                row ^= generator
                counts.row_xors += 1
        if row:
            return False
    return True


def _antichain(flats, counts):
    ordered = sorted(set(flats), key=lambda flat: (len(flat), flat))
    counts.duplicate_flats_discarded += len(flats) - len(ordered)
    result = []
    for flat in ordered:
        # Equal-rank consistent flats are comparable only if equal.
        if any(len(other) < len(flat) and _contained(flat, other, counts)
               for other in result):
            counts.contained_flats_discarded += 1
        else:
            result.append(flat)
    return result


def _merge_parallel(left, right, n, counts):
    # Same RREF linear parts. Remove one differing RHS coordinate. XOR it
    # into each other differing coordinate. The union has one fewer
    # independent equation and one more affine dimension.
    anchor = next(i for i, (a, b) in enumerate(zip(left, right)) if a != b)
    rows = []
    for i, (a, b) in enumerate(zip(left, right)):
        if i == anchor:
            continue
        if a != b:
            a ^= left[anchor]
            counts.row_xors += 1
        rows.append(a)
    counts.parallel_merges += 1
    merged = rref(rows, n, counts)
    assert merged is not None
    return merged


def _simplify_canonical(flats, n, counts, merge):
    counts.max_consistent_flats_before_simplification = max(
        counts.max_consistent_flats_before_simplification, len(flats))
    counts.max_consistent_rows_before_simplification = max(
        counts.max_consistent_rows_before_simplification, sum(map(len, flats)))
    result = _antichain(flats, counts)
    while merge:
        counts.grouping_passes += 1
        groups = {}
        for flat in result:
            direction = tuple(row >> 1 for row in flat)
            groups.setdefault(direction, []).append(flat)
        if all(len(group) == 1 for group in groups.values()):
            break
        merged = []
        for group in groups.values():
            for i in range(0, len(group) - 1, 2):
                merged.append(_merge_parallel(group[i], group[i + 1], n, counts))
            if len(group) % 2:
                merged.append(group[-1])
        result = _antichain(merged, counts)
    return tuple(result)


def normalize(raw_flats, n, counts, merge=True):
    if n < 0:
        raise ValueError("negative variable count")
    consistent = []
    for rows in raw_flats:
        flat = rref(rows, n, counts)
        if flat is not None:
            consistent.append(flat)
    return _simplify_canonical(consistent, n, counts, merge)


def project(flats, variable, n, counts, merge=True):
    """Existentially eliminate variable. The input must be normalized.

    Columns use the same variable IDs in the output. Its rows have zero
    coefficient at 'variable', so evaluating either value gives the same result.
    """
    if not 0 <= variable < n:
        raise ValueError("variable outside the specified universe")
    bit = 1 << (variable + 1)
    candidates = []
    graphs = []
    for flat in flats:
        pivot_index = None
        for i, row in enumerate(flat):
            counts.pivot_tests += 1
            if row & bit:
                pivot_index = i
                break
        if pivot_index is None:
            counts.cylinder_flats += 1
            candidates.append(flat)
            continue
        pivot = flat[pivot_index]
        domain = []
        for i, row in enumerate(flat):
            if i == pivot_index:
                continue
            counts.pivot_tests += 1
            if row & bit:
                row ^= pivot
                counts.row_xors += 1
            domain.append(row)
        graphs.append((tuple(domain), pivot ^ bit))
        counts.row_xors += 1
        counts.graph_flats += 1

    # Two graphs rule out both branches exactly where their domains overlap
    # and their prescribed z-values disagree.
    for (domain_a, value_a), (domain_b, value_b) in combinations(graphs, 2):
        counts.graph_pairs += 1
        counts.row_xors += 2
        rows = domain_a + domain_b + (value_a ^ value_b ^ 1,)
        counts.candidates_emitted += 1
        counts.candidate_rows_emitted += len(rows)
        counts.max_candidate_width_before_rref = max(counts.max_candidate_width_before_rref, len(rows))
        candidate = rref(rows, n, counts)
        if candidate is not None:
            candidates.append(candidate)
    return _simplify_canonical(candidates, n, counts, merge)


def _gamma_bits(positive):
    return 2 * positive.bit_length() - 1


def encoded_bits(flats, n):
    """Gamma(n+1), gamma(m+1), then gamma(k+1) and k dense (n+1)-bit rows per flat."""
    return (_gamma_bits(n + 1) + _gamma_bits(len(flats) + 1)
            + sum(_gamma_bits(len(flat) + 1) + (n + 1) * len(flat) for flat in flats))


def metrics(flats, n):
    return {
        "flats": len(flats),
        "rows": sum(map(len, flats)),
        "max_clause_width": max(map(len, flats), default=0),
        "dense_encoded_bits": encoded_bits(flats, n),
        "max_packed_row_bits": max((row.bit_length() for f in flats for row in f), default=0),
        "max_coefficient_bits": max((int(row != 0) for f in flats for row in f), default=0),
    }


def satisfied(flats, assignment):
    """Return whether the union of the forbidden flats misses this assignment."""
    return not any(all(((assignment & (row >> 1)).bit_count() & 1) == (row & 1)
                       for row in flat) for flat in flats)


def decide(raw_flats, n, merge=True):
    """Decide the input in ascending order of its original variable IDs."""
    flats = normalize(raw_flats, n, Counts(), merge)
    for variable in range(n):
        if not flats or flats == ((),):
            break
        flats = project(flats, variable, n, Counts(), merge)
    return not flats
