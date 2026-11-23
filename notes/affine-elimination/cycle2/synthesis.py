"""Small exact synthesis bounds and a conflict-budgeted optional membership SAT search."""

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path


def odd(k, point):
    return ((point & ((1 << k) - 1)) & (point >> k)).bit_count() & 1


def masks(symbol):
    # Four helper words numbered in binary. Directions 1, 2, 3 are line normals.
    if symbol == 0:
        return (15,)
    if symbol == 4:
        return tuple(1 << p for p in range(4))
    return tuple(sum(1 << p for p in range(4) if (p & symbol).bit_count() % 2 == v)
                 for v in (0, 1))


def irredundant_cover(parts):
    union = 0
    for part in parts:
        union |= part
    if union != 15:
        return False
    for i in range(len(parts)):
        union_without = 0
        for j, part in enumerate(parts):
            if i != j:
                union_without |= part
        if union_without == 15:
            return False
    return True


def is_affine(points):
    if not points:
        return True
    start = next(iter(points))
    linear = {p ^ start for p in points}
    return all(a ^ b in linear for a in linear for b in linear)


def certificate_cost(shape):
    """Count flat pieces to represent the minimal-cover relation on these offsets."""
    inventories = [masks(symbol) for symbol in shape]
    widths = [(len(options) - 1).bit_length() for options in inventories]
    offsets = []
    for indices in product(*(range(len(options)) for options in inventories)):
        if irredundant_cover(tuple(options[i] for options, i in zip(inventories, indices))):
            point = 0
            for i, width in zip(indices, widths):
                point = (point << width) + i
            offsets.append(point)
    if not offsets:
        return 0
    if shape != (4, 4, 4, 4):
        assert is_affine(offsets), (shape, offsets)
        return 1
    # If p_i are the ordered points, choose one of three nonzero d=p_0+p_1.
    # Then p_2+p_3=d and p_0+p_2 is in the unique other coset of span(d).
    pieces = [{v for v in offsets if ((v >> 6) ^ (v >> 4)) & 3 == d} for d in (1, 2, 3)]
    assert sorted(map(len, pieces)) == [8, 8, 8]
    assert all(is_affine(piece) for piece in pieces)
    assert set.union(*pieces) == set(offsets)
    return 3


def cap_by_m(m):
    costs = {shape: certificate_cost(shape) for length in range(1, min(m, 4) + 1)
             for shape in combinations_with_replacement(range(5), length)}
    maximum = 0
    histogram = {}
    maximizers = []
    for types in combinations_with_replacement(range(5), m):
        cap = sum(costs[subset] for length in range(1, min(m, 4) + 1)
                  for subset in combinations(types, length))
        histogram[cap] = histogram.get(cap, 0) + 1
        if cap > maximum:
            maximum = cap
            maximizers = []
        if cap == maximum:
            maximizers.append(types)
    return {"m": m, "max_projected_flats": maximum, "maximizing_multisets": maximizers,
            "caps_histogram": histogram}


def flat_family_witness(k, h):
    """A concrete cover for k<=3, using at most six flats, checked pointwise below."""
    if k == 2:
        blocks = [[0, 1]]
    elif k == 3 and h >= 1:
        blocks = [[0], [1, 2]]
    else:
        blocks = [list(range(k))]
    flats = []
    for block in blocks:
        for pattern in range(1 << len(block)):
            if len(blocks) == 1 and pattern == 0:
                continue
            rows = [(1 << (1 + i)) | ((pattern >> j) & 1) for j, i in enumerate(block)]
            dot = sum(((pattern >> j) & 1) << (1 + k + i) for j, i in enumerate(block))
            helper = 1 << (1 + 2*k) if len(blocks) == 2 else 0
            rows.append(dot | helper | 1)
            flats.append(rows)
    return flats


def has_point(rows, point):
    return all(((row >> 1) & point).bit_count() % 2 == (row & 1) for row in rows)


def check_witness(k, h, flats):
    for point in range(1 << (2*k)):
        accepted = any(not any(has_point(flat, point | (w << (2*k))) for flat in flats)
                       for w in range(1 << h))
        assert accepted == (not odd(k, point))
    return {"k": k, "helpers": h, "clauses": len(flats), "visible_inputs_checked": 1 << (2*k),
            "augmented_rows": flats}


class Cnf:
    def __init__(self):
        self.count = 0
        self.rows = []

    def variable(self):
        self.count += 1
        return self.count

    def write(self, path):
        with path.open("w") as file:
            file.write(f"p cnf {self.count} {len(self.rows)}\n")
            for row in self.rows:
                file.write(" ".join(map(str, row)) + " 0\n")


def membership_cnf(k, h, m):
    n = 2*k + h
    size = 1 << n
    visible = 1 << (2*k)
    cnf = Cnf()
    membership = [[cnf.variable() for _ in range(size)] for _ in range(m)]
    for group in membership:
        for delta in range(1, size):
            direction = cnf.variable()
            for point in range(size):
                other = point ^ delta
                if other <= point:
                    continue
                a, b = group[point], group[other]
                cnf.rows.extend(((-a, -b, direction), (-direction, -a, b), (-direction, a, -b)))
    for v in range(visible):
        lifted = [v + w*visible for w in range(1 << h)]
        if odd(k, v):
            cnf.rows.extend(tuple(group[q] for group in membership) for q in lifted)
        elif v == 0 or v & (v - 1) == 0:
            # Translate witnesses by an affine helper-valued function of the input.
            cnf.rows.extend((-group[v],) for group in membership)
        else:
            witnesses = [cnf.variable() for _ in lifted]
            cnf.rows.append(witnesses)
            for q, witness in zip(lifted, witnesses):
                cnf.rows.extend((-witness, -group[q]) for group in membership)
    # Symmetric flat labels can be sorted lexicographically by incidence.
    first_bad = next(v for v in range(visible) if odd(k, v))
    order = [first_bad] + [q for q in range(size) if q != first_bad]
    for left, right in zip(membership, membership[1:]):
        prefix = cnf.variable()
        cnf.rows.append((prefix,))
        for q in order:
            a, b = left[q], right[q]
            cnf.rows.append((-prefix, a, -b))
            nxt = cnf.variable()
            cnf.rows.extend(((-prefix, -a, -b, nxt), (-prefix, a, b, nxt)))
            prefix = nxt
    return cnf, membership


def as_rows(points, n):
    if not points:
        return (1,)  # An inconsistent equation. This neutral clause can be dropped.
    origin = next(iter(points))
    linear = {p ^ origin for p in points}
    rows = []
    for v in range(1, 1 << n):
        if all((v & u).bit_count() % 2 == 0 for u in linear):
            rows.append((v << 1) + (int(v & origin).bit_count() % 2))
    assert all(has_point(rows, p) == (p in points) for p in range(1 << n))
    return rows


def sat_probe(k, h, m, solver, budget):
    cnf, membership = membership_cnf(k, h, m)
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp, "input.cnf")
        cnf.write(path)
        result = subprocess.run([solver, "-q", "-c", str(budget), str(path)], capture_output=True,
                                text=True, check=False)
    status = {0: "UNKNOWN", 10: "SAT", 20: "UNSAT-reported"}.get(result.returncode)
    if status is None:
        raise RuntimeError(result.stderr or result.stdout)
    out = {"k": k, "helpers": h, "m": m, "variables": cnf.count, "cnf_clauses": len(cnf.rows),
           "conflict_budget": budget, "status": status}
    if status == "SAT":
        positive = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
                    for v in line.split()[1:] if int(v) > 0}
        assert all(any((lit in positive) if lit > 0 else (-lit not in positive) for lit in row)
                   for row in cnf.rows)
        flats = [as_rows({p for p, v in enumerate(group) if v in positive}, 2*k+h) for group in membership]
        out["verified_witness"] = check_witness(k, h, flats)
    return out


def check_domain_geometry():
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from verify_inner_product import affine_flats

    by_dim = [set() for _ in range(7)]
    many_odd = []
    for dimension, flat in affine_flats(6):
        weight = sum(odd(3, v) for v in flat)
        by_dim[dimension].add(weight)
        if dimension == 4 and weight == 10:
            many_odd.append(flat)
    assert [max(weights) for weights in by_dim] == [1, 2, 4, 6, 10, 16, 28]
    # A hyperplane section inside any 10-odd four-flat never has its four odd
    # points forming a plane. Deduplicate directions inducing the same section.
    checked_sections = 0
    for flat in many_odd:
        seen = set()
        for form in range(1, 64):
            for rhs in (0, 1):
                section = tuple(v for v in flat if (v & form).bit_count() % 2 == rhs)
                if len(section) != 8 or section in seen:
                    continue
                seen.add(section)
                odd_points = [v for v in section if odd(3, v)]
                assert len(odd_points) != 4 or not is_affine(odd_points)
                checked_sections += 1
    return {"odd_counts_by_flat_dimension": [sorted(w) for w in by_dim],
            "four_flats_with_ten_odd_points": len(many_odd),
            "hyperplane_sections_of_ten_odd_flats_checked": checked_sections}


def five_clause_profiles():
    fixed = {}
    for shape in combinations_with_replacement(range(5), 5):
        cap = sum(certificate_cost(subset) for size in range(1, 5)
                  for subset in combinations(shape, size))
        if cap >= 7:
            profile = (shape.count(0), tuple(sorted((shape.count(i) for i in (1, 2, 3)), reverse=True)),
                       shape.count(4))
            fixed[profile] = cap
    return [{"cylinders": c, "line_direction_counts": lines, "points": p, "cap": value}
            for (c, lines, p), value in sorted(fixed.items())]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--probe", action="store_true", help="run bounded CaDiCaL synthesis probes")
    parser.add_argument("--solver", default=shutil.which("cadical"))
    parser.add_argument("--conflicts", type=int, default=2000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error("run with Python assertions enabled")
    result = {"caps": [cap_by_m(m) for m in range(1, 6)],
              "one_helper_geometry": check_domain_geometry(),
              "five_clause_profiles_passing_shape_count": five_clause_profiles(),
              "witnesses": [check_witness(k, h, flat_family_witness(k, h)) for k in (2, 3)
                            for h in (1, 2)]}
    if args.probe:
        if not args.solver:
            parser.error("--probe needs CaDiCaL on PATH or --solver PATH")
        version = subprocess.check_output([args.solver, "--version"], text=True).strip()
        result["solver_version"] = version
        result["probes"] = [sat_probe(k, h, m, args.solver, args.conflicts)
                            for k, h, m in ((2, 2, 3), (3, 1, 5), (3, 2, 5))]
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
