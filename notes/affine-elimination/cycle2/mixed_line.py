"""A five-flat existential encoding of even inner product on three pairs."""
import json
from collections import Counter
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import Counts, metrics, normalize, project, satisfied


def five_flats():
    # Coordinate order x1,x2,x3,y1,y2,y3,h,t. Row bit zero is the RHS.
    x1, x2, x3, y1, y2, y3, h, t = (1 << i for i in range(8))
    return (
        (h << 1, t << 1),
        ((h ^ x1) << 1, (t ^ x2) << 1),
        ((h ^ y2) << 1, (t ^ y1) << 1),
        ((h ^ x1 ^ y2) << 1, (t ^ x2 ^ y1 ^ x3) << 1),
        ((x3 << 1) | 1, (h ^ x1 ^ y2 ^ y3) << 1),
    )


def literal_model(v):
    x1, x2, x3, y1, y2, y3 = ((v >> j) & 1 for j in range(6))
    A = x1 | (x2 << 1)
    B = y2 | (y1 << 1)
    points = [0, A, B, A ^ B ^ (x3 << 1)]
    forbidden = set(points)
    if x3:
        h_line = x1 ^ y2 ^ y3
        forbidden.update((h_line, h_line|2))
        odd_labels = [p for p in range(4) if points.count(p)%2]
        assert len(odd_labels) == 2 and odd_labels[0]^odd_labels[1] == 2
        line = odd_labels[0]&1
        assert line == ((x1*y1) ^ (x2*y2) ^ x1 ^ y2)
        assert not {1^line, (1^line)|2}.issubset(set(points))
    return forbidden


def main():
    raw = five_flats()
    by_witnesses = Counter()
    essential = [None]*len(raw)
    for v in range(64):
        odd = (v & (v >> 3)).bit_count() & 1
        direct = literal_model(v)
        forbidden = set()
        for w in range(4):
            failed = [i for i,f in enumerate(raw) if not satisfied([f], v | (w << 6))]
            if failed:
                forbidden.add(w)
            if odd and len(failed) == 1 and essential[failed[0]] is None:
                essential[failed[0]] = (v,w)
        assert forbidden == direct
        assert (len(forbidden)==4) == bool(odd)
        by_witnesses[4-len(forbidden)] += 1
    assert all(v is not None for v in essential)
    orders = []
    for order in ((6,7), (7,6)):
        counts = Counts()
        current = normalize(raw, 8, counts)
        sizes = [metrics(current,8)]
        for step,h in enumerate(order, start=1):
            current = project(current,h,8,counts)
            sizes.append(metrics(current,8))
            eliminated = order[:step]
            mask = sum(1 << j for j in eliminated)
            for v in range(256):
                expected = any(satisfied(raw,(v & ~mask) | sum(((w >> a)&1) << j
                                                               for a,j in enumerate(eliminated)))
                               for w in range(1 << step))
                assert satisfied(current,v) == expected
        orders.append(dict(order=order, stages=sizes, operations=counts.as_dict()))
    print(json.dumps(dict(rows=raw, initial=metrics(raw,8), direct_assignments=256,
                          visible_assignments_by_number_of_witnesses=dict(sorted(by_witnesses.items())),
                          odd_clause_deletion_witnesses=essential, projection_point_checks=1024,
                          traces=orders), indent=2))


if __name__ == '__main__':
    main()
