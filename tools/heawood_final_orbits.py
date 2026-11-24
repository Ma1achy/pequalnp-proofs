#!/usr/bin/env python3
"""Enumerate Heawood boundary rows and last-gate private-witness orbits.

Bit v of an assignment mask is the value of input v, numbered 0 through 13.
The 58-bit signature orders the 21 edge masks as in the posted statement,
followed by the 37 maximal independent-set masks in increasing numerical order.
Run without arguments for the table, or use --json for machine-readable data.
"""

import argparse
import itertools
import json

EDGES = (
    (0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8),
    (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11),
    (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11),
)
VERTICES = range(14)
POSITIVE_ROWS = tuple((1 << u) | (1 << v) for u, v in EDGES)


def vertices(mask):
    return [v for v in VERTICES if mask & (1 << v)]


def has_edge(mask):
    return any((mask & pair) == pair for pair in POSITIVE_ROWS)


def negative_rows():
    return tuple(
        mask for mask in range(1 << 14)
        if not has_edge(mask)
        and all(has_edge(mask | (1 << v)) for v in VERTICES if not mask & (1 << v))
    )


def automorphisms():
    neighbors = [
        frozenset(w for w in VERTICES if (min(v, w), max(v, w)) in EDGES)
        for v in VERTICES
    ]
    # A connected bipartite graph has a unique bipartition up to swapping sides.
    reached = {0}
    while (extended := reached.union(*(neighbors[v] for v in reached))) != reached:
        reached = extended
    assert reached == set(VERTICES)
    result = []
    for first_side in (0, 7):
        candidates = range(first_side, first_side + 7)
        image_of_line = {neighbors[v]: v for v in VERTICES if v not in candidates}
        # A line is determined by its set of three points.
        assert len(image_of_line) == 7
        for points in itertools.permutations(candidates):
            lines = tuple(
                image_of_line.get(frozenset(points[i] for i in neighbors[v]))
                for v in range(7, 14)
            )
            if None in lines:
                continue
            permutation = points + lines
            assert set(permutation) == set(VERTICES)
            assert {tuple(sorted((permutation[u], permutation[v]))) for u, v in EDGES} == set(EDGES)
            result.append(permutation)
    return result


def image(mask, permutation):
    return sum(1 << permutation[i] for i in vertices(mask))


def orbit_table(rows, group, row_index):
    todo = set(itertools.combinations(sorted(rows), 2))
    row_set = set(rows)
    actions = [{a: image(a, perm) for a in rows} for perm in group]
    assert all(set(action.values()) == row_set for action in actions)
    result = []
    while todo:
        a, b = min(todo)
        orbit = {tuple(sorted((act[a], act[b]))) for act in actions}
        assert (a, b) == min(orbit) and orbit <= todo
        todo -= orbit
        result.append({
            'assignment_masks': [a, b],
            'vertices': [vertices(a), vertices(b)],
            'signature_indices': [row_index[a], row_index[b]],
            'orbit_size': len(orbit),
        })
    assert sum(row['orbit_size'] for row in result) == len(rows) * (len(rows) - 1) // 2
    return result


def normalization_certificate(orbit_records, rows, group, row_index):
    """For each pair give an automorphism sending it to the indicated representative."""
    perm_index = {perm: i for i, perm in enumerate(group)}
    inverse = [tuple(perm.index(k) for k in VERTICES) for perm in group]
    witnesses = {}
    for orbit_number, record in enumerate(orbit_records):
        a, b = record['assignment_masks']
        for k, perm in enumerate(group):
            x, y = image(a, perm), image(b, perm)
            pair = tuple(sorted((x, y)))
            if pair in witnesses:
                continue
            back = inverse[k]
            # Exchange the two final-gate operands if the image pair was reversed.
            swap = x > y
            normalized = [image(z, back) for z in pair]
            assert normalized == ([b, a] if swap else [a, b])
            witnesses[pair] = [
                row_index[pair[0]], row_index[pair[1]], orbit_number, perm_index[back], int(swap),
            ]
    assert set(witnesses) == set(itertools.combinations(sorted(rows), 2))
    return [witnesses[pair] for pair in sorted(witnesses)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', action='store_true', help='emit the boundary rows and orbit table as JSON')
    parser.add_argument('--certificate', action='store_true',
                        help='include explicit input permutations and a normalization witness for every pair')
    args = parser.parse_args()
    negative = negative_rows()
    rows = POSITIVE_ROWS + negative
    group = automorphisms()
    preserving = sum(perm[0] < 7 for perm in group)
    assert len(set(rows)) == 58 and len(negative) == 37
    assert len(set(group)) == 336 and preserving == 168
    row_index = {mask: i for i, mask in enumerate(rows)}
    positive_pairs = orbit_table(POSITIVE_ROWS, group, row_index)
    negative_pairs = orbit_table(negative, group, row_index)
    assert len(positive_pairs) == 3 and len(negative_pairs) == 13
    out = {
        'group': {'color_preserving': preserving, 'color_reversing': len(group) - preserving},
        'positive_assignment_masks': POSITIVE_ROWS,
        'negative_assignment_masks': negative,
        'target_signature': (1 << len(POSITIVE_ROWS)) - 1,
        'input_signatures': [sum(1 << i for i, mask in enumerate(rows) if mask & (1 << v)) for v in VERTICES],
        'or_final_positive_pairs': positive_pairs,
        'and_final_negative_pairs': negative_pairs,
    }
    if args.certificate:
        out['input_permutations'] = group
        out['witness_columns'] = ['signature_row_0', 'signature_row_1', 'orbit_number',
                                  'permutation_number', 'swap_operands']
        out['positive_witnesses'] = normalization_certificate(positive_pairs, POSITIVE_ROWS, group, row_index)
        out['negative_witnesses'] = normalization_certificate(negative_pairs, negative, group, row_index)
    if args.json or args.certificate:
        print(json.dumps(out, indent=2))
        return
    print(f'{len(POSITIVE_ROWS)} positive rows, {len(negative)} negative rows, {len(group)} automorphisms')
    for kind, orbits in [('OR', positive_pairs), ('AND', negative_pairs)]:
        print(f'{kind} final gate: {len(orbits)} unordered pair orbits')
        print('assignment masks   signature indices   orbit size')
        for record in orbits:
            a, b = record['assignment_masks']
            x, y = record['signature_indices']
            print(f'0x{a:04x} 0x{b:04x}        {x:2} {y:2}             {record["orbit_size"]:3}')


if __name__ == '__main__':
    main()
