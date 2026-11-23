"""Exhaust every affine flat in the five-bit local witness-label examples."""

from itertools import product

from verify_inner_product import affine_flats


def bits(point):
    return tuple((point >> column) & 1 for column in range(5))


def witness_labels(w1, w2, w3, nonlinear):
    p1 = w1 ^ (w2 & w3) if nonlinear else w1
    return p1, w2, w3, p1 ^ w2 ^ w3


def explicit_cover(block, nonlinear):
    """Fix x, and additionally w2 when the helper label has product w2*w3."""
    use_second_product = nonlinear and block in (0, 3)
    cover = []
    for fixed in product(range(2), repeat=1 + int(use_second_product)):
        a = fixed[0]
        current = set()
        for point in range(32):
            x, y, w1, w2, w3 = bits(point)
            if x != a or (use_second_product and w2 != fixed[1]):
                continue
            first_label = w1 ^ (fixed[1] & w3) if use_second_product else w1
            target = (first_label, w2, w3, first_label ^ w2 ^ w3)[block]
            if (a & y) ^ target == 1:
                current.add(point)
        cover.append(frozenset(current))
    return cover


def check(nonlinear, flats):
    label_vectors = {witness_labels(*w, nonlinear) for w in product(range(2), repeat=3)}
    assert len(label_vectors) == 8 and all(sum(p) % 2 == 0 for p in label_vectors)
    all_flats = set(flats)
    results = []
    for i in range(4):
        bad = set()
        for point in range(32):
            x, y, w1, w2, w3 = bits(point)
            if (x & y) != witness_labels(w1, w2, w3, nonlinear)[i]:
                bad.add(point)
        max_size = max(len(flat) for flat in flats if flat <= bad)
        cover = explicit_cover(i, nonlinear)
        assert all(f in all_flats and f <= bad for f in cover)
        assert set.union(set(), *cover) == bad
        assert sum(map(len, cover)) == len(bad) == max_size * len(cover)
        results.append((len(bad), max_size, len(cover)))
    assert sum(row[-1] for row in results) == (12 if nonlinear else 8)
    return results


if __name__ == "__main__":
    flats = [frozenset(points) for _, points in affine_flats(5)]
    assert len(set(flats)) == len(flats)
    print(f"{len(flats)} distinct nonempty affine flats in five bits")
    print("labeling | block | bad assignments | largest contained flat | optimal clauses")
    for nonlinear in (False, True):
        name = "nonlinear" if nonlinear else "linear"
        for i, result in enumerate(check(nonlinear, flats), 1):
            print(name, i, *result, sep=" | ")
