"""Verify a row-ordered tour CNF and the matching-to-tour restriction."""

from itertools import combinations, permutations, product
from math import factorial
from pathlib import Path
from random import Random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from flat_elimination import clause, encoded_bits, satisfied


def tour_cnf(m):
    if m < 2:
        raise ValueError("at least two vertices are needed")
    width = (m - 1).bit_length()
    edges = [(i, j) for i in range(m) for j in range(m) if i != j]
    e = {edge: v + 1 for v, edge in enumerate(edges)}
    p = [[len(edges) + 1 + i * width + b for b in range(width)] for i in range(m)]
    flats = []

    def unequal(i, value):
        return [-v if value >> b & 1 else v for b, v in enumerate(p[i])]

    for i in range(m):
        outgoing = [e[i, j] for j in range(m) if i != j]
        flats.append(clause(*outgoing))
        for u, v in combinations(outgoing, 2):
            flats.append(clause(-u, -v))
        for a in range(m, 1 << width):
            flats.append(clause(*unequal(i, a)))
    for v in p[0]:
        flats.append(clause(-v))
    for (i, j), v in e.items():
        for a in range(m):
            for b, pos in enumerate(p[j]):
                bit = ((a + 1) % m) >> b & 1
                flats.append(clause(-v, *unequal(i, a), pos if bit else -pos))
    return edges, p, flats


def middle_rank_profile(n, flats):
    """In an ordinary CNF each residual coefficient row is a coordinate vector."""
    scopes = [sum({row >> 1 for row in flat}) for flat in flats]
    profile = []
    for i in range(n + 1):
        prefix = (1 << i) - 1
        suffix_scope = 0
        for scope in scopes:
            if scope & prefix:
                suffix_scope |= scope & ~prefix
        profile.append(suffix_scope.bit_count())
    return profile


def one_cycle(successors):
    visited = set()
    vertex = 0
    while vertex not in visited:
        visited.add(vertex)
        vertex = successors[vertex]
    return vertex == 0 and len(visited) == len(successors)


def check_cnf(m):
    edges, p, flats = tour_cnf(m)
    width = len(p[0])
    n = len(edges) + m * width
    profile = middle_rank_profile(n, flats)
    assert max(profile) <= m * width + m - 2

    # Non-functional edge choices falsify an outgoing-row clause independently
    # of all labels. Test every edge mask for m<=4, checking all label words
    # on every functional choice (and directly on every mask for m<=3).
    witnesses = 0
    labels_checked = 0
    edge_only = [f for f in flats if all(row >> (len(edges) + 1) == 0 for row in f)]
    for edge_mask in range(1 << len(edges)):
        selected = [j for index, (i, j) in enumerate(edges) if edge_mask >> index & 1]
        tails = [i for index, (i, j) in enumerate(edges) if edge_mask >> index & 1]
        functional = tails == list(range(m))
        if not functional and m > 3:
            # Filter immutable edge-only clauses from the actual encoding.
            assert not satisfied(edge_only, edge_mask)
            continue
        count = 0
        for label_mask in range(1 << (m * width)):
            labels_checked += 1
            count += satisfied(flats, edge_mask | (label_mask << len(edges)))
        assert count == int(functional and one_cycle(selected))
        witnesses += count
    assert witnesses == factorial(m - 1)
    return len(flats), encoded_bits(flats, n), max(profile), labels_checked, witnesses


def check_slice(k, extras):
    """Check every matching and connector for a miniature cut-coloured example."""
    rng = Random(27493 + extras)
    perms = list(permutations(range(k)))
    red_arcs = {(u, v) for u in range(k) for v in range(k) if u == v or rng.randrange(5)}
    blue_arcs = {(u, v) for u in range(k) for v in range(k) if u == k-1-v or rng.randrange(5)}
    red = [p for p in perms if all((i, v) in red_arcs for i, v in enumerate(p))]
    blue = [p for p in perms if all((i, v) in blue_arcs for i, v in enumerate(p))]
    bar = tuple(reversed(range(k)))
    total_successful = 0
    connector_counts = []
    for mu in perms:
        good = 0
        for alpha, beta in product(red, blue):
            m = 4*k + extras
            successor = [None] * m
            for j in range(k):
                successor[j] = k + alpha[j]
                successor[k+j] = 2*k + bar[j]
                successor[2*k+j] = 3*k + beta[j]
                successor[3*k+j] = mu[j]
            if extras:
                successor[3*k] = 4*k
                for j in range(4*k, m-1):
                    successor[j] = j+1
                successor[m-1] = mu[0]
            composition = [mu[beta[bar[alpha[i]]]] for i in range(k)]
            assert one_cycle(successor) == one_cycle(composition)
            good += one_cycle(composition)
        connector_counts.append(good)
        total_successful += good
    assert total_successful * k == len(red) * len(blue) * factorial(k)
    assert max(connector_counts) * k >= len(red)*len(blue)
    return len(red), len(blue), total_successful, max(connector_counts)


if __name__ == "__main__":
    print("m | clauses | dense bits | max rank | direct label assignments checked | tours")
    for m in range(2, 5):
        print(m, *check_cnf(m), sep=" | ")
    print("k | leftover vertices | red choices | blue choices | successes over all connectors | best")
    for k in (2, 3, 4):
        for extras in (0, 2):
            print(k, extras, *check_slice(k, extras), sep=" | ")
