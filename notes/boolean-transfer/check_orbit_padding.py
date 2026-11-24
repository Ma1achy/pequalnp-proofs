#!/usr/bin/env python3
"""Check F₂ diagonal specialization and square-root padding for Hamiltonicity.

For prime p and a a power of p, take p vertex classes of size a, with all
arcs from each class to the next cyclic class. Classwise cyclic translations
and rotation of the classes generate (C_a)^p ⋊ C_p. Each group element is a
class rotation with a vector of displacements, one per source class. These
give p*a^p distinct permutations, a p-power. Every arc can move to any arc
by rotating its source class and translating its two distinct endpoint
classes. Only the empty and full arc subsets are invariant, because every
invariant subset is a union of arc orbits. Other subset orbits have size
divisible by p. Hamiltonicity and its canonical multilinear coefficients are
invariant, so all proper nonempty coefficient orbits vanish on sending every
arc variable to t over F_p. The constant is zero, and the value at t=1 is one
by the cyclic class-by-class spanning tour. The resulting formal polynomial
is t^(p*a²), before univariate Boolean reduction.

For p=2 this template is bidirected K_{a,a}. The program independently
computes the decision polynomial by exhaustive subset Möbius transform where
there are at most eight arcs, and certifies the group action on larger graphs.
It also checks greedy assemblies of these gadgets and a final bidirected
cycle. Such a cycle on b>=3 vertices has two disjoint directed orientations;
their OR specializes over F₂ to t^b+t^b+t^(2b)=t^(2b).
"""

from argparse import ArgumentParser
from itertools import permutations
from math import isqrt, sqrt


def action_certificate(p, a):
    n = p*a
    vertices = range(n)
    edges = [(c*a+x, ((c+1) % p)*a+y) for c in range(p) for x in range(a) for y in range(a)]
    edge_index = {edge: bit for bit, edge in enumerate(edges)}
    generators = [tuple(c*a + (u+1) % a if u//a == c else u for u in vertices) for c in range(p)]
    generators.append(tuple((u+a) % n for u in vertices))

    # The generators have the displacement/rotation normal form described
    # above. Enumerate that group independently for the smaller orders.
    order = p*a**p
    prime_power = order
    while prime_power % p == 0:
        prime_power //= p
    assert prime_power == 1
    if order <= 256:
        identity = tuple(vertices)
        group = {identity}
        queue = [identity]
        while queue:
            element = queue.pop()
            for g in generators:
                image = tuple(g[u] for u in element)
                if image not in group:
                    group.add(image)
                    queue.append(image)
        assert len(group) == order

    # Check every generator preserves the template, and close a single arc
    # under the generators rather than enumerating any large subset spaces.
    orbit = {edges[0]}
    pending = [edges[0]]
    while pending:
        u, v = pending.pop()
        for g in generators:
            image = (g[u], g[v])
            assert image in edge_index
            if image not in orbit:
                orbit.add(image)
                pending.append(image)
    assert len(orbit) == len(edges) == p*a*a
    cycle = [c*a+i for i in range(a) for c in range(p)]
    assert len(set(cycle)) == n and all((cycle[i-1], cycle[i]) in edge_index for i in vertices)
    print(f"p={p}, a={a}: group order {order}, one orbit of {len(edges)} arcs, spanning cycle verified")
    if len(edges) > 8:
        return

    # All rooted vertex permutations give an independent Hamiltonicity oracle.
    tours = []
    for tail in permutations(range(1, n)):
        order = (0, *tail)
        walk = [(order[i-1], order[i]) for i in vertices]
        if all(e in edge_index for e in walk):
            tours.append(sum(1 << edge_index[e] for e in walk))
    size = 1 << len(edges)
    decision = bytearray(any(mask & tour == tour for tour in tours) for mask in range(size))
    anf = decision.copy()
    for j in range(len(edges)):
        for mask in range(size):
            if mask & (1 << j):
                anf[mask] = (anf[mask] - anf[mask ^ (1 << j)]) % p
    diagonal = [0]*(len(edges)+1)
    fixed = set(range(size))
    for mask, coefficient in enumerate(anf):
        degree = mask.bit_count()
        diagonal[degree] = (diagonal[degree] + coefficient) % p
    for g in generators:
        images = [1 << edge_index[g[u], g[v]] for u, v in edges]
        for mask in range(size):
            image = sum(bit for j, bit in enumerate(images) if mask & (1 << j))
            assert decision[image] == decision[mask] and anf[image] == anf[mask]
            if image != mask:
                fixed.discard(mask)
    assert fixed == {0, size-1} and diagonal == [0]*len(edges) + [1]
    print(f"  {size} edge subgraphs: diagonal over F_{p} = t^{len(edges)}")


def padding_plan(k):
    """Return (side size, copies) pairs in decreasing order and a final cycle."""
    if k < 3:
        raise ValueError("the residual cycle requires k >= 3")
    budget = k-3
    pieces = []
    while budget >= 4:
        # The largest permitted integer side is floor((1+sqrt(1+2*budget))/2).
        limit = (1 + isqrt(1 + 2*budget))//2
        a = 1 << (limit.bit_length()-1)
        copies, budget = divmod(budget, 2*a*(a-1))
        pieces.append((a, copies))
    return pieces, budget+3


def check_plan(k):
    pieces, cycle = padding_plan(k)
    vertices = cycle
    arcs = 2*cycle
    residual = k
    for a, copies in pieces:
        surplus = 2*a*(a-1)
        assert a >= 2 and a & (a-1) == 0
        assert surplus <= residual-3 < 4*a*(2*a-1)
        assert copies == (residual-3)//surplus
        residual -= copies*surplus
        vertices += copies*2*a
        arcs += copies*2*a*a
    assert 3 <= cycle == residual <= 6 and arcs-vertices == k
    # Proof of this bound: through k=26, every selected bipartite piece has
    # a=2, so V(k)=k. Otherwise maximality gives k<8a² with a>=4. Hence
    # sqrt(k)<=3a<=4(a-1), so sqrt(k)-sqrt(k-s)>=s/(2 sqrt(k))>=a/4,
    # where s=2a(a-1). Induction now pays 2a vertices from 8*(sqrt(k)-sqrt(k-s)).
    assert vertices*vertices <= 64*k
    return vertices


def main():
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-k", type=int, default=100000)
    args = parser.parse_args()
    if not __debug__ or args.max_k < 3:
        parser.error("run with assertions enabled and --max-k at least 3")
    for p in (2, 3, 5):
        for a in (1, p, p*p):
            action_certificate(p, a)
    best_k, best_v = 3, 3
    for k in range(3, args.max_k+1):
        vertices = check_plan(k)
        if vertices*vertices*best_k > best_v*best_v*k:
            best_k, best_v = k, vertices
    boundaries = set()
    for j in range(1, 65):
        a = 1 << j
        threshold = 3 + 2*a*(a-1)
        boundaries.update((threshold-1, threshold, threshold+1))
    for k in sorted(boundaries):
        check_plan(k)
    print(f"k=3..{args.max_k}: exact surplus and V(k) <= 8 sqrt(k) throughout; "
          f"peak observed V/sqrt(k) = {best_v/sqrt(best_k):.6f} at k={best_k}")
    print(f"{len(boundaries)} further threshold checks through side size 2^64")


if __name__ == "__main__":
    main()
