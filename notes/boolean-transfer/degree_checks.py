"""Check an OR restriction and the canonical top layer of a rooted-walk circuit."""

from itertools import permutations, product
from math import factorial, isqrt


def tour_edges(order):
    return tuple(zip(order, order[1:] + order[:1]))


def walk_parity_language(word):
    n = (isqrt(1 + 4 * len(word)) - 1) // 2
    if n < 2 or n * (n + 1) != len(word):
        return False
    state = [1] + [0] * (n - 1)
    for _ in range(n):
        state = [sum(state[i] * word[i] * word[n + i * n + j]
                     for i in range(n) if i != j) % 2
                 for j in range(n)]
    return bool(state[0])


def test_walk_language(n):
    walks = []
    for interior in product(range(n), repeat=n - 1):
        steps = tour_edges((0,) + interior)
        if all(i != j for i, j in steps):
            walks.append({k for i, j in steps for k in (i, n + i * n + j)})
    length = n * (n + 1)
    for word in product((0, 1), repeat=length):
        direct = sum(all(word[i] for i in walk) for walk in walks) % 2
        assert walk_parity_language(word) == bool(direct)
    return 1 << length


def test_or_restriction(n):
    first_size = n // 2
    free = {(i, j): j - first_size + i * (n - first_size)
            for i in range(first_size) for j in range(first_size, n)}
    tour_needs = []
    for rest in permutations(range(1, n)):
        edges = tour_edges((0,) + rest)
        tour_needs.append(sum(1 << free[e] for e in edges if e in free))
    coefficients = []
    for mask in range(1 << len(free)):
        # Every loopless arc outside 'free' is fixed present.
        value = any(needed & mask == needed for needed in tour_needs)
        assert value == bool(mask)
        coefficients.append(int(value))
    for j in range(len(free)):
        bit = 1 << j
        for mask in range(len(coefficients)):
            if mask & bit:
                coefficients[mask] ^= coefficients[mask ^ bit]
    assert coefficients == [0] + [1]*((1 << len(free))-1)
    return len(free), len(coefficients)


def add_term(poly, key, value, modulus):
    result = poly.get(key, 0) + value
    if modulus:
        result %= modulus
    if result:
        poly[key] = result
    else:
        poly.pop(key, None)


def test_walk(n, modulus):
    # First n variables mark source vertices. Then come n*n edge coordinates,
    # including unused loops. Base 2**bits is larger than every exponent.
    bits = n.bit_length()
    edge = {(i, j): (1 << (bits*i)) + (1 << (bits*(n+n*i+j)))
            for i in range(n) for j in range(n) if i != j}
    current = [{0: 1}] + [{} for _ in range(n-1)]
    for _ in range(n):
        updated = [{} for _ in range(n)]
        for (i, j), weight in edge.items():
            for monomial, coefficient in current[i].items():
                add_term(updated[j], monomial + weight, coefficient, modulus)
        current = updated
    raw = current[0]

    direct = {}
    for intermediate in product(range(n), repeat=n-1):
        edges = tour_edges((0,) + intermediate)
        if all(e in edge for e in edges):
            add_term(direct, sum(edge[e] for e in edges), 1, modulus)
    assert direct == raw

    projected = {}
    for monomial, coefficient in raw.items():
        exponents = [(monomial >> (bits*j)) & ((1 << bits)-1) for j in range(n+n*n)]
        assert sum(exponents) == 2*n
        support = sum(1 << j for j, exponent in enumerate(exponents) if exponent)
        if support.bit_count() == 2*n:
            assert support & ((1 << n)-1) == (1 << n)-1
            # Specialize every marker to one.
            add_term(projected, support >> n, coefficient, modulus)
    wanted = {sum(1 << (i*n+j) for i, j in tour_edges((0,) + rest)): 1
              for rest in permutations(range(1, n))}
    assert len(wanted) == factorial(n-1)
    assert projected == wanted
    return len(raw), len(projected)


def main():
    for n in (2, 3):
        assignments = test_walk_language(n)
        print(f'walk-parity language n={n}: {assignments} marked inputs checked')
    for length in range(20):
        if length not in (6, 12):
            assert not walk_parity_language([1] * length)
    for n in range(2, 7):
        rank, graphs = test_or_restriction(n)
        print(f'OR restriction n={n}: {rank} free inputs, {graphs} graphs checked')
    for n in range(2, 6):
        for modulus in (0, 2, 3):
            raw, layer = test_walk(n, modulus)
            print(f'closed walks n={n}, characteristic {modulus}: '
                  f'{raw} surviving formal monomials, {layer} tour monomials')
    # A single length-four closed walk and no four-vertex Hamiltonian cycle.
    arcs = {(0,1), (1,0)}
    assert sum(all(e in arcs for e in tour_edges((0,) + p))
               for p in product(range(4), repeat=3)) == 1
    assert not any(all(e in arcs for e in tour_edges((0,) + p))
                   for p in permutations(range(1,4)))


if __name__ == '__main__':
    main()
