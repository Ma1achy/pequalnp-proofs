"""Parsimoniously reduce signed exact-one formulas to simple directed Hamiltonicity.

Use positive/negative signed, one-based variable indices. Repeated literals are
distinct occurrences. Run this module to compare every tour with truth tables.
"""

from dataclasses import dataclass
from itertools import combinations_with_replacement, permutations, product
from random import Random


@dataclass(frozen=True)
class GadgetGraph:
    outgoing: tuple[int, ...]  # Row masks, with vertices numbered from zero.
    variable_entries: tuple[tuple[int, int, int], ...]  # Junction, true and false endpoints.

    def decode(self, successors):
        assignment = []
        for junction, true_entry, false_entry in self.variable_entries:
            assert successors[junction] in (true_entry, false_entry)
            assignment.append(successors[junction] == true_entry)
        return tuple(assignment)


def build_graph(variables, clauses):
    if variables < 0:
        raise ValueError('variable count must be nonnegative')
    clauses = tuple(tuple(clause) for clause in clauses)
    occurrences = [[] for _ in range(variables)]
    for c, clause in enumerate(clauses):
        for i, literal in enumerate(clause):
            if not 1 <= abs(literal) <= variables:
                raise ValueError(f'literal {literal} outside declared variable range')
            occurrences[abs(literal) - 1].append((c, i, literal))

    rows = []

    def vertex():
        rows.append(0)
        return len(rows) - 1

    def arc(source, target):
        assert source != target and not rows[source] & (1 << target)
        rows[source] |= 1 << target

    root = vertex()
    junction = vertex()
    arc(root, junction)
    entries = []
    false_arcs = {}
    for variable_occurrences in occurrences:
        next_junction = vertex()
        path = [vertex() for _ in range(max(1, len(variable_occurrences)) + 1)]
        entries.append((junction, path[0], path[-1]))
        for endpoint in (path[0], path[-1]):
            arc(junction, endpoint)
            arc(endpoint, next_junction)
        if not variable_occurrences:
            arc(path[0], path[1])
            arc(path[1], path[0])
        for j, (c, i, literal) in enumerate(variable_occurrences):
            left, right = path[j:j+2]
            false_arc = (right, left) if literal > 0 else (left, right)
            false_arcs[c, i] = false_arc
            arc(*reversed(false_arc))
        junction = next_junction

    for c, clause in enumerate(clauses):
        next_junction = vertex()
        for i in range(len(clause)):
            source, target = false_arcs[c, i]
            left, middle, right = vertex(), vertex(), vertex()
            for origin, end in ((left, middle), (middle, left), (middle, right),
                                (right, middle), (source, left), (right, target),
                                (junction, right), (left, next_junction)):
                arc(origin, end)
        junction = next_junction
    arc(junction, root)
    return GadgetGraph(tuple(rows), tuple(entries))


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def hamiltonian_successors(outgoing):
    """Enumerate successor permutations using only ordinary adjacency data."""
    n = len(outgoing)

    def search(rows):
        while True:
            if any(row == 0 for row in rows):
                return
            forced = [row for row in rows if row.bit_count() == 1]
            if len(set(forced)) != len(forced):
                return
            used = sum(forced)
            narrowed = [row if row.bit_count() == 1 else row & ~used for row in rows]
            if narrowed != rows:
                rows = narrowed
                continue
            incoming = [0] * n
            for i, row in enumerate(rows):
                for bit in bits(row):
                    incoming[bit.bit_length() - 1] |= 1 << i
            if any(column == 0 for column in incoming):
                return
            tail_forced = rows.copy()
            for j, column in enumerate(incoming):
                if column.bit_count() == 1:
                    tail_forced[column.bit_length() - 1] &= 1 << j
            if tail_forced != rows:
                rows = tail_forced
                continue
            break

        # Any closed forced orbit on fewer than n vertices is a proper subtour.
        seen = set()
        for i in range(n):
            v = i
            path = set()
            while v not in seen and rows[v].bit_count() == 1:
                seen.add(v)
                path.add(v)
                v = rows[v].bit_length() - 1
            if v in path:
                # Forced successors are injective, hence this path is the cycle.
                if len(path) == n:
                    yield tuple(row.bit_length() - 1 for row in rows)
                return
        i = min((i for i in range(n) if rows[i].bit_count() > 1),
                key=lambda v: rows[v].bit_count())
        for choice in bits(rows[i]):
            branch = rows.copy()
            branch[i] = choice
            yield from search(branch)

    yield from search(list(outgoing))


def truth(variables, clauses):
    for assignment in product((False, True), repeat=variables):
        if all(sum(assignment[abs(lit)-1] == (lit > 0) for lit in clause) == 1
               for clause in clauses):
            yield assignment


def check_formula(variables, clauses):
    graph = build_graph(variables, clauses)
    solutions = set(truth(variables, clauses))
    decoded = set()
    for successors in hamiltonian_successors(graph.outgoing):
        assignment = graph.decode(successors)
        assert assignment in solutions and assignment not in decoded
        decoded.add(assignment)
    assert decoded == solutions
    k = sum(len(c) for c in clauses)
    u = variables - len({abs(lit) for c in clauses for lit in c})
    assert len(graph.outgoing) == 2 + 2*variables + len(clauses) + 4*k + u
    assert sum(row.bit_count() for row in graph.outgoing) == 2 + 4*variables + 9*k + 2*u
    return len(decoded)


def check_counter():
    total = 0
    for n in range(2, 5):
        edges = [(i, j) for i in range(n) for j in range(n) if i != j]
        for mask in range(1 << len(edges)):
            rows = [0] * n
            for k, (i, j) in enumerate(edges):
                if mask & 1 << k:
                    rows[i] |= 1 << j
            expected = 0
            for tail in permutations(range(1, n)):
                order = (0, *tail)
                expected += all(rows[i] & 1 << j for i, j in zip(order, order[1:] + order[:1]))
            assert sum(1 for _ in hamiltonian_successors(rows)) == expected
            total += 1
    return total


def main():
    print(f'Independent rooted-permutation checks: {check_counter()} loopless graphs', flush=True)
    cases = tours = 0
    for variables in range(3):
        literals = tuple(j for x in range(1, variables+1) for j in (x, -x))
        clauses = [c for size in range(4) for c in combinations_with_replacement(literals, size)]
        for size in range(3):
            for formula in combinations_with_replacement(clauses, size):
                tours += check_formula(variables, formula)
                cases += 1
    rng = Random(81191)
    for _ in range(80):
        variables = rng.randint(2, 5)
        formula = [tuple(rng.choice((-1, 1)) * rng.randint(1, variables)
                         for _ in range(rng.randint(1, 4)))
                   for _ in range(rng.randint(1, 5))]
        tours += check_formula(variables, formula)
        cases += 1
    print(f'Exact-one formula checks: {cases} graphs, {tours} tours matched bijectively')


if __name__ == '__main__':
    main()
