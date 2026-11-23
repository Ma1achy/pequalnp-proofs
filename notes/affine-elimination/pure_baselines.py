"""Independent decision algorithms for the two pure input classes."""

def gaussian_decision(raw, n):
    """Batch forward elimination of the linear equations required by all unit clauses."""
    if any(len(flat) != 1 for flat in raw):
        raise ValueError("expected one forbidden equation per clause")
    # For each forbidden equation, its complement is the required equation.
    matrix = [flat[0] ^ 1 for flat in raw]
    rank = probes = row_xors = 0
    for col in range(n):
        bit = 1 << (col + 1)
        pivot = None
        for i in range(rank, len(matrix)):
            probes += 1
            if matrix[i] & bit:
                pivot = i
                break
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        for i in range(rank + 1, len(matrix)):
            probes += 1
            if matrix[i] & bit:
                matrix[i] ^= matrix[rank]
                row_xors += 1
        rank += 1
    return not any(row == 1 for row in matrix), {
        "rank_of_coefficients": rank, "coefficient_probes": probes, "row_xors": row_xors,
    }


def two_sat_decision(raw, n):
    """Iterative Kosaraju SCC on the literal implication graph for ordinary 2-CNF."""
    graph = [[] for _ in range(2 * n)]
    reverse = [[] for _ in range(2 * n)]
    for flat in raw:
        if not flat:
            return False, {"empty_clause": True}
        if len(flat) > 2:
            raise ValueError("expected at most two ordinary literals")
        vertices = []
        for row in flat:
            mask = row >> 1
            if mask == 0 or mask & (mask - 1) or mask.bit_length() > n:
                raise ValueError("expected an ordinary literal")
            vertices.append(2 * (mask.bit_length() - 1) + (row & 1))
        # A false-value 0 row means the clause asks for x, vertex 2*i.
        if len(vertices) == 1:
            vertices *= 2
        a, b = vertices
        for source, dest in ((a ^ 1, b), (b ^ 1, a)):
            graph[source].append(dest)
            reverse[dest].append(source)
    visited = [False] * len(graph)
    order = []
    for start in range(len(graph)):
        if visited[start]:
            continue
        visited[start] = True
        stack = [(start, 0)]
        while stack:
            node, index = stack[-1]
            if index == len(graph[node]):
                order.append(node)
                stack.pop()
                continue
            nxt = graph[node][index]
            stack[-1] = node, index + 1
            if not visited[nxt]:
                visited[nxt] = True
                stack.append((nxt, 0))
    labels = [-1] * len(graph)
    component_count = 0
    for start in reversed(order):
        if labels[start] >= 0:
            continue
        labels[start] = component_count
        todo = [start]
        while todo:
            for nxt in reverse[todo.pop()]:
                if labels[nxt] < 0:
                    labels[nxt] = component_count
                    todo.append(nxt)
        component_count += 1
    sat = all(labels[2 * i] != labels[2 * i + 1] for i in range(n))
    return sat, {"vertices": 2 * n, "directed_edges": sum(map(len, graph)), "scc_count": component_count}
