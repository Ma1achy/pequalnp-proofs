"""Decide a topologically ordered Boolean circuit via exact affine-clause elimination.

JSON example: {"gates":[["input"],["input"],["and",0,1],["not",2]],"output":3}
Each list element creates a wire. An input wire represents one distinct variable.
"""

import argparse
import json
from pathlib import Path

from flat_elimination import Counts, clause, normalize, project, satisfied


ARITY = {"input": 0, "false": 0, "true": 0, "not": 1, "and": 2, "or": 2}


def validate(gates, output):
    if type(output) is not int or not 0 <= output < len(gates):
        raise ValueError("output must be an existing zero-based wire ID")
    for index, gate in enumerate(gates):
        if not isinstance(gate, (list, tuple)) or not gate or not isinstance(gate[0], str):
            raise ValueError(f"invalid gate at wire {index}")
        op, *args = gate
        if op not in ARITY or len(args) != ARITY[op]:
            raise ValueError(f"unknown operation or wrong arity at wire {index}")
        if any(type(arg) is not int or not 0 <= arg < index for arg in args):
            raise ValueError(f"wire {index} uses an invalid predecessor")


def encode(gates, output):
    validate(gates, output)
    raw = [clause(output + 1)]
    inputs = []
    for index, (op, *args) in enumerate(gates):
        v = index + 1
        parents = [j + 1 for j in args]
        if op == "input":
            inputs.append(index)
        elif op in ("true", "false"):
            raw.append(clause(v if op == "true" else -v))
        elif op == "not":
            a, = parents
            raw.extend((clause(-v, -a), clause(v, a)))
        elif op == "and":
            a, b = parents
            raw.extend((clause(-v, a), clause(-v, b), clause(v, -a, -b)))
        elif op == "or":
            a, b = parents
            raw.extend((clause(v, -a), clause(v, -b), clause(-v, a, b)))
    return inputs, raw


def decide(gates, output):
    _, raw = encode(gates, output)
    n = len(gates)
    counts = Counts()
    state = normalize(raw, n, counts)
    for variable in reversed(range(n)):
        state = project(state, variable, n, counts)
    return satisfied(state, 0)


def check():
    from itertools import product

    def wire_value(op, values):
        if op == "not":
            return not values[0]
        if op == "and":
            return all(values)
        if op == "or":
            return any(values)
        return op == "true"

    def choices(parents):
        yield ["true"]
        yield ["false"]
        for i in range(parents):
            yield ["not", i]
        for op, i, j in product(("and", "or"), range(parents), range(parents)):
            yield [op, i, j]

    checked = 0
    for first, second in product(choices(2), choices(3)):
        gates = [["input"], ["input"], first, second]
        for output in range(len(gates)):
            inputs, raw = encode(gates, output)
            assert inputs == [0, 1]
            results = []
            for point in range(4):
                values = [bool(point & 1), bool(point & 2)]
                for op, *args in (first, second):
                    values.append(wire_value(op, [values[j] for j in args]))
                witnesses = [mask for mask in range(4)
                             if satisfied(raw, point | (mask << 2))]
                expected_mask = int(values[2]) | (int(values[3]) << 1)
                assert witnesses == ([expected_mask] if values[output] else [])
                results.append(values[output])
            assert decide(gates, output) == any(results)
            checked += 1
    assert not decide([["false"]], 0)
    assert decide([["true"]], 0)
    return checked + 2


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check", action="store_true")
    action.add_argument("--input", type=Path, help="JSON circuit file")
    args = parser.parse_args()
    if args.check:
        print(f"{check()} circuit/output cases passed")
    else:
        obj = json.loads(args.input.read_text())
        print("SAT" if decide(obj["gates"], obj["output"]) else "UNSAT")
