"""Prove the one- and two-bit values by exhaustive gate search and direct simulation."""

from itertools import combinations_with_replacement
import json
from pathlib import Path

CIRCUITS = Path(__file__).with_name("circuits.json")


def input_names(n):
    return tuple(f"{operand}{i}" for operand in ("a", "b") for i in range(n))


def target_bits(n, row):
    mask = (1 << n) - 1
    value = (row & mask) * (row >> n)
    return tuple((value >> j) & 1 for j in range(n))


def form(terms, signals):
    value = 0
    for name in terms:
        value ^= signals[name]
    return value


def check_upper(n, circuit, gate_count):
    names = input_names(n)
    if circuit["input_order"] != list(names) or len(circuit["gates"]) != gate_count:
        raise ValueError(f"Wrong inputs or gate count for n={n}")
    for row in range(1 << (2 * n)):
        signals = {name: (row >> i) & 1 for i, name in enumerate(names)}
        signals["1"] = 1
        for i, gate in enumerate(circuit["gates"]):
            signals[f"g{i}"] = form(gate["left"], signals) & form(gate["right"], signals)
        got = tuple(form(terms, signals) for terms in circuit["outputs"])
        if got != target_bits(n, row):
            raise ValueError(f"Upper-bound circuit failed at n={n}, row={row}")


def variable_tables(n):
    return tuple(sum(((row >> i) & 1) << row for row in range(1 << (2 * n)))
                 for i in range(2 * n))


def target_tables(n):
    tables = [0] * n
    for row in range(1 << (2 * n)):
        for i, bit in enumerate(target_bits(n, row)):
            tables[i] |= bit << row
    return tuple(tables)


def affine_tables(n, variables):
    rows = (1 << (1 << (2 * n))) - 1, *variables
    functions = [0]
    for row in rows:
        functions += [f ^ row for f in functions]
    return rows, functions


def quotient_reducer(generators):
    pivots = {}
    for value in generators:
        while value:
            high = value.bit_length() - 1
            if high not in pivots:
                pivots[high] = value
                break
            value ^= pivots[high]
    ordered = sorted(pivots.items(), reverse=True)

    def reduce(value):
        for high, pivot in ordered:
            if (value >> high) & 1:
                value ^= pivot
        return value

    return reduce


def search_two_gates():
    variables = variable_tables(2)
    affine_rows, affine = affine_tables(2, variables)
    reduce = quotient_reducer(affine_rows)
    targets = tuple(reduce(t) for t in target_tables(2))
    # Two gates can jointly compute a0*b0 and a0*b1.
    a0, _, b0, b1 = variables
    control = (reduce(a0 & b0), reduce(a0 & b1))
    first_products = {left & right for left, right in combinations_with_replacement(affine, 2)}
    affine_set = set(affine)
    second_pairs = actual_hits = control_hits = 0
    for first in sorted(first_products):
        space = affine if first in affine_set else affine + [f ^ first for f in affine]
        p = reduce(first)
        for left, right in combinations_with_replacement(space, 2):
            q = reduce(left & right)
            span = {0, p, q, p ^ q}
            actual_hits += targets[0] in span and targets[1] in span
            control_hits += control[0] in span and control[1] in span
            second_pairs += 1
    if actual_hits or not control_hits:
        raise AssertionError(f"Unexpected search result: {actual_hits=}, {control_hits=}")
    return {"affine_functions": len(affine), "first_factor_pairs": len(affine) * (len(affine) + 1) // 2,
            "distinct_first_products": len(first_products), "second_factor_pairs": second_pairs,
            "target_hits": actual_hits, "positive_control_hits": control_hits}


def check():
    circuits = json.loads(CIRCUITS.read_text(encoding="utf-8"))
    check_upper(1, circuits["1"], 1)
    check_upper(2, circuits["2"], 3)
    variables = variable_tables(1)
    _, affine = affine_tables(1, variables)
    if target_tables(1)[0] in affine or variables[0] ^ variables[1] not in affine:
        raise AssertionError("Unexpected zero-gate result")
    return {"status": "pass",
            "one_bit": {"mc": 1, "upper_rows": 4, "zero_gate_functions": len(affine),
                        "target_hits": 0, "positive_controls": 1},
            "two_bit": {"mc": 3, "upper_rows": 16, **search_two_gates(), "positive_controls": 1}}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
