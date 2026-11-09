"""Exhaustively check the exact Lean proposition LastFactorLowIdeal."""

from itertools import product
import json
from pathlib import Path


FULL = (1 << 64) - 1
VARIABLES = tuple(sum(1 << x for x in range(64) if x >> i & 1) for i in range(6))
A0, A1, A2, B0, B1, B2 = VARIABLES
P0 = A0 & B0
Z1 = (A0 & B1) ^ (A1 & B0)
Z2 = (A0 & B2) ^ (A1 & B1) ^ (A2 & B0) ^ (P0 & A1 & B1)
EXTERNAL = (1 << 2) | (1 << 5)
LOW = (1 << 0) | (1 << 3)
BASE = (FULL, *VARIABLES, P0, Z1)
OFF = FULL ^ P0
NONCORE = sum(1 << m for m in range(64) if m.bit_count() >= 2 and m & EXTERNAL)


def span(generators):
    values = [0]
    for generator in generators:
        values += [value ^ generator for value in values]
    return values


LINEAR = span(VARIABLES)
BASE_VALUES = frozenset(span(BASE))
ZETA = tuple((1 << i, FULL ^ v) for i, v in enumerate(VARIABLES))


def anf(table):
    for shift, mask in ZETA:
        table ^= (table & mask) << shift
    return table


def bits(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word ^= low


def verify_space(space):
    """For each R, keep the indices of all w=1+k with wR=0 and w outside I."""
    functions = sorted(space)
    width = (len(functions) + 7) // 8
    masks = [bytearray(width) for _ in range(64)]
    nonideal = bytearray(width)
    for i, w in enumerate(functions):
        if w & OFF:
            nonideal[i // 8] |= 1 << (i % 8)
        for x in bits(w):
            masks[x][i // 8] |= 1 << (i % 8)
    support = [int.from_bytes(mask, "little") for mask in masks]
    initial = int.from_bytes(nonideal, "little")
    for v in functions:
        r = Z2 ^ v
        candidates = initial
        for x in bits(r):
            candidates &= ~support[x]
            if not candidates:
                break
        if candidates:
            w = functions[next(bits(candidates))]
            raise AssertionError(f"Found k={FULL ^ w:#x}, R={r:#x} outside conclusion")
    return len(functions) ** 2


def main():
    counts = [0, 0]
    representatives = {}
    for d, l, b in product(range(2), range(64), range(64)):
        if b & ~LOW == 0:
            continue
        c = ((P0 if d else 0) ^ LINEAR[l]) & LINEAR[b]
        if anf(c) & NONCORE == 0:
            continue
        counts[d] += 1
        # Equality of cosets over BASE is exactly equality of the PlusZ1 spaces.
        key = min(c ^ a for a in BASE_VALUES)
        representatives.setdefault(key, c)
    assert sum(counts) == 7200

    target_cases = factor_target_pairs = 0
    for c in representatives.values():
        space = BASE_VALUES | {c ^ a for a in BASE_VALUES}
        target_cases += len(space)
        factor_target_pairs += verify_space(space)

    # A nonlinear k is legal and fixes R, with k=1 only off the low ideal.
    c = P0 & A2
    k = FULL ^ c
    r = Z2 ^ B2 ^ FULL
    assert anf(c) & NONCORE and k & r == r
    assert (k ^ FULL) & OFF == 0 and k not in (FULL, FULL ^ P0)
    assert k ^ c in BASE_VALUES and r ^ Z2 in BASE_VALUES
    # Dropping the target-coset premise admits an actual counterexample.
    assert A0 & A0 == A0 and (A0 ^ FULL) & OFF and A0 ^ Z2 not in BASE_VALUES
    assert A0 ^ Z2 ^ c not in BASE_VALUES
    result = {
        "admissible_triples_by_d": counts,
        "distinct_plus_z1_spaces": len(representatives),
        "target_cases": target_cases,
        "factor_target_pairs_covered": factor_target_pairs,
        "positive_controls": 2,
        "failures": 0,
    }
    rendered = json.dumps(result, indent=2) + "\n"
    Path(__file__).with_name("check_lastfactor_results.json").write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
