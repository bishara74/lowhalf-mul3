"""Discover and serialize five-gate witnesses by an exact product-coset search."""

import json
from itertools import combinations
from pathlib import Path

INPUTS = ("a0", "a1", "a2", "b0", "b1")
SIGNALS = ("1", *INPUTS, "g0", "g1", "g2", "g3", "g4")
FULL = (1 << 32) - 1
X = tuple(sum(((x >> i) & 1) << x for x in range(32)) for i in range(5))
A0, A1, A2, B0, B1 = X
PREFIX = (A0 & B0, A0 & B1, A1 & B0)
BASE = (FULL, *X, *PREFIX)


def span(rows):
    values = [0]
    for row in rows:
        values += [value ^ row for value in values]
    return values


def base_eliminator():
    pivots = {}
    for i, row in enumerate(BASE):
        coefficients = 1 << i
        while row:
            high = row.bit_length() - 1
            if high not in pivots:
                pivots[high] = row, coefficients
                break
            pivot, tag = pivots[high]
            row ^= pivot
            coefficients ^= tag
    ordered = sorted(pivots.items(), reverse=True)

    def reduce(table):
        coefficients = 0
        for high, (pivot, tag) in ordered:
            if (table >> high) & 1:
                table ^= pivot
                coefficients ^= tag
        return table, coefficients

    return reduce


def z2_table(mask, constant):
    b2 = FULL if constant else 0
    for i, row in enumerate(X):
        if (mask >> i) & 1:
            b2 ^= row
    return (A0 & b2) ^ (A1 & B1) ^ (A2 & B0) ^ (A0 & A1 & B0 & B1)


def terms(coefficients):
    return [name for i, name in enumerate(SIGNALS) if (coefficients >> i) & 1]


def generate():
    reduce = base_eliminator()
    values = span(BASE[1:])  # Adding 1 to a factor changes its product by a base function.
    products = {0: (0, 0)}
    for i, j in combinations(range(len(values)), 2):
        products.setdefault(reduce(values[i] & values[j])[0], (i, j))

    solutions = {}
    for mask in (0, 2, 4, 6):  # Only the coefficients of a1 and a2 affect the coset.
        target, _ = reduce(z2_table(mask, 0))
        hit = next(((pair, products[coset ^ target]) for coset, pair in products.items()
                    if coset ^ target in products), None)
        if hit is None:
            raise ValueError(f"No pair found in the fixed-prefix search for mask {mask}")
        solutions[mask] = hit

    records = []
    for mask in range(32):
        for constant in (0, 1):
            (i, j), (k, m) = solutions[mask & 6]
            t3, t4 = values[i] & values[j], values[k] & values[m]
            residual, correction = reduce(z2_table(mask, constant) ^ t3 ^ t4)
            if residual:
                raise ValueError(f"Unmatched output correction for mask {mask}, c={constant}")
            records.append({
                "restriction": {
                    "linear": [v for n, v in enumerate(INPUTS) if (mask >> n) & 1],
                    "constant": constant,
                },
                "gates": [
                    {"name": "g0", "left": ["a0"], "right": ["b0"]},
                    {"name": "g1", "left": ["a0"], "right": ["b1"]},
                    {"name": "g2", "left": ["a1"], "right": ["b0"]},
                    {"name": "g3", "left": terms(i << 1), "right": terms(j << 1)},
                    {"name": "g4", "left": terms(k << 1), "right": terms(m << 1)},
                ],
                "outputs": {"z0": ["g0"], "z1": ["g1", "g2"],
                            "z2": terms(correction) + ["g3", "g4"]},
            })
    return {"format": "xor-and-restrictions-v1", "input_order": list(INPUTS),
            "encoding": "Each factor or output list is the XOR of its named signals. '1' is constant one.",
            "search": {"base_without_constants": len(values),
                       "unordered_distinct_factor_pairs": len(values) * (len(values) - 1) // 2,
                       "distinct_product_cosets": len(products),
                       "target_cosets": len(solutions)},
            "circuits": records}


if __name__ == "__main__":
    path = Path(__file__).with_name("circuits.json")
    path.write_text(json.dumps(generate(), indent=2) + "\n", encoding="utf-8")
    print(path)
