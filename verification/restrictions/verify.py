"""Verify all serialized circuits by direct evaluation, without search or a solver."""

from collections import Counter
from copy import deepcopy
from itertools import product
import json
from pathlib import Path

INPUTS = ("a0", "a1", "a2", "b0", "b1")
OUTPUTS = ("z0", "z1", "z2")
DEFAULT = Path(__file__).with_name("circuits.json")


def xor_terms(terms, signals):
    if not isinstance(terms, list) or any(type(t) is not str for t in terms):
        raise ValueError(f"Invalid ANF term list: {terms!r}")
    if len(set(terms)) != len(terms) or any(t not in signals for t in terms):
        raise ValueError(f"Repeated or unavailable ANF signal: {terms!r}")
    value = 0
    for term in terms:
        value ^= signals[term]
    return value


def restriction_key(restriction):
    names, constant = restriction["linear"], restriction["constant"]
    xor_terms(names, dict.fromkeys(INPUTS, 0))
    if type(constant) is not int or constant not in (0, 1):
        raise ValueError(f"Invalid restriction constant: {constant!r}")
    return sum(1 << INPUTS.index(name) for name in names), constant


def evaluate(record, bits):
    signals = dict(zip(INPUTS, bits))
    signals["1"] = 1
    gates = record["gates"]
    if not isinstance(gates, list) or len(gates) > 5:
        raise ValueError("Expected a list of at most five AND gates")
    for i, gate in enumerate(gates):
        if gate["name"] != f"g{i}":
            raise ValueError(f"Unexpected gate name: {gate['name']!r}")
        signals[gate["name"]] = xor_terms(gate["left"], signals) & xor_terms(gate["right"], signals)
    if set(record["outputs"]) != set(OUTPUTS):
        raise ValueError("Expected exactly z0, z1 and z2")
    return tuple(xor_terms(record["outputs"][name], signals) for name in OUTPUTS)


def verify_circuit(record):
    key = restriction_key(record["restriction"])
    for bits in product((0, 1), repeat=5):
        a0, a1, a2, b0, b1 = bits
        b2 = key[1] ^ xor_terms(record["restriction"]["linear"], dict(zip(INPUTS, bits)))
        number = (a0 + 2 * a1 + 4 * a2) * (b0 + 2 * b1 + 4 * b2)
        expected = tuple((number >> i) & 1 for i in range(3))
        got = evaluate(record, bits)
        if got != expected:
            raise ValueError(f"Output mismatch for restriction {key}, input {bits}: {got} != {expected}")
    return key


def check(path=DEFAULT):
    artifact = json.loads(Path(path).read_text(encoding="utf-8"))
    if artifact["format"] != "xor-and-restrictions-v1" or artifact["input_order"] != list(INPUTS):
        raise ValueError("Unexpected circuit file format or input order")
    seen, counts = set(), Counter()
    for record in artifact["circuits"]:
        key = verify_circuit(record)
        if key in seen:
            raise ValueError(f"Duplicate restriction {key}")
        seen.add(key)
        counts[len(record["gates"])] += 1
    if seen != set(product(range(32), (0, 1))):
        raise ValueError("The file does not cover all 64 affine restrictions")

    # Positive controls for detection of an incorrect output and a forward reference.
    for change, expected_error in (
        (lambda r: r["outputs"]["z0"].append("1"), "Output mismatch"),
        (lambda r: r["gates"][0]["left"].append("g4"), "unavailable ANF signal"),
    ):
        bad = deepcopy(artifact["circuits"][0])
        change(bad)
        try:
            verify_circuit(bad)
        except ValueError as exc:
            if expected_error not in str(exc):
                raise
        else:
            raise AssertionError(f"Verifier missed the positive control: {expected_error}")
    return {"status": "pass", "restrictions": len(seen), "inputs_per_restriction": 32,
            "input_rows_checked": len(seen) * 32, "output_bits_checked": len(seen) * 32 * 3,
            "gate_count_distribution": dict(sorted(counts.items())), "positive_controls": 2}


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("circuits", type=Path, nargs="?", default=DEFAULT)
    print(json.dumps(check(parser.parse_args().circuits), indent=2))
