"""Independent finite checks for the referee audit. Uses only Python's stdlib."""

from collections import Counter
from itertools import combinations, combinations_with_replacement, product
import json
from pathlib import Path

POINTS = range(64)
FULL = (1 << 64) - 1
UNITS = tuple(1 << i for i in range(6))
A0, A1, A2, B0, B1, B2 = UNITS
LOW = A0 | B0
EXT = A2 | B2
CORE = 63 ^ EXT
EDGES = tuple(combinations(UNITS, 2))


def dot(a, x):
    return (a & x).bit_count() % 2


def tt(function):
    return sum(function(x) << x for x in POINTS)


LINEAR = [tt(lambda x: dot(a, x)) for a in POINTS]
a0, a1, a2, b0, b1, b2 = (LINEAR[i] for i in UNITS)
p0 = a0 & b0
z1 = (a0 & b1) ^ (a1 & b0)
carry = p0 & a1 & b1
q2 = (a0 & b2) ^ (a1 & b1) ^ (a2 & b0)
z2 = q2 ^ carry
OFF = FULL ^ p0
AFF = [FULL, *(LINEAR[i] for i in UNITS)]
S0 = AFF + [p0, z1]
CORE_POINTS = tt(lambda x: int(x & EXT == 0))


def span(basis):
    elements = [0]
    for v in basis:
        elements += [x ^ v for x in elements]
    return elements


def wedge(l, r):
    return sum((dot(l, i) * dot(r, j) ^ dot(r, i) * dot(l, j)) << k
               for k, (i, j) in enumerate(EDGES))


def contract(form, direction):
    answer = 0
    for k, (i, j) in enumerate(EDGES):
        if (form >> k) & 1:
            answer ^= dot(direction, i) * j ^ dot(direction, j) * i
    return answer


def phi(form):
    return contract(form, A2), contract(form, B2)


def check_forms():
    planes = {wedge(l, r) for l, r in combinations(POINTS, 2)} - {0}
    P = wedge(A0, B0)
    Z = wedge(A0, B1) ^ wedge(A1, B0)
    Q = wedge(A0, B2) ^ wedge(A1, B1) ^ wedge(A2, B0)
    groups = Counter("core" if phi(v) == (0, 0)
                     else "full" if contract(v, A2) & B2 else "type v"
                     for v in planes)
    assert groups == {"core": 35, "type v": 360, "full": 256}
    assert phi(wedge(A2, B0)) == (B0, 0)  # Nonzero-cross control.
    assert phi(wedge(A2, B2)) == (B2, A2)
    assert phi(Q) not in {phi(v) for v in planes | {0}}
    for T in (Z, Z ^ P):
        assert T not in planes
        splits = [v for v in planes if v ^ T in planes]
        assert splits and all(phi(v) == (0, 0) for v in splits)
    assert wedge(A0, B1) ^ Z == wedge(A1, B0)  # A genuine splitting.
    for s, t in product((0, 1), repeat=2):
        T = Q ^ s * Z ^ t * P
        assert all(contract(T, e) for e in range(1, 64))
        assert all(T ^ v not in planes | {0} for v in planes | {0})
    assert contract(Z, A2) == 0  # A radical direction after removing q2.
    for l, r in product(POINTS, repeat=2):
        if phi(wedge(l, r)) != (0, 0):
            assert any(not (e & LOW) and (e & (A1 | B1))
                       and dot(l, e) == dot(r, e) == 0 for e in POINTS)
    assert not any((e & (A1 | B1)) and dot(A1, e) == dot(B1, e) == 0
                   for e in POINTS)  # Both factors core can block this choice.
    print("Forms: 651 wedges, both support splittings, rank-six test, killing directions.")


def check_gram():
    edges = list(combinations(range(4), 2))
    nonzero_examples = 0
    unequal_control = False
    for u, v in product(range(1, 16), repeat=2):
        if u == v:
            continue
        minor = lambda i, j: dot(u, 1 << i) * dot(v, 1 << j) ^ dot(u, 1 << j) * dot(v, 1 << i)
        for bits in range(64):
            rows = [0] * 4
            for k, (i, j) in enumerate(edges):
                if bits & (1 << k):
                    rows[i] ^= 1 << j
                    rows[j] ^= 1 << i
            if any(dot(row, u) or dot(row, v) for row in rows):
                continue
            g12, g34 = dot(rows[0], 2), dot(rows[2], 8)
            if minor(0, 1) == minor(2, 3):
                assert g12 == g34
                nonzero_examples += g12
            else:
                unequal_control |= g12 != g34
    assert nonzero_examples and unequal_control
    print("Gram: all independent row pairs and alternating matrices, with nonzero controls.")


def quotient_reducer(basis):
    rows = {}
    for vector in basis:
        for pivot in sorted(rows, reverse=True):
            if vector & (1 << pivot):
                vector ^= rows[pivot]
        if vector:
            rows[vector.bit_length() - 1] = vector
    pivots = sum(1 << i for i in rows)
    corrections = {}
    for vector in span(rows.values()):
        key = vector & pivots
        assert key not in corrections
        corrections[key] = vector

    def reduce(vector):
        return vector ^ corrections[vector & pivots]

    assert all(reduce(rows[i]) == 0 for i in rows)
    return reduce


def ordinary_sums(basis):
    reduce = quotient_reducer(basis)
    values = span(basis)
    residues = {reduce(x & y) for x, y in combinations_with_replacement(values, 2)}
    return reduce, residues


def signal(d, l, b):
    return (d * p0 ^ LINEAR[l]) & LINEAR[b]


def check_core_and_pairs():
    core_signals = {signal(1, l, b) & CORE_POINTS
                    for l, b in product(POINTS, repeat=2)
                    if b & ~LOW and phi(wedge(l, b)) == (0, 0) and not b & EXT}
    assert core_signals
    for c in core_signals:
        assert all((c & f).bit_count() % 2 == 0 for f in (FULL, a0, b0))
    bad_cubic = a1 & b0 & b1 & CORE_POINTS
    assert (bad_cubic & a0).bit_count() % 2 == 1
    # Positive placement when the radical hypothesis is dropped.
    assert (a0 & (a1 & b0 & b1)) ^ (a2 & b0) ^ z2 == ((a0 & b2) ^ (a1 & b1))
    cases = [(0, A1), (B1, A1), (A2, A1), (A2, B0 | A1), (A2, B2)]
    for l, b in cases:
        reduce, residues = ordinary_sums(S0 + [signal(1, l, b)])
        target = reduce(z2)
        assert all(target ^ residue not in residues for residue in residues)
        assert reduce(a0 & a1) != 0 and reduce(a0 & a1) in residues
    # Independent enumeration of the possible first products when P is 0 or P0.
    reduce, residues = ordinary_sums(AFF + [p0])
    assert reduce(z1) not in residues
    assert reduce(z2) not in residues
    assert reduce(a0 & a1) in residues
    print(f"Coset and ordinary pairs: {len(core_signals)} radical checks, five full product-pair spaces, degenerate first products.")


def check_cube_parity():
    core = [x for x in POINTS if not x & EXT]
    for l in POINTS:
        for w in (0, A2, B2):
            if not (dot(l, w) or l == w == 0):
                continue
            points = [u ^ (dot(l, u) * w) for u in core]
            mask = sum(1 << x for x in points)
            assert mask.bit_count() == 16 and not (mask & LINEAR[l])
            for f, h in combinations_with_replacement(S0, 2):
                assert (mask & f & h).bit_count() % 2 == 0
            assert (mask & q2).bit_count() % 2 == 0
            assert (mask & z2).bit_count() % 2 == 1
            assert (mask & carry).bit_count() % 2 == 1
    print("Cube parity: all single-unit tilts and the untilted degenerate core cube.")


def check_last_factor():
    pairs = [(0, A2), (A1, A2), (A1 | A2, A2), (A2, A1),
             (A2, B2), (A2 | B0, B2 | A1), (A1, A1 | B2)]
    coverage = Counter()
    for d, (l, b) in product((0, 1), pairs):
        c = signal(d, l, b)
        if phi(wedge(l, b)) == (0, 0) and not (d and b & EXT):
            continue
        independent = bool(wedge(l, b) and contract(wedge(l, b), A2) & B2)
        base = span(S0)
        for tau, sigma in product((0, 1), repeat=2):
            coverage[independent, tau, sigma] += 1
            for u in base:
                k = u ^ tau * c
                zero_set = k ^ FULL
                for v in base:
                    R = z2 ^ v ^ sigma * c
                    if not zero_set & R:
                        assert not zero_set & OFF
                        if independent and tau == 1:
                            raise AssertionError("Independent tau=1 has no solutions")
                        if independent and sigma == 1:
                            assert k == FULL
    assert set(coverage) == set(product((False, True), (0, 1), (0, 1)))
    R = z2 ^ a2 ^ b2
    assert not (p0 & R) and p0  # k=1+P0 is a genuine modular-only solution.
    c = signal(1, 0, A2)
    assert c and not c & R and not c & OFF  # k=1+c in dependent tau=1.
    assert ((FULL ^ a1) & z2) != z2  # Negative fixed-factor control.
    for k, r, a, b, e, f in product((0, 1), repeat=6):
        if all(not ((1 ^ kx) & rx) for kx, rx in
               [(k, r), (k ^ a, r ^ e), (k ^ b, r ^ f),
                (k ^ a ^ b ^ 1, r ^ e ^ f)]):
            assert r == (e ^ f ^ (a & f) ^ (b & e))
    print(f"Last factor: {sum(coverage.values())} full generator/branch spaces, plus the scalar square identity.")


def check_targets_and_witness():
    g1, g2 = a0 & b1, a1 & b0
    g3, g4 = a0 & b2, a2 & b0
    g5 = (g1 ^ a1) & (g2 ^ b1)
    assert z2 == (g5 ^ g1 ^ g2 ^ g3 ^ g4)
    for x in POINTS:
        a, b = x & 7, x >> 3
        z = sum(((wire >> x) & 1) << j for j, wire in enumerate((p0, z1, z2)))
        assert z == a * b % 8
    assert ((z2 >> 27) & 1) == 0 and ((carry >> 27) & 1) == 1  # 3*3 = 1 mod 8.
    verification_dir = Path(__file__).resolve().parents[2]
    path = verification_dir / "lambda2-lambda1-checks/quotient_relaxed_witness.json"
    data = json.loads(path.read_text())
    assert data["coordinate_order"] == ["1", "a0", "a1", "a2", "b0", "b1", "b2", "t0", "t1", "t2", "t3"]

    def evaluate(mask, wires):
        assert mask >> len(wires) == 0
        result = 0
        for i, wire in enumerate(wires):
            if mask & (1 << i):
                result ^= wire
        return result

    wires = AFF.copy()
    assert OFF == data["domain_tt"] and OFF.bit_count() == 48
    for gate in data["gates"]:
        gate_tt = evaluate(gate["L_coefficients"], wires) & evaluate(gate["R_coefficients"], wires)
        assert gate_tt & OFF == gate["output_tt"]
        wires.append(gate_tt)
    for name, target in (("z1", z1), ("q2", q2)):
        mask = data["outputs"][name]
        assert not (evaluate(mask, wires) ^ target) & OFF
        assert (evaluate(mask ^ 1, wires) ^ target) & OFF == OFF
    print("Targets: all 64 inputs and the six-gate circuit, plus the 48-point relaxed witness.")


if __name__ == "__main__":
    check_forms()
    check_gram()
    check_core_and_pairs()
    check_cube_parity()
    check_last_factor()
    check_targets_and_witness()
