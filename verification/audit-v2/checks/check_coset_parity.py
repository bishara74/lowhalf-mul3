"""Test the two Toolkit cosets and the noncore ordinary-product parity claim."""

from functools import cache
from itertools import product
from random import Random

from anf import (
    AFF, ALL, CARRY, DEG, EXTERNAL, LOW, P0, Q2, Z1, Z2,
    a0, a1, a2, b0, b1, b2, basis, cubic_representatives, mul, reduce_by, span, zeta,
)

SAMPLES = 1_000_000
SEED = 20261107
PROJECTION = EXTERNAL | CARRY


def sample_cosets():
    # This is the maximal admissible B. A cubic monomial missing a0 or b0
    # pairs with the missing variable, so the other two cubics are forbidden.
    gens = (*AFF, mul(a0, a1), P0, mul(a0, b1), mul(a1, b0), mul(a1, b1),
            mul(b0, b1), mul(P0, a1), mul(P0, b1))
    funcs = span(map(zeta, gens))
    target_a = Z2 & PROJECTION
    target_b = zeta(Z2)

    @cache
    def a_image(f):
        return basis((*(g & PROJECTION for g in gens),
                      *(zeta(f & zeta(g)) & PROJECTION for g in gens)))

    @cache
    def b_image(k):
        return basis((*tg, *(k & g for g in tg)))

    tg = tuple(map(zeta, gens))
    # Plant a violation of (a) after adding a forbidden cubic to B.
    forbidden = mul(a1, mul(b0, b1))
    f, h, F, H = b0, a2, a0, b2 ^ forbidden
    assert (mul(f, h) ^ mul(F, H)) & PROJECTION == target_a
    extended = basis((zeta(zeta(F) & zeta(g)) & PROJECTION for g in (*gens, forbidden)))
    assert not reduce_by(target_a ^ mul(f, h), extended)
    assert reduce_by(target_a ^ mul(f, h), a_image(zeta(F)))

    # Plant a positive result of (b) by using an allowed product as the target.
    k, g, F = zeta(a0), zeta(mul(a0, b1)), zeta(b2)
    planted = k & (g ^ F)
    assert planted and not reduce_by(planted ^ (k & g), b_image(k))

    def verify(f, h, F, k):
        g = f & h
        projected_g = zeta(g) & PROJECTION
        pivots = a_image(F)
        # Exact in H, C, and the two values of sigma for the chosen f,h,F.
        assert reduce_by(target_a, pivots)
        assert reduce_by(target_a ^ projected_g, pivots), [hex(zeta(v)) for v in (f, h, F)]
        # Exact in F' and the correction for the chosen f,h,k.
        assert reduce_by(target_b ^ (k & g), b_image(k)), [hex(zeta(v)) for v in (f, h, k)]

    rng = Random(SEED)
    for _ in range(SAMPLES):
        verify(*(funcs[rng.randrange(len(funcs))] for _ in range(4)))

    edge = tuple(map(zeta, (0, 1, a0, b0, a2, b2, a2 ^ b2, P0, 1 ^ P0,
                            mul(P0, a1), mul(P0, b1) ^ a2)))
    for f, h, F, k in product(edge, repeat=4):
        verify(f, h, F, k)

    minors_checked = 0
    pairs = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
    def minors(x, y):
        return [((x >> i & 1) & (y >> j & 1)) ^ ((x >> j & 1) & (y >> i & 1))
                for i, j in pairs]
    for m, n in product(range(1, 16), repeat=2):
        if m == n:
            continue
        kernel = [x for x in range(1, 16) if (m & x).bit_count() % 2 == (n & x).bit_count() % 2 == 0]
        assert len(kernel) == 3
        assert minors(*kernel[:2]) == minors(m, n)[::-1]
        minors_checked += 1

    # Boolean identities are pointwise. Exhaust all bit assignments including
    # the output correction sigma, the two feedback flags, and both factor bits.
    count = 0
    for x, y, g, s, t, sigma in product(range(2), repeat=6):
        X, Y = x ^ (s & g), y ^ (t & g)
        original = (X & Y) ^ (sigma & g)
        correction = 0
        if s == t == 1:
            y ^= x
            t = 0
            correction = X
        if t == 1:
            x, y, s, t = y, x, t, s
        assert t == 0
        if s:
            normalized = ((y ^ sigma) & (x ^ g)) ^ (sigma & x)
        else:
            normalized = (x & y) ^ (sigma & g)
        assert original == normalized ^ correction
        count += 1
    return {'seed': SEED, 'samples_per_part': SAMPLES, 'maximal_A_dimension': len(gens),
            'edge_tuples_per_part': len(edge) ** 4, 'complementary_minor_matrices': minors_checked,
            'final_product_point_assignments': count,
            'positive_controls': ['forbidden cubic gives an exact (a) witness',
                                  'relaxed target gives an exact (b) witness']}


def parity_example():
    f = (a0, P0 ^ b2, b0, b1 ^ a2)
    ordinary = mul(f[0], f[1]) ^ mul(f[2], f[3])
    assert ordinary == P0 ^ mul(b0, b1) ^ mul(a0, b2) ^ mul(b0, a2)
    assert ordinary & EXTERNAL == Q2 & EXTERNAL
    def parity(x, j):
        mask = sum(1 << i for i in range(64) if i & 36 == 0 and (i >> 1 & 1) == j)
        return (zeta(x) & mask).bit_count() % 2
    checks = {}
    for name, x, expected in (
        ('beta(P0,b1)', mul(P0, b1), [1, 1]),
        ('beta(a0,P0)', mul(a0, P0), [0, 0]),
        ('beta(b0,b1)', mul(b0, b1), [0, 0]),
        ('product_sum', ordinary, [0, 0]), ('target', Z2, [0, 1]),
    ):
        checks[name] = [parity(x, j) for j in range(2)]
        assert checks[name] == expected
    return checks


def parity_pairs():
    # Independently compare ordinary-product cosets, without imposing the
    # proposed hyperplane equalities or using the pairing argument.
    reps = cubic_representatives()
    candidates = [c for c in reps.values() if c & EXTERNAL & (ALL ^ LOW)
                  and c & EXTERNAL & DEG[3] == 0]
    # All other noncore cases are eliminated by the B-wedge-Omega observation.
    base_mask = ALL ^ (LOW | P0)
    z_pivot = 1 << (Z1.bit_length() - 1)
    planes = products = 0
    positive = False
    for c in candidates:
        cp = 1 << (c.bit_length() - 1)
        def canonical(x):
            if x & cp:
                x ^= c
            if x & z_pivot:
                x ^= Z1
            return x & base_mask

        funcs = span(zeta(g) for g in (*AFF[1:], P0, Z1, c))
        goal = canonical(Z2)
        seen = {0}
        for i in range(1, len(funcs)):
            f = funcs[i]
            for j in range(i + 1, len(funcs)):
                if i ^ j <= j:
                    continue
                planes += 1
                residue = canonical(zeta(f & funcs[j]))
                assert residue ^ goal not in seen, (hex(c), hex(residue), hex(goal))
                seen.add(residue)
        products += len(seen)
        relaxed = canonical(Q2 ^ mul(a1, b1) ^ P0 ^ mul(b0, b1))
        assert relaxed != 0
        positive |= any(r ^ relaxed in seen for r in seen)
    assert candidates and positive
    return {'noncore_first_gate_cosets_with_core_B': len(candidates), 'planes': planes,
            'distinct_product_cosets_summed_over_spaces': products,
            'positive_control': 'the worked example gives a pair for its relaxed target'}


def run():
    return {'toolkit': sample_cosets(), 'example': parity_example(), 'ordinary_pairs': parity_pairs()}
