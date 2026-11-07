"""Exact existential R tests, plus both priority coordinate calculations."""

from itertools import product

from anf import (
    AFF, ALL, CARRY, EXTERNAL, LOW, OUTER_RANK_TWO, P0, Q2, Z1, Z2,
    a0, a1, a2, b0, b1, b2, basis, cubic_representatives, mul, reduce_by, span, zeta,
)


def supports_target(k, generators, target):
    """True iff (1+k)(target+v)=0 for at least one v in the span."""
    outside_k = ALL ^ k
    restricted_target = outside_k & target
    if not restricted_target:
        return True
    return not reduce_by(restricted_target, basis(g & outside_k for g in generators))


def sweep(gens, target, allowed, counts, split):
    tg = tuple(map(zeta, gens))
    tt = zeta(target)
    for i, k in enumerate(span(tg)):
        branch = split(i)
        counts[branch][0] += 1
        if supports_target(k, tg, tt):
            counts[branch][1] += 1
            if not allowed(k):
                r = next(tt ^ v for v in span(tg) if k & (tt ^ v) == tt ^ v)
                raise AssertionError({'k': hex(zeta(k)), 'R': hex(zeta(r)), 'branch': branch})


def coordinate_checks():
    core_linears = span((a0, a1, b0, b1))
    count = 0
    for x, y, xi, eta in product(core_linears, core_linears, range(2), range(2)):
        p, q = a2 ^ x ^ xi, b2 ^ y ^ eta
        corrected = (mul(b0, p) ^ mul(a0, q) ^ mul(a1, b1)
                     ^ mul(b0, x ^ xi) ^ mul(a0, y ^ eta))
        assert corrected == Q2
        # The leading form of pq is unchanged by either constant shift.
        assert (mul(p, q) ^ mul(a2 ^ x, b2 ^ y)) & (ALL ^ LOW) == 0
        count += 1

    table_rows = 0
    for row, c, s, aa, bb in product(range(3), range(2), range(2), range(2), range(2)):
        low0, low1 = ((c, s), (s, c), (s, s ^ c))[row]
        p0_expected = ((c & s), (c & s), ((1 ^ c) & s))[row]
        z1_expected = ((c & bb) ^ (s & aa), (s & bb) ^ (c & aa),
                       (s & (aa ^ bb)) ^ (c & aa))[row]
        point = low0 | aa << 1 | low1 << 3 | bb << 4
        assert (zeta(P0) >> point) & 1 == p0_expected
        assert (zeta(Z1) >> point) & 1 == z1_expected
        carry_expected = s & aa & bb if (row, c) in {(0, 1), (1, 1), (2, 0)} else 0
        assert (zeta(CARRY) >> point) & 1 == carry_expected
        table_rows += 1
    return count, table_rows


def run():
    k = zeta(a2)
    target = zeta(mul(a2, b0))
    tg = tuple(map(zeta, (*AFF, P0, Z1)))
    assert supports_target(k, tg, target)
    assert not supports_target(k, tg, zeta(mul(a1, b1)))
    planted_c = mul(P0, a2)
    planted_k = 1 ^ planted_c
    planted_r = Z2 ^ b2 ^ planted_c
    assert mul(planted_k, planted_r) == planted_r
    assert supports_target(zeta(planted_k), (*tg, zeta(planted_c)), zeta(Z2))

    p0t = zeta(P0)
    allowed = {ALL, ALL ^ p0t}
    counts = {key: [0, 0] for key in ('full d=0', 'full d=1', 'type-v d=0', 'type-v d=1')}
    for p in OUTER_RANK_TWO:
        kind = 'full' if p & mul(a2, b2) else 'type-v'
        sweep((*AFF, P0, Z1, p), Z2, allowed.__contains__, counts,
              lambda i: f'{kind} d={i >> 9}')

    representatives = cubic_representatives()
    noncore = [c for c in representatives.values() if c & EXTERNAL & (ALL ^ LOW)]
    nc = {'tau=0': [0, 0], 'tau=1': [0, 0]}
    for c in noncore:
        sweep((*AFF, P0, Z1, c), Z2, lambda k: (ALL ^ k) & (ALL ^ p0t) == 0,
              nc, lambda i: f'tau={i >> 9}')

    full_shifts, type_table = coordinate_checks()
    # Counterexample to the literal claim that the value on (1,1) is free.
    point = 1 | 4 | 8
    bad_k = 1 ^ P0
    assert (zeta(Z2) >> point) & 1 == 1
    assert (zeta(bad_k) >> point) & 1 == 0
    return {
        'count_format': ['k tested against the whole R coset by elimination', 'k with a witness R'],
        'last_factor': counts, 'noncore_multiplier': nc,
        'rank_two_P_outside_U': len(OUTER_RANK_TWO),
        'noncore_cubic_cosets': len(noncore), 'all_cubic_cosets': len(representatives),
        'full_coordinate_shifts': full_shifts, 'type_v_table_and_carry_assignments': type_table,
        'fiber_freedom_counterexample': {'k_anf': hex(bad_k), 'R_anf': hex(Z2),
                                         'point_a0_a1_a2_b0_b1_b2': [1, 0, 1, 1, 0, 0]},
        'positive_controls': ['relaxed target a2*b0 has a witness for k=a2',
                              'tau=1 with c=P0*a2, k=1+c, R=z2+b2+c'],
    }
