"""Exhaust D1's exterior branches and every rank-two extension in B."""

from collections import Counter
from itertools import combinations, product

from anf import (
    CARRY, EXTERNAL, OUTER_RANK_TWO, P0, Q2, QUAD_MONOMIALS, RANK_TWO,
    VARS, Z1, Z2, a0, a1, a2, b0, b1, b2, basis, contract, mul, reduce_by, span, wedge, zeta,
)

DIRECTIONS = (4, 32, 36)


def killing_directions(qs):
    return {e for e in DIRECTIONS if all(contract(q, e) == 0 for q in qs)}


def d1():
    types = {p: next(iter(killing_directions([p])), 0) for p in OUTER_RANK_TWO}
    p0w = {p: wedge(P0, p) for p in OUTER_RANK_TWO}
    pairs = Counter()
    core_wedges = Counter()
    witnesses = Counter()
    first = None
    for p, q in combinations(OUTER_RANK_TWO, 2):
        if p ^ q == P0:
            continue
        v, w = types[p], types[q]
        if v == w == 0:
            branch = 'both full'
        elif v == 0 or w == 0:
            branch = 'mixed full and type-v'
        else:
            branch = 'same type-v' if v == w else 'distinct type-v'
        pairs[branch] += 1
        pq = wedge(p, q)
        if branch == 'both full':
            y, yp = contract(p, 4) ^ b2, contract(q, 4) ^ b2
            x, xp = contract(p, 32) ^ a2, contract(q, 32) ^ a2
            dx, dy = x ^ xp, y ^ yp
            assert contract(pq, 4) == wedge(wedge(dx, b2 ^ y), dy)
            assert contract(pq, 32) == wedge(wedge(a2 ^ x, dx), dy)
        has_pair = False
        for index, form in enumerate(span([p0w[p], p0w[q], pq])[1:], 1):
            if form & EXTERNAL:
                continue
            key = f'{branch}, m01,m02,m12={index & 1},{index >> 1 & 1},{index >> 2}'
            core_wedges[key] += 1
            if form == CARRY:
                assert branch == 'same type-v' and contract(p, v) == contract(q, v) == 0
                has_pair = True
                first = first or [hex(p), hex(q), index, v]
            elif branch != 'same type-v':
                assert form == 0, (key, hex(p), hex(q), hex(form))
        if has_pair:
            witnesses[branch] += 1
    assert first is not None
    assert sum(pairs.values()) == 189384 and sum(witnesses.values()) == 2304
    return {'pairs': dict(pairs), 'external_free_wedges_by_subcase': dict(core_wedges),
            'pairs_with_Omega': dict(witnesses), 'positive_control': first}


def prop_b():
    ranks = sorted(RANK_TWO)
    spaces = {tuple(sorted(set(span([P0, p, q]))))
              for p, q in combinations(ranks, 2)}
    spaces.add((0, P0))  # also include the pair with both generators P0
    dimensions = Counter(len(qs).bit_length() - 1 for qs in spaces)
    eligible = Counter()
    no_kill = containing_z1 = 0
    for qs in spaces:
        if Z1 in qs:
            assert all(q & EXTERNAL == 0 for q in qs)
            containing_z1 += 1
            continue
        candidates = {Z1 ^ q for q in qs} & RANK_TWO
        if not candidates:
            continue
        eligible[len(qs).bit_length() - 1] += 1
        for r in candidates:
            qprime = set(qs) | {Z1 ^ q for q in qs}
            current = basis(qprime & RANK_TWO)
            assert 1 << len(current) == len(qprime)
            assert Z1 in qprime and P0 in qprime and r not in qs
            generators = [P0, *sorted(qprime & RANK_TWO - {P0})]
            independent = []
            for g in generators + list(QUAD_MONOMIALS):
                if reduce_by(g, basis(independent)):
                    independent.append(g)
                if len(independent) == 4:
                    break
            assert independent[0] == P0 and len(independent) == 4
            assert all(g in RANK_TWO for g in independent)
            assert all(reduce_by(g, basis(independent)) == 0 for g in qprime)
            kills = killing_directions(qs)
            assert killing_directions(qprime) == kills
            if not kills:
                assert len(qprime) == 16
                assert sum(g & EXTERNAL == 0 for g in qprime) == 8
                assert all(g & mul(a2, b2) for g in qprime if g & EXTERNAL)
        no_kill += not kills
    assert eligible[2] and eligible[3]
    # Actual placement with a dependent list P0, P1, P2, Z1+q.
    p1 = mul(a0, b1)
    p2 = p1 ^ P0
    assert p2 in RANK_TWO and len(basis([P0, p1, p2])) == 2
    assert mul(P0 ^ a1, b0) == Z1 ^ P0 ^ p1
    return {'dimensions_of_actual_Q3': dict(dimensions), 'eligible_for_B': dict(eligible),
            'no_kill': no_kill, 'Q3_containing_Z1': containing_z1,
            'positive_control': '(P0+a1)*b0 places z1 with dependent generators P0, a0*b1, a0*(b0+b1)'}


def rank_and_upper():
    ranks = []
    for eps, alpha in product(range(2), repeat=2):
        q = Q2 ^ eps * Z1 ^ alpha * P0
        rank = lambda x: len(basis(contract(x, 1 << i) for i in range(6)))
        assert rank(q) == 6
        ranks.extend(rank(q ^ p) for p in RANK_TWO)
    assert min(ranks) == 4
    for p in OUTER_RANK_TWO:
        assert reduce_by(CARRY, basis(wedge(p, m) for m in QUAD_MONOMIALS))
    assert not reduce_by(CARRY, basis(wedge(P0, m) for m in QUAD_MONOMIALS))
    g1, g2, g3, g4 = (mul(a0, b1), mul(a1, b0), mul(a0, b2), mul(a2, b0))
    g5 = mul(g1 ^ a1, g2 ^ b1)
    output = (P0, g1 ^ g2, g5 ^ g1 ^ g2 ^ g3 ^ g4)
    assert output == (P0, Z1, Z2)
    tt = tuple(map(zeta, output))
    for point in range(64):
        assert sum(((t >> point) & 1) << i for i, t in enumerate(tt)) == (point & 7) * (point >> 3) % 8
    return {'rank_tests_after_rank_two_addition': len(ranks), 'outside_wedge_images': len(OUTER_RANK_TWO),
            'circuit_inputs': 64, 'positive_control': 'P0 exterior image contains Omega'}


def run():
    assert len(RANK_TWO) == 651 and len(OUTER_RANK_TWO) == 616
    return {'D1': d1(), 'B': prop_b(), 'rank_and_upper': rank_and_upper()}
