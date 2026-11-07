"""Enumerate all plane products modulo (a0*b0), including affine planes."""

from anf import (
    AFF, DEG, HIGH, LOW, OUTSIDE_I, P0, QUAD_SPACES, RANK_TWO, VARS, Z1, Z2, a0, a1, b0, b1,
    monomial_mul, mul, span, substitute, symmetry_actions, zeta,
)


def representative_spaces():
    actions = tuple(symmetry_actions())
    assert len(set(actions)) == 32
    assert all(substitute(P0, a) == P0 and substitute(Z1, a) == Z1
               and (substitute(Z2, a) ^ Z2) & ~(LOW | P0) == 0 for a in actions)
    action_set = set(actions)
    for a in actions:
        for b in actions:
            assert tuple(substitute(x, a) for x in b) in action_set
    reps = set()
    for qs in QUAD_SPACES:
        reps.add(min(tuple(sorted(substitute(q, a) & DEG[2] for q in qs)) for a in actions))
    return reps


def first_gate():
    tt = span(zeta(x) for x in (*AFF, P0))
    ignored = LOW | P0
    goals = {z & ~ignored for z in (Z1, Z2, Z1 ^ Z2)}
    relaxed = mul(a0, b1)
    seen_relaxed = False
    count = 0
    for i, f in enumerate(tt):
        for h in tt[i:]:
            residue = zeta(f & h) & ~ignored
            assert residue not in goals
            seen_relaxed |= residue == relaxed
            count += 1
    assert seen_relaxed
    return count


def run():
    quotient_rank_two = {q & OUTSIDE_I for q in RANK_TWO} | {0}
    # Positive control: ab has a genuinely new rank-two direction. A cubic
    # without both low bits survives the quotient and must be rejected.
    q = mul(a0, b1)
    assert q & OUTSIDE_I in quotient_rank_two and q not in (0, P0)
    assert mul(a1, mul(b0, b1)) & OUTSIDE_I & HIGH
    assert monomial_mul(a0 ^ a1 ^ P0, b0 ^ b1 ^ P0) == mul(a0 ^ a1 ^ P0, b0 ^ b1 ^ P0)

    representatives = representative_spaces()
    planes = quadratic = quartic = nonzero_cubic_branch = 0
    representative_planes = representative_quadratic = representative_quartic = 0
    for qs in QUAD_SPACES:
        # A plane basis change or constant change adds a member of V(Q).
        # Dependent factors are already in V(Q). Changing quadratic lifts
        # modulo the ideal adds only P0 and cannot change this test.
        forms = [l ^ q for q in qs for l in span(VARS)]
        tt = list(map(zeta, forms))
        admissible = {r ^ (q & OUTSIDE_I) for q in qs for r in quotient_rank_two}
        sub_planes = sub_quadratic = sub_quartic = 0
        for i in range(1, len(forms)):
            for j in range(i + 1, len(forms)):
                if i ^ j <= j:
                    continue
                sub_planes += 1
                prod = zeta(tt[i] & tt[j])
                sub_quartic += bool(prod & DEG[4])
                reduced = prod & OUTSIDE_I
                if reduced & HIGH:
                    continue
                sub_quadratic += 1
                nonzero_cubic_branch += bool(prod & DEG[3])
                assert reduced & DEG[2] in admissible, {
                    'Q': list(map(hex, qs)), 'f': hex(forms[i]), 'h': hex(forms[j]),
                    'quadratic_lift': hex(reduced),
                }
        planes += sub_planes
        quadratic += sub_quadratic
        quartic += sub_quartic
        if qs in representatives:
            representative_planes += sub_planes
            representative_quadratic += sub_quadratic
            representative_quartic += sub_quartic
    return {'Q': len(QUAD_SPACES), 'planes': planes, 'quadratic_quotient_products': quadratic,
            'quartic_products': quartic, 'Q_symmetry_representatives': len(representatives),
            'representative_planes': representative_planes,
            'representative_quadratic_quotient_products': representative_quadratic,
            'representative_quartic_products': representative_quartic,
            'with_nonzero_cubic_before_quotient': nonzero_cubic_branch,
            'first_gate_pairs_including_affine_and_dependent': first_gate(),
            'positive_control': 'a0*b1 gives an allowed genuinely new quadratic direction'}
