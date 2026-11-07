"""Independent Boolean algebra on six variables. Bit m is monomial m."""

from itertools import combinations

ALL = (1 << 64) - 1
DEG = tuple(sum(1 << m for m in range(64) if m.bit_count() == d) for d in range(7))
LOW = DEG[0] | DEG[1]
HIGH = ALL ^ (LOW | DEG[2])
VARS = tuple(1 << (1 << i) for i in range(6))
a0, a1, a2, b0, b1, b2 = VARS
EXTERNAL = sum(1 << m for m in range(64) if m & 36)
OUTSIDE_I = sum(1 << m for m in range(64) if m & 9 != 9)
CORE = ALL ^ EXTERNAL


def zeta(x):
    """Involutory Möbius transform between ANF and truth-table masks."""
    x ^= (x & 0x5555555555555555) << 1
    x ^= (x & 0x3333333333333333) << 2
    x ^= (x & 0x0F0F0F0F0F0F0F0F) << 4
    x ^= (x & 0x00FF00FF00FF00FF) << 8
    x ^= (x & 0x0000FFFF0000FFFF) << 16
    return x ^ ((x & 0x00000000FFFFFFFF) << 32)


def mul(x, y):
    return zeta(zeta(x) & zeta(y))


def terms(x):
    while x:
        bit = x & -x
        yield bit.bit_length() - 1
        x ^= bit


def monomial_mul(x, y):
    out = 0
    for i in terms(x):
        for j in terms(y):
            out ^= 1 << (i | j)
    return out


def wedge(x, y):
    out = 0
    ys = tuple(terms(y))
    for i in terms(x):
        for j in ys:
            if i & j == 0:
                out ^= 1 << (i | j)
    return out


def contract(x, direction):
    out = 0
    for term in terms(x):
        for index in range(6):
            bit = 1 << index
            if term & direction & bit:
                out ^= 1 << (term ^ bit)
    return out


def span(generators):
    out = [0]
    for g in generators:
        out += [x ^ g for x in out]
    return out


def reduce_by(x, pivots):
    while x:
        p = pivots.get(x.bit_length())
        if p is None:
            return x
        x ^= p
    return 0


def basis(generators):
    pivots = {}
    for g in generators:
        x = reduce_by(g, pivots)
        if x:
            pivots[x.bit_length()] = x
    return pivots


P0 = mul(a0, b0)
Z1 = mul(a0, b1) ^ mul(a1, b0)
Q2 = mul(a0, b2) ^ mul(a1, b1) ^ mul(a2, b0)
CARRY = mul(P0, mul(a1, b1))
Z2 = Q2 ^ CARRY
AFF = (1, *VARS)
LINEARS = span(VARS)
RANK_TWO = frozenset(wedge(x, y) for x, y in combinations(LINEARS[1:], 2))
OUTER_RANK_TWO = tuple(sorted(x for x in RANK_TWO if x & EXTERNAL))
QUAD_MONOMIALS = tuple(1 << m for m in terms(DEG[2]))
QUAD_SPACES = sorted({tuple(sorted({0, P0, p, p ^ P0})) for p in RANK_TWO})


def cubic_representatives():
    """One actual normalized gate for each cubic output coset modulo V1."""
    reps = {}
    for b in LINEARS:
        if not wedge(P0, b):
            continue
        for a in LINEARS:
            c = mul(P0 ^ a, b)
            reps.setdefault(c & (ALL ^ (LOW | P0)), c)
    return reps


def symmetry_actions():
    """Precompute ANF images of the 64 monomials under the 32 substitutions."""
    for swap in (False, True):
        left, right = (VARS[3:], VARS[:3]) if swap else (VARS[:3], VARS[3:])
        for s in span([left[0], right[0]]):
            for t in span([left[0], right[0]]):
                coords = (*left[:2], left[2] ^ s, *right[:2], right[2] ^ t)
                images = [1]
                for x in coords:
                    images += [mul(m, x) for m in images]
                yield tuple(images)


def substitute(x, images):
    out = 0
    for m in terms(x):
        out ^= images[m]
    return out
