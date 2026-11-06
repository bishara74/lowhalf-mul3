# Task 11 toolkit: exhaustive checks of the lambda = 3 lemmas (written for the checks; reuses only the
# line-B truth-table primitives of t6_B_indep.py).
# Conventions: variables x0..x5 = a0,a1,a2,b0,b1,b2. Functions = 64-bit truth tables (python int or np.uint64).
# 2-forms = 15-bit masks over PAIRS (i<j); linear forms = 6-bit masks.
import itertools, json, collections
import numpy as np
import t6_B_indep as L
u = np.uint64
FULL = L.FULL
X = L.X
A0, A1, A2, B0, B1, B2 = range(6)
PAIRS = [(i, j) for i in range(6) for j in range(i + 1, 6)]
PIDX = {p: k for k, p in enumerate(PAIRS)}
z0, z1, z2 = L.z0, L.z1, L.z2
OMEGA_TT = X[0] & X[1] & X[3] & X[4]
U_MASK = 0b011011          # a0,a1,b0,b1
def wedge_ll(l, r):
    """2-form l^r for linear forms l, r (6-bit masks)"""
    m = 0
    for k, (i, j) in enumerate(PAIRS):
        if (((l >> i) & 1) & ((r >> j) & 1)) ^ (((l >> j) & 1) & ((r >> i) & 1)): m |= 1 << k
    return m
def form_tt(w):
    t = 0
    for k, (i, j) in enumerate(PAIRS):
        if (w >> k) & 1: t ^= X[i] & X[j]
    return t
def lin_tt(l):
    t = 0
    for i in range(6):
        if (l >> i) & 1: t ^= X[i]
    return t
def anf(t): return int(L.mob(u(t)))
def quad_part(t):
    """2-form mask of the quadratic ANF part of truth table t"""
    a = anf(t); w = 0
    for k, (i, j) in enumerate(PAIRS):
        if (a >> ((1 << i) | (1 << j))) & 1: w |= 1 << k
    return w
def degree(t):
    a = anf(t); return max([bin(m).count('1') for m in range(64) if (a >> m) & 1] or [-1])
def mat(w):
    M = [0] * 6
    for k, (i, j) in enumerate(PAIRS):
        if (w >> k) & 1: M[i] |= 1 << j; M[j] |= 1 << i
    return M
def span_basis(rows):
    """reduced row echelon basis (sorted descending) of the span of the given bit vectors"""
    basis = []
    for r in rows:
        for b in basis:
            if r & (1 << (b.bit_length() - 1)): r ^= b
        if r:
            lb = 1 << (r.bit_length() - 1)
            basis = [b ^ r if b & lb else b for b in basis] + [r]
            basis.sort(reverse=True)
    return basis
def rank_rows(rows): return len(span_basis(rows))
def rank(w): return rank_rows(mat(w))
def supp(w): return span_basis(mat(w))           # row space = support, as rref basis of linear forms
def span_elems(basis):
    out = {0}
    for b in basis: out |= {x ^ b for x in out}
    return out
FOUR = list(itertools.combinations(range(6), 4))
def wedge4(w1, w2):
    """4-form w1^w2 as a 15-bit mask over 4-subsets FOUR"""
    res = 0
    for k1, (i, j) in enumerate(PAIRS):
        if not (w1 >> k1) & 1: continue
        for k2, (k, l) in enumerate(PAIRS):
            if not (w2 >> k2) & 1: continue
            s = {i, j, k, l}
            if len(s) == 4: res ^= 1 << FOUR.index(tuple(sorted(s)))
    return res
OMEGA4 = 1 << FOUR.index((0, 1, 3, 4))
def beta(w1, w2):
    """coefficient of a0a1b0b1 in w1^w2"""
    return (wedge4(w1, w2) >> FOUR.index((0, 1, 3, 4))) & 1
P0 = wedge_ll(1 << A0, 1 << B0)
Z1F = wedge_ll(1 << A0, 1 << B1) ^ wedge_ll(1 << A1, 1 << B0)
Q2F = wedge_ll(1 << A0, 1 << B2) ^ wedge_ll(1 << A1, 1 << B1) ^ wedge_ll(1 << A2, 1 << B0)
assert form_tt(P0) == z0 and form_tt(Z1F) == z1
def in_LamU(w): return all(((w >> k) & 1) == 0 or (((U_MASK >> i) & 1) and ((U_MASK >> j) & 1)) for k, (i, j) in enumerate(PAIRS))
R2 = sorted({wedge_ll(l, r) for l in range(1, 64) for r in range(1, 64)} - {0})
assert len(R2) == 651 and all(rank(w) == 2 for w in R2)

def q3_spaces():
    """all subspaces span{P0, P1, P2} with P1, P2 rank 2 (any dimension); list of rref bases (tuples)"""
    S = set()
    for i, p in enumerate(R2):
        for q in R2[i:]:
            S.add(tuple(span_basis([P0, p, q])))
    return sorted(S)
def minrank_Z1(basis):
    return min(rank(Z1F ^ q) for q in span_elems(basis))

# ---- V3 machinery (truth tables) ----
def v_gens(basis):
    return list(X) + [form_tt(w) for w in basis]
def reducer(gens):
    piv = L.multi_echelon([[int(g)] for g in [FULL] + list(gens)])
    P = [(u(b), u(r[0])) for (w, b, r) in piv]
    def red(a):
        a = np.array(a, dtype=u, copy=True)
        for b, r in P: a ^= ((a >> b) & u(1)) * r
        return a
    return red
def planes(n, nonlin_from=6):
    """2-dim subspaces {i, j, i^j} of coordinate space F2^n (indices into elements(gens)), not inside the first
    `nonlin_from` coordinates (i.e. not inside Aff/<1>)"""
    I, J = L.sub2(1 << n)
    k = (I >= (1 << nonlin_from)) | (J >= (1 << nonlin_from)) | ((I ^ J) >= (1 << nonlin_from))
    return I[k], J[k]
