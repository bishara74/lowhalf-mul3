# Task 11: exhaustive checks, over all 164,596 spaces Q3 and all nonlinear planes {f,h} of V3 = V(Q3), of
#  Lemma P (product lemma): if deg(fh) <= 2 then (fh)_2 = pi + rho with pi in <f2,h2> and rho = 0 or
#           rank 2 with supp(rho) meeting supp(R) for a rank-2 R in <f2,h2>;
#  P1 (affine element l in the plane): every non-affine element of the plane has l in the support of its 2-form;
#  P2 (no affine element, >= 2 rank-2 forms in the plane): the rank-2 forms of the plane share a factor;
#  P3 (no affine element, <= 1 rank-2 form): all rank>=4 forms of the plane have equal support, and
#           fh lies in span{1, f, h} (as a function);
#  Rad (radical lemma): if deg(FH) <= 3 for F, H in the plane and rank(H2) >= 4, then supp(F2) is inside supp(H2).
# usage: python t11_checkP.py <out.jsonl> <start> <stride>
import sys, json, os
import numpy as np
import t11_tools as K
u = np.uint64
L = K.L
NF = 1 << 15
RANK = np.array([K.rank(w) for w in range(NF)], dtype=np.int8)
def supp_mask(w):
    m = 0
    for x in K.span_elems(K.supp(w)): m |= 1 << x
    return m
SUPP = np.array([supp_mask(w) for w in range(NF)], dtype=np.uint64)
POS = [(1 << i) | (1 << j) for (i, j) in K.PAIRS]
GE3 = L.MASK_GE3; GE4 = L.MASK_GE4

def quad_masks(anf):
    m = np.zeros(len(anf), dtype=np.int64)
    for k, p in enumerate(POS):
        m |= (((anf >> u(p)) & u(1)).astype(np.int64)) << k
    return m

def main(outp, start, stride):
    S = K.q3_spaces()
    PL = {n: K.planes(n) for n in (7, 8, 9)}
    done = set()
    if os.path.exists(outp):
        for l in open(outp):
            try: done.add(json.loads(l)['i'])
            except Exception: pass
    fo = open(outp, 'a')
    for idx in range(start, len(S), stride):
        if idx in done: continue
        b = list(S[idx]); n = 6 + len(b)
        gens = K.v_gens(b); E = L.elements(gens); I, J = PL[n]
        Kc = I ^ J
        G = E[I] & E[J]; A = L.mob(G)
        FORMS = np.zeros(1 << len(b), dtype=np.int64)
        for c in range(1 << len(b)):
            w = 0
            for k in range(len(b)):
                if (c >> k) & 1: w ^= b[k]
            FORMS[c] = w
        fI, fJ, fK = FORMS[I >> 6], FORMS[J >> 6], FORMS[Kc >> 6]
        rec = {'i': idx}
        # ---- radical lemma on planes with deg(fh) <= 3 (all ordered pairs inside the plane give the same degree bound)
        d3 = (A & GE4) == 0
        bad_rad = 0
        for (x, y) in ((fI, fJ), (fJ, fI), (fI, fK), (fK, fI), (fJ, fK), (fK, fJ)):
            sel = d3 & (RANK[y] >= 4)
            bad_rad += int((sel & ((SUPP[x] & ~SUPP[y]) != 0)).sum())
        rec['n_deg3'] = int(d3.sum()); rec['bad_rad'] = bad_rad
        # ---- deg(fh) <= 2
        d2 = np.nonzero((A & GE3) == 0)[0]
        fI2, fJ2, fK2 = fI[d2], fJ[d2], fK[d2]
        g2 = quad_masks(A[d2])
        aff = (fI2 == 0) | (fJ2 == 0) | (fK2 == 0)
        nr2 = (RANK[fI2] == 2).astype(int) + (RANK[fJ2] == 2).astype(int) + (RANK[fK2] == 2).astype(int)
        typ = np.where(aff, 0, np.where(nr2 >= 2, 1, 2))
        # Lemma P
        okP = np.zeros(len(d2), dtype=bool)
        for pi in (np.zeros_like(fI2), fI2, fJ2, fK2):
            Xf = g2 ^ pi
            ok = Xf == 0
            for R in (fI2, fJ2, fK2):
                ok |= (RANK[Xf] == 2) & (RANK[R] == 2) & ((SUPP[Xf] & SUPP[R]) > u(1))
            okP |= ok
        rec['n_deg2'] = int(len(d2)); rec['n_type'] = [int((typ == t).sum()) for t in range(3)]
        rec['bad_P'] = int((~okP).sum())
        # P1: affine element l (coordinate < 64, nonzero): l in support of every non-affine element
        cI, cJ, cK = I[d2], J[d2], Kc[d2]
        bad1 = 0
        for (ca, fa) in ((cI, fI2), (cJ, fJ2), (cK, fK2)):
            isaff = (fa == 0) & (ca > 0)
            l = (ca & 63).astype(np.uint64)
            for fo2 in (fI2, fJ2, fK2):
                nonaff = fo2 != 0
                bad1 += int((isaff & nonaff & (((SUPP[fo2] >> l) & u(1)) == 0)).sum())
        rec['bad_P1'] = bad1
        # P2: rank-2 forms share a factor
        t1 = typ == 1
        bad2 = 0
        for (x, y) in ((fI2, fJ2), (fI2, fK2), (fJ2, fK2)):
            both = t1 & (RANK[x] == 2) & (RANK[y] == 2)
            bad2 += int((both & ((SUPP[x] & SUPP[y]) <= u(1))).sum())
        rec['bad_P2'] = bad2
        # P3: equal supports of rank>=4 forms, and fh in span{1,f,h}
        t2 = typ == 2
        bad3 = 0
        for (x, y) in ((fI2, fJ2), (fI2, fK2), (fJ2, fK2)):
            both = t2 & (RANK[x] >= 4) & (RANK[y] >= 4)
            bad3 += int((both & (SUPP[x] != SUPP[y])).sum())
        Ef, Eh, Gd = E[I[d2]], E[J[d2]], G[d2]
        inspan = np.zeros(len(d2), dtype=bool)
        for a in (u(0), u(K.FULL)):
            for s1 in (0, 1):
                for s2 in (0, 1):
                    inspan |= Gd == (a ^ (Ef if s1 else u(0)) ^ (Eh if s2 else u(0)))
        rec['bad_P3_supp'] = bad3; rec['bad_P3_span'] = int((t2 & ~inspan).sum())
        fo.write(json.dumps(rec) + '\n')
        if idx % (100 * stride) == start: fo.flush()
    fo.flush()

if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
