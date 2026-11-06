# Task 11: exhaustive checks of Lemmas B3a and B3b on all 11 spaces Q3 with Z1 in Q3 and all 42,784 nonlinear g3 = fh.
#  B3a (exact):   no F, H in V3 with FH in z2 + V3 + <g3>.
#  B3a (level i): no F, H in V3 with P(FH + z2) in P(V3 + <g3>), P = (D_a2, D_b2, D_{a2+b2}, coefficient of a0a1b0b1).
#  B3b (exact):   no k, F' in V3 with k (F' + g3) in z2 + V3.
# usage: python t11_checkB3.py a <out.json>  |  python t11_checkB3.py b <out.jsonl> <start> <stride>
import sys, json, os, time
import numpy as np
import t11_tools as K
u = np.uint64
L = K.L

def b3_spaces():
    S = K.q3_spaces()
    return [list(b) for b in S if len(b) == 3 and K.Z1F in K.span_elems(list(b))]

def proj_int(t):
    """level-i projection of a truth table as one python int: D_a2 | D_b2 | D_a2+b2 | Omega bit"""
    w = L.proj(u(t), ['D', 'COmega'], ['e_a2', 'e_b2', 'e_a2+e_b2'])
    return int(w[0]) | (int(w[1]) << 64) | (int(w[2]) << 128) | (int(w[3]) << 192)

def make_reducer(vecs):
    piv = []
    for v in vecs:
        for p in piv:
            if v & (1 << (p.bit_length() - 1)): v ^= p
        if v:
            piv = [p ^ v if p & (1 << (v.bit_length() - 1)) else p for p in piv] + [v]
    def red(x):
        for p in piv:
            if x & (1 << (p.bit_length() - 1)): x ^= p
        return x
    return red

def proj_arr(t):
    w = L.proj(np.asarray(t, dtype=u), ['D', 'COmega'], ['e_a2', 'e_b2', 'e_a2+e_b2'])
    return [int(a) | (int(b) << 64) | (int(c) << 128) | (int(d) << 192) for a, b, c, d in zip(*[np.atleast_1d(x).tolist() for x in w])]

def check_a(outp, si):
    b = b3_spaces()[si]
    gens = K.v_gens(b); basis = [K.FULL] + gens
    E = L.elements(basis)                                  # all 1024 elements of V3 (with constants)
    ii, jj = np.triu_indices(len(E))
    FH = E[ii] & E[jj]
    I, J = K.planes(9); E9 = L.elements(gens); G3 = E9[I] & E9[J]
    res = {'space': si, 'basis': b}
    for mode in ('exact', 'level_i'):
        P = (lambda a: [int(x) for x in np.atleast_1d(a).tolist()]) if mode == 'exact' else proj_arr
        red = make_reducer(P(np.array(basis, dtype=u)))
        Sset = {red(x) for x in P(FH)}
        rz = red(P(np.array([K.z2], dtype=u))[0])
        bad = int(rz in Sset) + sum(1 for x in P(G3) if (rz ^ red(x)) in Sset)
        res[mode] = {'n_products': int(len(FH)), 'n_residues': len(Sset), 'n_g3': int(len(G3)), 'violations': bad}
    with open(outp, 'a') as fo: fo.write(json.dumps(res) + '\n')

def check_b(outp, start, stride, CH=2000):
    sp = b3_spaces()
    I, J = K.planes(9)
    units = [(si, a) for si in range(len(sp)) for a in range(0, len(I), CH)]
    done = set()
    if os.path.exists(outp):
        for l in open(outp):
            try: d = json.loads(l); done.add((d['space'], d['start']))
            except Exception: pass
    fo = open(outp, 'a'); cache = {}
    for (si, a) in units[start::stride]:
        if (si, a) in done: continue
        t0 = time.time()
        if si not in cache:
            b = sp[si]; gens = K.v_gens(b); basis = [K.FULL] + gens
            red = K.reducer(gens)
            kk = L.elements(basis)                        # 1024 choices of k
            # per-k echelon of span{ r(k*b) : b in basis }, vectorised over k (pivot = lowest set bit)
            piv = []
            for bb in basis:
                v = red(kk & u(bb))
                for (pv, pb) in piv:
                    v ^= np.where((v & pb) != 0, pv, u(0))
                pb = v & (~v + u(1))
                piv.append((v, pb))
            E9 = L.elements(gens)
            cache = {si: (kk, red, piv, E9, red(np.array([K.z2], dtype=u))[0])}
        kk, red, piv, E9, rz = cache[si]
        bad = 0; n = 0
        for c in range(a, min(len(I), a + CH)):
            g3 = E9[I[c]] & E9[J[c]]
            r = red(kk & g3) ^ rz
            for (pv, pb) in piv:
                r ^= np.where((r & pb) != 0, pv, u(0))
            bad += int((r == 0).sum()); n += 1
        fo.write(json.dumps({'space': si, 'start': a, 'n_g3': n, 'n_k': len(kk), 'violations': bad,
                             'seconds': round(time.time() - t0, 2)}) + '\n'); fo.flush()

if __name__ == '__main__':
    if sys.argv[1] == 'a': check_a(sys.argv[2], int(sys.argv[3]))
    else: check_b(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
