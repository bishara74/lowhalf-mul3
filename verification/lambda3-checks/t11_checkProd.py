# Task 11: classify all nonlinear planes {f,h} in V3 (all 164,596 spaces Q3) whose product fh has degree <= 2,
# by plane type: 'aff' (plane contains an affine function), 'rk22' (no affine element, at least two rank-2
# quadratic parts), 'rk4' (no affine element, at most one rank-2 quadratic part); and whether (fh)_2 lies in Q3.
# usage: python t11_checkProd.py <out.jsonl> <start> <stride>
import sys, json, os, collections
import numpy as np
import t11_tools as K
u = np.uint64
GE3 = K.L.MASK_GE3

def main(outp, start, stride):
    S = K.q3_spaces()
    PL = {n: K.planes(n) for n in (7, 8, 9)}
    fo = open(outp, 'a')
    for idx in range(start, len(S), stride):
        b = list(S[idx]); n = 6 + len(b)
        gens = K.v_gens(b); E = K.L.elements(gens); I, J = PL[n]
        G = E[I] & E[J]
        low = (K.L.mob(G) & GE3) == 0
        sel = np.nonzero(low)[0]
        Eb = sorted(K.span_elems(b)); rk = {}
        def form_of(c):          # quadratic part of coordinate vector c (bits >= 6 select basis forms)
            w = 0
            for k in range(len(b)):
                if (c >> (6 + k)) & 1: w ^= b[k]
            return w
        cnt = collections.Counter(); inQ = set(Eb)
        for s in sel.tolist():
            i, j = int(I[s]), int(J[s]); fs = [form_of(i), form_of(j), form_of(i ^ j)]
            if 0 in fs: typ = 'aff'
            else:
                n2 = sum(1 for w in fs if K.rank(w) == 2)
                typ = 'rk22' if n2 >= 2 else 'rk4'
            g2 = K.quad_part(int(G[s]))
            cnt[(typ, g2 in inQ)] += 1
        fo.write(json.dumps({'i': idx, 'counts': {f'{a}|{c}': v for (a, c), v in cnt.items()}}) + '\n')
    fo.flush()

if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
