# Task 11: exhaustive check over all 164,596 spaces Q3 = span{P0,P1,P2} (P1, P2 rank 2) of
#  Lemma A  (some nonlinear g3 = fh, f,h in V3, has fh = z1 mod V3)  <=>  Z1 in Q3 or predicate(rank 2 + shared support)
#  Lemma A1 (every z1-placing plane {f,h} contains an affine function, i.e. f2, h2 are dependent)
#  Lemma C  (no f,h in V3 with fh = z2 or z1+z2 mod V3)
# usage: python t11_checkAC.py <out.jsonl> <start> <stride>
import sys, json, time, os
import numpy as np
import t11_tools as K
u = np.uint64

def predicate(basis):
    E = K.span_elems(basis)
    rk2 = [w for w in E if w and K.rank(w) == 2]
    for q in E:
        Z = K.Z1F ^ q
        if Z and K.rank(Z) == 2:
            sZ = K.span_elems(K.supp(Z))
            for R in rk2:
                if len(sZ & K.span_elems(K.supp(R))) > 1: return True
    return False

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
        gens = K.v_gens(b); E = K.L.elements(gens); I, J = PL[n]
        G = E[I] & E[J]; red = K.reducer(gens); R = red(G); zz = red([K.z1, K.z2, K.z1 ^ K.z2])
        pz1 = np.nonzero(R == zz[0])[0]
        aff_in_plane = ((I[pz1] >> 6) == 0) | ((J[pz1] >> 6) == 0) | (((I[pz1] ^ J[pz1]) >> 6) == 0)
        Eb = K.span_elems(b)
        rec = {'i': idx, 'dim': len(b), 'Z1in': K.Z1F in Eb, 'minrank': K.minrank_Z1(b), 'pred': predicate(b),
               'n_place_z1': int(len(pz1)), 'n_place_no_affine': int((~aff_in_plane).sum()),
               'n_z2': int((R == zz[1]).sum()), 'n_z12': int((R == zz[2]).sum())}
        fo.write(json.dumps(rec) + '\n')
        if idx % (50 * stride) == start: fo.flush()
    fo.flush()

if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
