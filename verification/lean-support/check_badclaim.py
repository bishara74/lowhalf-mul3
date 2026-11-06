"""Full classical check of the Lean statement `BadClaim` (LowHalfMul3/LambdaThree.lean).

Statement checked
-----------------
For every Q3 = span{P0, l1^r1, l2^r2} (P0 = a0^b0, l_i, r_i in F2^6, so every
form of rank <= 2 is allowed, including 0 and repetitions) such that
`GoodDir Q3` FAILS, and for every target T in {z1, z2, z2 + z1}:

    there are no f, h in V(Q3) with f*h + T in V(Q3)          (NoPlace Q3 T)

where V(Q) = {p : deg p <= 2, pi2(p) in Q} = span{1, x_i, quad(omega) : omega in Q}.

Definitions follow the Lean sources exactly:
* inputs x0..x5 = a0 a1 a2 b0 b1 b2 (bit i of the truth-table index);
* wedge l r (i,j) = l_i r_j + l_j r_i;
* iota e omega (j) = sum_i e_i omega(i,j);
* GoodDir Q :<=> exists (e, d) in {(a2, b0), (b2, a0), (a2+b2, a0+b0)} and a
  vector ell != d with iota_e(omega) in {0, ell} for all omega in Q.
  Equivalently: iota_e(Q) = 0, or iota_e(Q) = {0, ell} with ell != d.

Method (exact, no sampling)
---------------------------
Functions are 64-bit truth tables; products are bitwise AND. For fixed f the
map h -> f*h is linear, so  exists h in V: f*h in T + V  <=>  T in f*V + V.
Moreover (f+1)*h = f*h + h with h in V, so f may be taken modulo constants:
2^9 - 1 = 511 nonzero representatives when dim Q3 = 3 (f = 0 gives f*V = 0).
Membership is decided by Gaussian elimination over GF(2).

Controls
--------
* positive control: T = a0*b1 (a product of two affine functions) must be
  placeable in EVERY space (f = a0, h = b1);
* on a deterministic sample of spaces WITH a good direction the same checker is
  run for z1, z2, z2+z1: z1 placements are expected to occur (Lemma A), while
  z2 and z2+z1 placements are excluded by Lemma C for all dim-3 spaces.

Usage:  python check_badclaim.py [--shards N]   (writes check_badclaim_results.json)

The work is split over N independent worker processes (default 7), each
writing a shard file; no shared state, so the result does not depend on N.
"""

import itertools
import json
import subprocess
import os
import random
import sys
import time

N = 64
PAIRS = list(itertools.combinations(range(6), 2))
PIDX = {p: k for k, p in enumerate(PAIRS)}


def var(i):
    return sum(1 << x for x in range(N) if (x >> i) & 1)


X = [var(i) for i in range(6)]
ONE = (1 << N) - 1
a0, a1, a2, b0, b1, b2 = X
Z0 = a0 & b0
Z1 = (a0 & b1) ^ (a1 & b0)
Z2 = (a0 & b2) ^ (a1 & b1) ^ (a2 & b0) ^ (a0 & a1 & b0 & b1)
CONTROL = a0 & b1


def ent(w, i, j):
    if i == j:
        return 0
    if i > j:
        i, j = j, i
    return (w >> PIDX[(i, j)]) & 1


def wedge(l, r):
    w = 0
    for k, (i, j) in enumerate(PAIRS):
        if (((l >> i) & 1) & ((r >> j) & 1)) ^ (((l >> j) & 1) & ((r >> i) & 1)):
            w |= 1 << k
    return w


def iota(e, w):
    v = 0
    for j in range(6):
        s = 0
        for i in range(6):
            if (e >> i) & 1:
                s ^= ent(w, i, j)
        if s:
            v |= 1 << j
    return v


def quad(w):
    """A quadratic function with quadratic part w: sum_{i<j} w_ij x_i x_j."""
    f = 0
    for k, (i, j) in enumerate(PAIRS):
        if (w >> k) & 1:
            f ^= X[i] & X[j]
    return f


P0 = wedge(1 << 0, 1 << 3)
Z1FORM = wedge(1 << 0, 1 << 4) ^ wedge(1 << 1, 1 << 3)
# PaperPair: (a2, b0), (b2, a0), (a2+b2, a0+b0) as 6-bit vectors
PAPER = [(1 << 2, 1 << 3), (1 << 5, 1 << 0), ((1 << 2) | (1 << 5), (1 << 0) | (1 << 3))]


def span(vecs):
    out = {0}
    for v in vecs:
        out |= {o ^ v for o in out}
    return frozenset(out)


def basis_of(vecs):
    piv = {}
    for v in vecs:
        for p in sorted(piv, reverse=True):
            if (v >> p) & 1:
                v ^= piv[p]
        if v:
            piv[v.bit_length() - 1] = v
    return list(piv.values())


def good_dir(Q):
    for e, d in PAPER:
        img = {iota(e, w) for w in Q}
        if img == {0}:
            return True
        if len(img) == 2 and (img - {0}) != {d}:
            return True
    return False


class Reducer:
    def __init__(self, vecs):
        self.piv = {}
        for v in vecs:
            self.add(v)

    def reduce(self, v):
        for p in sorted(self.piv, reverse=True):
            if (v >> p) & 1:
                v ^= self.piv[p]
        return v

    def add(self, v):
        v = self.reduce(v)
        if v:
            self.piv[v.bit_length() - 1] = v
        return v != 0


def placements(qbasis, targets):
    """For each target T, does some f, h in V(Q) give f*h in T + V(Q)?"""
    Vb = [ONE] + X + [quad(w) for w in qbasis]
    Vred = Reducer(Vb)
    tred = [Vred.reduce(t) for t in targets]
    found = [False] * len(targets)
    nonconst = X + [quad(w) for w in qbasis]
    for mask in range(1, 1 << len(nonconst)):
        f = 0
        for k, g in enumerate(nonconst):
            if (mask >> k) & 1:
                f ^= g
        R = Reducer([])
        R.piv = dict(Vred.piv)
        for h in Vb:
            R.add(f & h)
        for t, tr in enumerate(tred):
            if not found[t] and R.reduce(tr) == 0:
                found[t] = True
        if all(found):
            break
    return found


def work(qbasis):
    return placements(qbasis, [Z1, Z2, Z2 ^ Z1, CONTROL])


def enumerate_spaces():
    wedges = sorted({wedge(l, r) for l in range(64) for r in range(64)})
    assert len(wedges) == 652, len(wedges)  # 0 and the 651 rank-2 forms
    spans = set()
    for w1 in wedges:
        for w2 in wedges:
            spans.add(span([P0, w1, w2]))
    spans = sorted(spans, key=lambda S: sorted(S))
    bad = [S for S in spans if not good_dir(S)]
    good = [S for S in spans if good_dir(S) and len(S) == 8]
    rng = random.Random(20261106)
    good_sample = rng.sample(good, 2000)
    return wedges, spans, bad, good_sample


def run_shard(k, n, path):
    _, _, bad, good_sample = enumerate_spaces()
    res = {"bad": {}, "good": {}}
    for i in range(k, len(bad), n):
        res["bad"][i] = work(basis_of(sorted(bad[i])))
    for i in range(k, len(good_sample), n):
        res["good"][i] = work(basis_of(sorted(good_sample[i])))
    with open(path, "w") as fh:
        json.dump(res, fh)


def main(nshards):
    t0 = time.time()
    here = os.path.dirname(os.path.abspath(__file__))
    wedges, spans, bad, good_sample = enumerate_spaces()
    dims = {}
    for S in spans:
        d = len(S).bit_length() - 1
        dims[d] = dims.get(d, 0) + 1
    spans12 = {span([w1, w2]) for w1 in wedges for w2 in wedges}
    bad_dims = {}
    for S in bad:
        d = len(S).bit_length() - 1
        bad_dims[d] = bad_dims.get(d, 0) + 1
    contains_Z1 = sum(1 for S in bad if Z1FORM in S)
    print(f"spans {len(spans)} dims {dims}  bad {len(bad)} bad_dims {bad_dims}  "
          f"bad containing Z1 {contains_Z1}  ({time.time()-t0:.1f}s)", flush=True)

    paths = [os.path.join(here, f"_shard_{k}.json") for k in range(nshards)]
    procs = [subprocess.Popen([sys.executable, os.path.abspath(__file__), "--worker",
                               str(k), str(nshards), paths[k]],
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
             for k in range(nshards)]
    codes = [p.wait() for p in procs]
    assert all(c == 0 for c in codes), codes
    res_bad, res_good = {}, {}
    for pth in paths:
        with open(pth) as fh:
            r = json.load(fh)
        res_bad.update({int(i): v for i, v in r["bad"].items()})
        res_good.update({int(i): v for i, v in r["good"].items()})
        os.remove(pth)
    assert sorted(res_bad) == list(range(len(bad)))
    assert sorted(res_good) == list(range(len(good_sample)))
    print(f"placement checks done ({time.time()-t0:.1f}s)", flush=True)

    names = ["z1", "z2", "z2+z1", "control a0*b1"]
    viol = {n: sum(res_bad[i][k] for i in res_bad) for k, n in enumerate(names)}
    gctl = {n: sum(res_good[i][k] for i in res_good) for k, n in enumerate(names)}
    examples = [sorted(bad[i]) for i in sorted(res_bad) if any(res_bad[i][:3])][:5]
    out = {
        "statement": "BadClaim: no f,h in V(Q3) with f*h + T in V(Q3), T in {z1, z2, z2+z1}, "
                     "for every Q3 = span{P0, w1, w2} (w_i of rank <= 2) without GoodDir",
        "wedges_rank_le_2": len(wedges),
        "distinct_spans_P0_w1_w2": len(spans),
        "spans_by_dimension": {str(k): v for k, v in sorted(dims.items())},
        "distinct_spans_w1_w2_without_P0": len(spans12),
        "spans_without_GoodDir": len(bad),
        "spans_without_GoodDir_by_dimension": {str(k): v for k, v in sorted(bad_dims.items())},
        "spans_without_GoodDir_containing_Z1": contains_Z1,
        "f_representatives_per_dim3_space": 511,
        "bad_spaces_with_placement": viol,
        "bad_spaces_examples_with_placement": examples,
        "control_good_sample_size": len(good_sample),
        "control_good_spaces_with_placement": gctl,
        "shards": nshards,
        "seconds": round(time.time() - t0, 1),
        "python": sys.version.split()[0],
    }
    with open(os.path.join(here, "check_badclaim_results.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps(out, indent=2))
    ok = (viol["z1"] == 0 and viol["z2"] == 0 and viol["z2+z1"] == 0
          and viol["control a0*b1"] == len(bad) and gctl["control a0*b1"] == len(good_sample)
          and gctl["z1"] > 0)
    print("RESULT:", "PASS" if ok else "FAIL")


if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "--worker":
        run_shard(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    else:
        n = int(sys.argv[2]) if len(sys.argv) >= 3 and sys.argv[1] == "--shards" else 7
        main(n)
