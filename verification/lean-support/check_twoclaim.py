"""Exhaustive check of TwoClaim (Proposition `onehigh` of lambda2_proof.tex for
P outside Lambda^2(U)) and of the intermediate claims planned for its Lean proof.

Setting (inputs x0..x5 = a0 a1 a2 b0 b1 b2):
  Q = span{P0, P}, P = l ^ r a rank-two form with P not in Lambda^2(U),
  S = Q + <Z1>, A = V(S) (degree <= 2, quadratic part in S), V(Q) likewise,
  g = f h with f, h in V(Q).
TwoClaim(P):  for all such g,
  (i)  z2 not in A + <g>;
  (ii) there are no F, H in A + <g> with F H + z2 in A + <g>.

Functions are 64-bit truth tables (bit n = value at the point whose bit i is
x_i). Products are bitwise AND, sums XOR, so all spaces are F2-subspaces of
F2^64 and membership is exact Gaussian elimination.

Exact reduction of (ii). Write F = F' + s g, H = H' + t g with F', H' in A.
  (s, t) = (0, 0):  F'H' + z2 + sigma g in A.                       form (a)
  otherwise (using g g = g, and replacing k by k + sigma, which moves only an
  element of A):    k (g + F) + z2 in A with k, F in A.              form (b)
Form (a), sigma = 0 and sigma = 1, is tested against the set of all products
F H (F, H in A modulo constants, which changes F H only by an element of A),
reduced modulo A. Form (b) for a fixed k is linear: k g + z2 in A + kA. Only
k with (1 + k)(z2 + v) = 0 for some v in A can occur (R = k(g + F) satisfies
k R = R); this set K_P is computed exhaustively over k, v in A.

Intermediate claims checked for every P:
  part 1  : S has a good direction (some paper direction e in {a2, b2, a2+b2}
            with iota_e(S) inside a line <l>, l != delta_e); and (i).
  part 2  : for w in {e2, e5} with l(w) = 1 (l a form of the plane with an
            external coordinate), the cube K = span{u + l(u) w : u in e0, e1,
            e3, e4} lies in ker l; the fourth difference over K vanishes on every
            product F H, F, H in A, and equals 1 on z2. Hence form (a) never holds.
  rigidity: K_P is a subset of {1, 1 + a0 b0}.
  form (b), k = 1 + a0 b0: g + a0 b0 g + z2 not in A + a0 b0 A for every g.
Positive controls replace z2 by planted targets that are placeable.
A brute-force cross-check enumerates all F, H in A + <g> for a few (P, g).
"""

import json
import sys
import time
from itertools import combinations, product

import numpy as np

U64 = np.uint64
ALL = (1 << 64) - 1


def tt_var(i):
    return sum(1 << n for n in range(64) if (n >> i) & 1)


X = [tt_var(i) for i in range(6)]
ONE = ALL


def tt_lin(v):
    """Truth table of the linear form sum v_i x_i (v a 6-bit mask)."""
    t = 0
    for i in range(6):
        if (v >> i) & 1:
            t ^= X[i]
    return t


P0 = X[0] & X[3]
Z1 = (X[0] & X[4]) ^ (X[1] & X[3])
CARRY = X[0] & X[1] & X[3] & X[4]
Z2 = (X[0] & X[5]) ^ (X[1] & X[4]) ^ (X[2] & X[3]) ^ CARRY
AFF = [ONE] + X
EXT = (1 << 2) | (1 << 5)          # external coordinates a2, b2
UCOORD = [0, 1, 3, 4]


def rref(vecs):
    basis = {}
    for v in vecs:
        for p, b in basis.items():
            if (v >> p) & 1:
                v ^= b
        if v:
            p = v.bit_length() - 1
            for q in list(basis):
                if (basis[q] >> p) & 1:
                    basis[q] ^= v
            basis[p] = v
    return basis


def reduce_arr(arr, basis):
    arr = arr.copy()
    for p, b in basis.items():
        m = ((arr >> U64(p)) & U64(1)).astype(bool)
        arr[m] ^= U64(b)
    return arr


def reduce_int(x, basis):
    for p, b in basis.items():
        if (x >> p) & 1:
            x ^= b
    return x


def span_elems(gens):
    out = [0]
    for g in gens:
        out = out + [o ^ g for o in out]
    return np.array(out, dtype=U64)


# ---------- 2-forms and contractions (for the good-direction check) ----------

def wedge(l, r):
    """2-form as a 6x6 0/1 matrix (list of row masks): w[i] bit j = l_i r_j + l_j r_i."""
    rows = []
    for i in range(6):
        m = 0
        for j in range(6):
            if i != j and ((((l >> i) & 1) & ((r >> j) & 1)) ^ (((l >> j) & 1) & ((r >> i) & 1))):
                m |= 1 << j
        rows.append(m)
    return rows


def add_forms(a, b):
    return [x ^ y for x, y in zip(a, b)]


def iota(e, w):
    out = 0
    for i in range(6):
        if (e >> i) & 1:
            out ^= w[i]
    return out


P0F = wedge(1 << 0, 1 << 3)
Z1F = add_forms(wedge(1 << 0, 1 << 4), wedge(1 << 1, 1 << 3))
PAPER = [((1 << 2), (1 << 3)), ((1 << 5), (1 << 0)), ((1 << 2) | (1 << 5), (1 << 0) | (1 << 3))]


def good_dir(gens):
    for e, d in PAPER:
        imgs = {iota(e, w) for w in gens} - {0}
        span = {0}
        for v in imgs:
            span |= {s ^ v for s in span}
        if len(span) == 1:
            return True
        if len(span) == 2:
            (lv,) = span - {0}
            if lv != d:
                return True
    return False


def t4(func_arr, cube):
    """Fourth difference at base point 0 over the cube spanned by four 6-bit vectors."""
    acc = np.zeros(func_arr.shape, dtype=U64)
    for s in range(16):
        pt = 0
        for t in range(4):
            if (s >> t) & 1:
                pt ^= cube[t]
        acc ^= (func_arr >> U64(pt)) & U64(1)
    return acc


def planes_outside_U():
    seen, out = set(), []
    for l in range(1, 64):
        for r in range(l + 1, 64):
            key = frozenset((l, r, l ^ r))
            if key in seen:
                continue
            seen.add(key)
            if all((v & EXT) == 0 for v in key):
                continue
            out.append((l, r))
    return out


def analyse(l, r, target, collect_fail=None, brute_g=0):
    """All checks for one plane; `target` is z2 (or a planted control target)."""
    p = tt_lin(l) & tt_lin(r)
    A_gens = AFF + [P0, p, Z1]
    A = rref(A_gens)
    VQ_gens = AFF + [P0, p]
    res = {"dimA": len(A)}
    Aall = span_elems(A_gens)                     # 1024 elements
    Am = span_elems(X + [P0, p, Z1])              # A modulo constants: 512
    VQm = span_elems(X + [P0, p])                 # V(Q) modulo constants: 256
    tz = reduce_int(target, A)
    # products F H, F, H in A
    FH = (Am[:, None] & Am[None, :]).ravel()
    PI = np.unique(reduce_arr(FH, A))
    # g = f h
    G = (VQm[:, None] & VQm[None, :]).ravel()
    Gred = reduce_arr(G, A)
    gcos, gidx = np.unique(Gred, return_index=True)
    Grep = G[gidx]
    res["g_cosets"] = int(len(gcos))
    # (i)
    res["i_fail"] = int(np.sum(gcos == U64(tz)))
    # form (a)
    res["a0_fail"] = int(np.isin(np.array([tz], dtype=U64), PI)[0])
    res["a1_fail"] = int(np.sum(np.isin(gcos ^ U64(tz), PI)))
    # K_P: k in A with (1+k)(target+v) = 0 for some v in A
    Zv = U64(target) ^ Aall
    Kp = [int(k) for k in Aall if np.any((~k & Zv) == 0)]
    res["K_P"] = sorted(Kp)
    # form (b), every k in K_P
    bfail = 0
    for k in Kp:
        Ek = rref(A_gens + [k & b for b in A_gens])
        test = reduce_arr((U64(k) & Grep) ^ U64(target), Ek)
        bfail += int(np.sum(test == 0))
    res["b_fail"] = bfail
    # rigidity and the k = 1 + a0 b0 conclusion
    res["rigid"] = set(Kp) <= {ONE, ONE ^ P0}
    Ep = rref(A_gens + [P0 & b for b in A_gens])
    tb = reduce_arr(Grep ^ (U64(P0) & Grep) ^ U64(target), Ep)
    res["k1p0_fail"] = int(np.sum(tb == 0))
    # good direction for S
    gens = [P0F, wedge(l, r), Z1F]
    res["goodS"] = good_dir(gens)
    # fourth-difference cube in ker l' for a form l' of the plane with an external coordinate
    lp = next(v for v in (l, r, l ^ r) if v & EXT)
    w = (1 << 2) if (lp >> 2) & 1 else (1 << 5)
    cube = []
    for u in UCOORD:
        uu = 1 << u
        lu = bin(lp & uu).count("1") & 1
        cube.append(uu ^ (w if lu else 0))
    in_ker = all(bin(lp & c).count("1") % 2 == 0 for c in cube)
    t4_prod = t4(FH, cube)
    t4_z2 = int(t4(np.array([target], dtype=U64), cube)[0])
    res["t4_ok"] = bool(in_ker and not np.any(t4_prod) and t4_z2 == 1)
    if brute_g:
        res["brute"] = brute(A_gens, Grep[:brute_g], target)
    return res


def brute(A_gens, gs, target):
    """Direct enumeration of all F, H in A + <g>: placements of target."""
    hits = []
    for g in gs:
        g = int(g)
        W = rref(A_gens + [g])
        Wall = span_elems(A_gens + [g])
        tz = reduce_int(target, W)
        prod_red = reduce_arr((Wall[:, None] & Wall[None, :]).ravel(), W)
        hits.append(int(tz == 0) + int(np.any(prod_red == U64(tz))))
    return hits


def main():
    t0 = time.time()
    out = {"setting": "TwoClaim, all planes P outside Lambda^2(U), all g = f h, f, h in V(Q)"}
    # semantic sanity: z2 is bit 2 of (a * b) mod 8
    ok = True
    for a in range(8):
        for b in range(8):
            n = sum(((a >> i) & 1) << i for i in range(3)) | sum(((b >> i) & 1) << (3 + i) for i in range(3))
            ok &= ((Z2 >> n) & 1) == (((a * b) % 8) >> 2 & 1)
    out["z2_semantics_64_inputs"] = bool(ok)
    planes = planes_outside_U()
    out["planes_outside_U"] = len(planes)
    tot = {"g_cosets": 0, "i_fail": 0, "a0_fail": 0, "a1_fail": 0, "b_fail": 0,
           "k1p0_fail": 0, "not_rigid": 0, "not_goodS": 0, "t4_bad": 0, "dimA_not_10": 0}
    kp_hist = {}
    for idx, (l, r) in enumerate(planes):
        res = analyse(l, r, Z2)
        tot["g_cosets"] += res["g_cosets"]
        for key in ("i_fail", "a0_fail", "a1_fail", "b_fail", "k1p0_fail"):
            tot[key] += res[key]
        tot["not_rigid"] += int(not res["rigid"])
        tot["not_goodS"] += int(not res["goodS"])
        tot["t4_bad"] += int(not res["t4_ok"])
        tot["dimA_not_10"] += int(res["dimA"] != 10)
        key = "+".join(sorted({ONE: "1", ONE ^ P0: "1+a0b0"}.get(k, "other") for k in res["K_P"]))
        kp_hist[key] = kp_hist.get(key, 0) + 1
        if idx % 100 == 0:
            print(f"{idx}/{len(planes)} {time.time() - t0:.0f}s", flush=True)
    out["totals"] = tot
    out["K_P_histogram"] = kp_hist
    # brute-force cross-check on a few planes and cosets
    cross = []
    for (l, r) in planes[:: max(1, len(planes) // 4)][:4]:
        res = analyse(l, r, Z2, brute_g=3)
        cross.append({"plane": [l, r], "brute_hits": res["brute"]})
    out["brute_cross_check"] = cross
    # positive brute-force control: a planted form-(b) target must be found by direct enumeration
    rngb = np.random.default_rng(7)
    bpos = []
    for (l, r) in planes[:3]:
        p = tt_lin(l) & tt_lin(r)
        Aall = span_elems(AFF + [P0, p, Z1])
        VQ = span_elems(AFF + [P0, p])
        k0, F0, a0 = (int(Aall[i]) for i in rngb.integers(0, len(Aall), 3))
        g0 = int(VQ[rngb.integers(0, len(VQ))]) & int(VQ[rngb.integers(0, len(VQ))])
        T = (k0 & (g0 ^ F0)) ^ a0
        bpos.append(brute(AFF + [P0, p, Z1], np.array([g0], dtype=U64), T)[0])
    out["brute_positive_control_hits"] = bpos
    # positive controls: planted placeable targets
    rng = np.random.default_rng(20261108)
    controls = []
    for (l, r) in planes[:: max(1, len(planes) // 6)][:6]:
        p = tt_lin(l) & tt_lin(r)
        Aall = span_elems(AFF + [P0, p, Z1])
        VQ = span_elems(AFF + [P0, p])
        F0, H0, k0, a0 = (int(Aall[i]) for i in rng.integers(0, len(Aall), 4))
        f0, h0 = (int(VQ[i]) for i in rng.integers(0, len(VQ), 2))
        g0 = f0 & h0
        planted = {
            "T=g+a (i)": g0 ^ a0,
            "T=FH+a (a, sigma 0)": (F0 & H0) ^ a0,
            "T=FH+g+a (a, sigma 1)": (F0 & H0) ^ g0 ^ a0,
            "T=k(g+F)+a (b)": (k0 & (g0 ^ F0)) ^ a0,
        }
        row = {"plane": [l, r]}
        for name, T in planted.items():
            res = analyse(l, r, T)
            row[name] = {"i": res["i_fail"], "a0": res["a0_fail"], "a1": res["a1_fail"],
                         "b": res["b_fail"], "rigid": res["rigid"], "K_P_size": len(res["K_P"])}
        controls.append(row)
    out["positive_controls"] = controls
    out["seconds"] = round(time.time() - t0, 1)
    t = tot
    out["PASS"] = bool(ok and all(h >= 1 for h in bpos) and t["i_fail"] == 0 and t["a0_fail"] == 0 and t["a1_fail"] == 0
                       and t["b_fail"] == 0 and t["k1p0_fail"] == 0 and t["not_rigid"] == 0
                       and t["not_goodS"] == 0 and t["t4_bad"] == 0 and t["dimA_not_10"] == 0)
    json.dump(out, open(sys.argv[1] if len(sys.argv) > 1 else "check_twoclaim_results.json", "w"),
              indent=1)
    print(json.dumps({k: out[k] for k in ("totals", "K_P_histogram", "PASS", "seconds")}))


if __name__ == "__main__":
    main()
