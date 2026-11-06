"""Standalone F2 Boolean algebra. Public functions are 64-bit ANF bitsets.
Bit m represents the squarefree monomial with variable subset m.
Truth tables are a temporary acceleration, never a substitute for the ANF model.
No dependency on supplied search code or third-party packages.
"""
from itertools import combinations
from pathlib import Path
import json, time
N = 6
FULL = (1 << 64) - 1
X = tuple(1 << (1 << i) for i in range(N))
CONST = 1
AFF = (CONST,) + X
PAIRS = tuple(combinations(range(N), 2))
MONS2 = tuple((1 << i) | (1 << j) for i,j in PAIRS)
DEG = tuple(sum(1 << m for m in range(64) if m.bit_count() == d) for d in range(7))
LOW2 = DEG[0] | DEG[1] | DEG[2]
HIGH2 = FULL ^ LOW2
U = 0b011011
P0 = 1 << ((1 << 0) | (1 << 3))
Z1 = (1 << ((1 << 0) | (1 << 4))) ^ (1 << ((1 << 1) | (1 << 3)))
OMEGA = 1 << U
Q2_TARGET = (1 << ((1 << 0) | (1 << 5))) ^ (1 << ((1 << 1) | (1 << 4))) ^ (1 << ((1 << 2) | (1 << 3)))
Z2 = Q2_TARGET ^ OMEGA
MASKS = tuple(sum(1 << m for m in range(64) if m & (1 << i)) for i in range(N))

def mob(f):
    for i,mask in enumerate(MASKS):
        f ^= (f << (1 << i)) & mask
    return f

def mul(f,h): return mob(mob(f) & mob(h))

def mul_slow(f,h):
    out = 0
    while f:
        b = f & -f; i = b.bit_length()-1; f ^= b
        hh = h
        while hh:
            c = hh & -hh; j=c.bit_length()-1; hh ^= c
            out ^= 1 << (i|j)
    return out

def degree(f): return max((d for d in range(7) if f & DEG[d]), default=-1)

def basis(rows):
    piv = {}
    for r in rows:
        while r:
            p = r.bit_length()-1
            if p in piv: r ^= piv[p]
            else:
                piv[p] = r
                break
    for p in sorted(piv):
        for q in piv:
            if q > p and ((piv[q] >> p) & 1): piv[q] ^= piv[p]
    return tuple(piv[p] for p in sorted(piv,reverse=True))

def reduce(f,B):
    for b in B:
        if f & (1 << (b.bit_length()-1)): f ^= b
    return f

def elements(B):
    out=[0]
    for b in B: out += [f^b for f in out]
    return out

def linear(l): return sum(X[i] for i in range(6) if (l>>i)&1)

def wedge(l,r): return mul(linear(l),linear(r)) & DEG[2]

R2_FACTORS = {}
for l in range(1,64):
    for r in range(l+1,64):
        w=wedge(l,r)
        if w: R2_FACTORS.setdefault(w,(l,r))
R2 = tuple(sorted(R2_FACTORS))
R2_SET = set(R2)

def rank(q):
    rows = [0]*6
    for i,j in PAIRS:
        if (q >> ((1<<i)|(1<<j)))&1:
            rows[i] ^= 1<<j; rows[j] ^= 1<<i
    return len(basis(rows))

def planes(n, nonlinear_from=6):
    # The three nonzero vectors are i < j < i^j. Constants are factored out.
    out=[]
    for i in range(1,1<<n):
        p=1 << (i.bit_length()-1)
        for j in range(i+1,1<<n):
            if not j&p and (nonlinear_from is None or j >= 1<<nonlinear_from):
                out.append((i,j))
    return out

PLANES={n:planes(n) for n in (7,8,9)}

def v_basis(Q): return basis(AFF + tuple(Q))

def gate_products(Q):
    # Basis ordered as variables followed by independent quadratics, excluding 1.
    B=X+tuple(Q)
    vals=elements(B)
    tts=[mob(v) for v in vals]
    for i,j in PLANES[len(B)]:
        yield vals[i],vals[j],mob(tts[i]&tts[j])

def substitute(f, images):
    ans=0
    while f:
        b=f&-f; m=b.bit_length()-1; f^=b
        t=1
        for i in range(6):
            if (m>>i)&1: t=mul(t,images[i])
        ans ^= t
    return ans

def group():
    # a_i <-> b_i after any of 16 independent shifts in <a0,b0>.
    out=[]
    for sw in (0,1):
        for sa in range(4):
            for sb in range(4):
                im=list(X)
                im[2] ^= (X[0] if sa&1 else 0) ^ (X[3] if sa&2 else 0)
                im[5] ^= (X[0] if sb&1 else 0) ^ (X[3] if sb&2 else 0)
                if sw: im=[substitute(f,X[3:]+X[:3]) for f in im]
                out.append(tuple(im))
    return out
GROUP=group()
GROUP_MONO2 = tuple(tuple(substitute(1<<m,g)&DEG[2] for m in MONS2) for g in GROUP)

def transform_quad(q,gi):
    return xor_many(img for m,img in zip(MONS2,GROUP_MONO2[gi]) if (q>>m)&1)

def xor_many(seq):
    x=0
    for y in seq: x^=y
    return x

def q2_spaces(): return sorted({basis((P0,r)) for r in R2})

def q2_orbits():
    spaces=set(q2_spaces()); out=[]
    while spaces:
        q=min(spaces)
        orbit={basis(transform_quad(r,i) for r in q) for i in range(32)}
        assert orbit <= spaces # previously removed orbits are disjoint
        out.append((q,len(orbit)))
        spaces-=orbit
    return out

def record(name, result):
    path=Path(__file__).with_name('results.json')
    allres=json.loads(path.read_text()) if path.exists() else {}
    allres[name]=result
    path.write_text(json.dumps(allres,indent=2,sort_keys=True)+'\n')
    print(json.dumps({name:result},sort_keys=True),flush=True)
