"""Fresh six-variable Boolean algebra, written for this referee audit.
ANF: bit s is coefficient of product of variables indexed by bits in s.
Variable order: a0,a1,a2,b0,b1,b2. All function masks fit unsigned 64 bits.
Truth tables are temporary and are never confused with ANF at the API boundary.
"""
import json, time
from pathlib import Path
FULL=(1<<64)-1
LO=[sum(1<<s for s in range(64) if not s&(1<<i)) for i in range(6)]
X=[1<<(1<<i) for i in range(6)]
P0=1<<9; Z1=(1<<17)^(1<<10); OMEGA=1<<27
Q2=(1<<33)^(1<<18)^(1<<12); Z2=Q2^OMEGA
U_MASK=27
DEG=[sum(1<<s for s in range(64) if s.bit_count()==d) for d in range(7)]
IDEAL=sum(1<<s for s in range(64) if s&9==9)

def transform(x):
    for i,m in enumerate(LO): x^=(x&m)<<(1<<i)
    return x

def mul(a,b): return transform(transform(a)&transform(b))
def direct_mul(a,b):
    c=0
    for i in bits(a):
        for j in bits(b): c^=1<<(i|j)
    return c

def bits(n):
    while n:
        t=n&-n; yield t.bit_length()-1; n^=t

def degree(x): return max((s.bit_count() for s in bits(x)),default=-1)
def wedge(a,b):
    c=0
    for i in bits(a):
        for j in bits(b):
            if not i&j: c^=1<<(i|j)
    return c

def linear(v): return sum(1<<(1<<i) for i in bits(v))
def rank(q):
    rows=[0]*6
    for s in bits(q&DEG[2]):
        i,j=list(bits(s)); rows[i]^=1<<j; rows[j]^=1<<i
    return len(basis(rows))

def basis(vs):
    out={}
    for v in vs:
        while v:
            p=v.bit_length()-1
            if p in out: v^=out[p]
            else: out[p]=v; break
    return tuple(out[p] for p in sorted(out,reverse=True))

def reduce(v,bs):
    for b in bs:
        if v&(1<<(b.bit_length()-1)): v^=b
    return v

def canonical(vs):
    bs=list(basis(vs))
    for i in range(len(bs)-1,-1,-1):
        p=1<<(bs[i].bit_length()-1)
        for j in range(i):
            if bs[j]&p: bs[j]^=bs[i]
    return tuple(bs)

def span(bs):
    out=[0]
    for b in bs: out += [v^b for v in out]
    return out

def contains(v,bs): return reduce(v,basis(bs))==0

def contraction(q,e):
    out=0
    for s in bits(q):
        for i in bits(s&e): out^=1<<(s^(1<<i))
    return out

def killed(q,e): return not contraction(q,e)
def inside(q): return all(s&~U_MASK==0 for s in bits(q))
def rank2forms(): return sorted({wedge(linear(v),linear(w)) for v in range(1,64) for w in range(v+1,64)}-{0})
def quadratic_spaces(): return sorted({canonical([P0,p]) for p in [0]+rank2forms()})
def aff(): return [1]+X

def support(q):
    return basis([sum((1<<j) for j in range(6) if i!=j and (q>>( (1<<i)|(1<<j)))&1) for i in range(6)])

def meet(a,b): return len(basis(support(a)+support(b)))<rank(a)+rank(b)

def formula(f):
    names=['a0','a1','a2','b0','b1','b2']
    return ' + '.join(''.join(names[i] for i in bits(s)) if s else '1' for s in bits(f)) or '0'

def save(name,data,start):
    data['seconds']=round(time.time()-start,3)
    Path(__file__).with_name(name+'.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'check':name,**data}),flush=True)

if __name__=='__main__':
    import random
    start=time.time(); rng=random.Random(7102)
    for i in range(10000):
        a,b=rng.getrandbits(64),rng.getrandbits(64)
        assert transform(transform(a))==a
        assert mul(a,b)==direct_mul(a,b)
    # Positive control: ordinary integer multiplication is a planted wrong product.
    assert any(((1<<i)*(1<<j))&FULL != direct_mul(1<<i,1<<j) for i in range(1,8) for j in range(1,8))
    save('algebra',{'status':'pass','random_crosschecks':10000,'positive_control_detected':True},start)
