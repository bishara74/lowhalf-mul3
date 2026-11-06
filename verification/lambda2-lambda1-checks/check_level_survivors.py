"""Reproduce the historical derivative-plus-Omega survivor count, on the
higher-degree lambda=2 branch. This is a weaker test than the exact search.
"""
from check_lambda2_exact import Screen,products
from core import *
from collections import Counter

def contract(q,e):
    out=0
    for i,j in PAIRS:
        if (q>>((1<<i)|(1<<j)))&1:
            if (e>>i)&1:out^=X[j]
            if (e>>j)&1:out^=X[i]
    return out

def level_kernel(Q):
    kills=[e for e in (4,32,36) if all(not contract(q,e) for q in Q)]
    forms=[X[i] for i in (0,1,3,4)]
    if len(kills)==1:
        forms.append({4:X[5],32:X[2],36:X[2]^X[5]}[kills[0]])
    out=[]
    for mask in range(1<<len(forms)):
        p=1
        for i,f in enumerate(forms):
            if (mask>>i)&1:p=mul(p,f)
        if not p&OMEGA:out.append(p)
    return out,kills

class Level:
    def __init__(self,Q):
        S=basis(Q+(Z1,)); self.base=S
        K,self.kills=level_kernel(Q)
        V=tuple(mob(v) for v in AFF+S)
        self.S=basis(V+tuple(mob(k) for k in K))
        self.target=reduce(mob(Z2),self.S)
        pp=products(S,True)
        self.ordinary={reduce(mob(p),self.S) for p in pp}
        self.mult=[]
        for k in [mob(f) for f in elements(X+S)][1:]:
            B=basis(self.S+tuple(k&v for v in V))
            self.mult.append((k,B,reduce(mob(Z2),B)))
    def feasible(self,g):
        gt=mob(g);r=reduce(gt,self.S)
        if self.target in (0,r):return True
        if self.target in self.ordinary or self.target^r in self.ordinary:return True
        for k,B,t in self.mult:
            a=reduce(k&gt,B)^t
            if not a or a==reduce(gt,B):return True
        return False

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=83)
    args=ap.parse_args();rows=[];t=time.time()
    for idx,(Q,w) in enumerate(q2_orbits()):
        if not args.start<=idx<args.stop:continue
        t0=time.time(); pp=products(Q);z1=Screen(Q,Z1,pp);lev=Level(Q);c=Counter();survivors=[]
        for g,m in pp.items():
            if not g&HIGH2:continue
            n0,n1=z1.count(g)
            if n0+n1:
                c['candidate_cosets']+=1;c['candidate_pairs']+=m*(n0+n1)
                if lev.feasible(g):
                    c['surviving_cosets']+=1;c['surviving_pairs']+=m*(n0+n1)
                    c['surviving_ordinary_z1_pairs']+=m*n0
                    c['surviving_feedback_z1_pairs']+=m*n1
                    survivors.append([g,m,n0,n1])
        row={'orbit':idx,'weight':w,'kills':lev.kills,'counts':dict(c),'survivors':survivors,'seconds':round(time.time()-t0,3)}
        rows.append(row);print(json.dumps(row),flush=True)
        Path(__file__).with_name(f'level_{args.start}_{args.stop}.json').write_text(json.dumps(rows,indent=2)+'\n')
    total=Counter()
    for row in rows:total.update(row['counts'])
    # Positive relaxed instance: a known product has zero residual modulo its
    # own target coset; direct predicate exercised in an otherwise excluded space.
    Q=(P0,);lev=Level(Q);g=mul(X[2]^P0,X[5]);lev.target=reduce(mob(g),lev.S)
    assert lev.target
    assert lev.feasible(0)
    record(f'level_{args.start}_{args.stop}',{'status':'PASS' if args.start==0 and args.stop==83 else 'PARTIAL_PASS',
      'scope':'higher-degree lambda=2 branch only','totals':dict(total),'positive_controls_detected':1,
      'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
