"""Exploratory stronger relaxation for lambda=1. Restrict to P0=0 and ask
whether FOUR arbitrary AND gates compute (z1,q2). If impossible, it would
exclude the original cubic branch because its first remaining gate is affine
input modulo (P0). All later gates are relaxed to arbitrary products.
Not a claimed lemma unless the complete run and a written proof exist.
"""
from core import *
from collections import Counter
DOMAIN=FULL^mob(P0)
AFFTT=tuple(mob(f)&DOMAIN for f in AFF)

def space(rows):
    C=[DOMAIN]
    for row in basis(rows):
        r=reduce(row,basis(C))
        if r:C.append(r)
    return tuple(C)

def products_tt(B):
    BB=basis(B);vals=elements(B[1:]);out={}
    for i,j in planes(len(B)-1,None):
        r=reduce(vals[i]&vals[j],BB)
        out[r]=out.get(r,0)+1
    out.setdefault(0,1)
    return out

class QS:
    def __init__(self,B,T,pp=None):
        self.B=space(B);self.BB=basis(B);self.T=reduce(T,self.BB)
        self.pp=products_tt(self.B) if pp is None else pp
        self.K=[]
        for k in elements(self.B):
            if k in (0,DOMAIN):continue
            c=DOMAIN^k
            if reduce(c&T,basis(c&b for b in self.B)):continue
            S=basis(self.B+tuple(k&b for b in self.B))
            self.K.append((k,S,reduce(T,S)))
    def can(self,g):
        g=reduce(g,self.BB)
        if self.T in (0,g):return True
        if self.T in self.pp or self.T^g in self.pp:return True
        for k,S,t in self.K:
            a=reduce(k&g,S)^t
            if not a or a==reduce(g,S):return True
        return False

def main():
    t=time.time();zt=mob(Z1)&DOMAIN;qt=mob(Q2_TARGET)&DOMAIN
    count=Counter();rows=[];counterexamples=[]
    for idx,(Q,w) in enumerate(q2_orbits()):
        ttrows=AFFTT+tuple(mob(q)&DOMAIN for q in Q)
        B=space(ttrows);pp=products_tt(B)
        screens=[]
        for T,O in [(zt,qt),(qt,zt),(qt^zt,zt)]:
            S=space(B+(T,));screens.append((T,QS(B,T,pp),QS(S,O),S))
        for g,m in pp.items():
            for T,early,last,S in screens:
                if reduce(T,basis(B))==g:
                    possible=any(last.can(h) for h in products_tt(S))
                else:
                    possible=early.can(g) and last.can(g)
                if possible:
                    counterexamples.append({'orbit':idx,'Q':list(Q),'g2_tt':g,'first_target_tt':T})
                    break
            count['g2_cosets']+=1
            if counterexamples:break
        row={'orbit':idx,'Q':list(Q),'g2_cosets':len(pp)};rows.append(row)
        print(json.dumps(row),flush=True)
        if counterexamples:break
    # Known quotient product: q2 is a sum of three affine-input products.
    P=mob(1<<((1<<0)|(1<<5)))&DOMAIN
    G=mob(1<<((1<<2)|(1<<3)))&DOMAIN
    S=space(AFFTT+(P,G))
    assert QS(S,qt).can(0)
    result={'status':'RELAXATION_HAS_SOLUTION' if counterexamples else 'RELAXATION_EXCLUDED',
      'orbits_checked':len(rows),'orbits_total':83,'counts':dict(count),
      'counterexamples':counterexamples,'positive_controls_detected':1,
      'human_proof_status':'OPEN','seconds':round(time.time()-t,3)}
    record('lambda1_quotient_exploration',result)
if __name__=='__main__':main()
