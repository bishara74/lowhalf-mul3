"""Exact statement on ALL Boolean g (2^64 choices), via complete linear
elimination, for every applicable Q and each of the four allowed k.
The unknown auxiliary factors and output corrections are eliminated too.
"""
from core import *
from check_annihilator import K,inside_U

def feasible(Q,k_anf,target=Z2):
    V=tuple(mob(v) for v in AFF+Q)
    S=V+(mob(Z1),)
    k=mob(k_anf);t=mob(1^P0)
    A=V+tuple(k&v for v in V)
    B=S+tuple(t&s for s in S)
    columns=tuple(A)+tuple(b<<64 for b in B)
    columns+=tuple((k&(1<<j))^((t&(1<<j))<<64) for j in range(64))
    return not reduce(mob(Z1)^(mob(target)<<64),basis(columns))

def main():
    t=time.time();n=raw=0
    for Q,w in q2_orbits():
        if len(Q)<2 or all(inside_U(q) for q in Q):continue
        for k in K:
            assert not feasible(Q,k),(Q,k)
            n+=1;raw+=w
    relaxed=basis((P0,wedge(1<<1,1<<4)))
    controls=sum(feasible(relaxed,k,0) for k in K)
    assert controls>0
    record('two_feedback',{'status':'PASS','Q_representatives':n//4,
      'exact_linear_systems':n,'weighted_systems':raw,
      'g_domain':'all 2^64 Boolean functions, covered exactly by linear elimination',
      'positive_controls_detected':controls,'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
