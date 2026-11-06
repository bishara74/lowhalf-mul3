"""Exact application-domain check of the new four-factor lemma.
Q=<P0> and every Q=<P0,P> with P rank two outside Lambda^2(U).
Enumerates ALL k in V(Q), ALL R in z1+V(Q), including constants.
The 32-element symmetry has already been independently checked.
"""
from collections import Counter
from core import *

K=(1^P0,1^X[0]^P0,1^X[3]^P0,X[0]^X[3]^P0)
KTT={mob(k) for k in K}|{FULL}

def inside_U(q):
    return all(not(q>>m)&1 or (m&U)==m for m in MONS2)

def main():
    t=time.time(); spaces=0; rawspaces=0; pairs=0; weightedpairs=0; identities=0
    used=Counter(); controls=0
    for Q,w in q2_orbits():
        if len(Q)>1 and all(inside_U(q) for q in Q): continue
        spaces+=1; rawspaces+=w
        vals=[mob(v) for v in elements(AFF+tuple(Q))]
        rs=[r^mob(Z1) for r in vals]
        for k in vals:
            seen=0
            for R in rs:
                pairs+=1; weightedpairs+=w
                if k&R==R:
                    identities+=1; seen+=1
                    assert k in KTT,(Q,mob(k),mob(R))
            if seen: used[str(mob(k))]+=1
        assert all(any((mob(k)&R)==R for R in rs) for k in K)
        # Relax the rank-four target to R=a0; k=a0 violates the claimed
        # conclusion, and the same membership predicate detects it.
        relaxed_R=mob(X[0]); relaxed_k=mob(X[0])
        assert relaxed_k&relaxed_R==relaxed_R and relaxed_k not in KTT
        controls+=1
    record('annihilator_four_factors',{'status':'PASS','Q_representatives':spaces,
       'Q_raw_spaces':rawspaces,'pairs_checked':pairs,'weighted_pairs':weightedpairs,
       'identities_found':identities,'factor_occurrences':dict(used),
       'positive_controls_detected':controls,'seconds':round(time.time()-t,3),
       'full_arbitrary_quadratic_domain_checked':False,
       'scope':'exact stated application domain, all k and R; not all pairs of arbitrary quadratic functions'})
if __name__=='__main__': main()
