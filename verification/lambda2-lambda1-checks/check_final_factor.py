"""Exact application domain of the last-factor rigidity lemma:
all k in V(<P0,P,Z1>), all R in z2+that space, for all rank-two P
outside Lambda^2(U), exhaustive using the verified symmetry group.
"""
from core import *
from check_annihilator import inside_U

def main():
    t=time.time();n=pairs=identities=0;allowed={FULL,mob(1^P0)}
    for Q,w in q2_orbits():
        if len(Q)<2 or all(inside_U(q) for q in Q):continue
        S=basis(Q+(Z1,));vals=[mob(v) for v in elements(AFF+S)]
        rs=[r^mob(Z2) for r in vals]
        seen=set()
        for k in vals:
            for R in rs:
                pairs+=1
                if k&R==R:
                    identities+=1;seen.add(k)
                    assert k in allowed,(Q,mob(k),mob(R))
        assert seen==allowed
        n+=1
    # Relaxing the target to a0 admits the forbidden nonconstant factor a0.
    k=mob(X[0]);R=k
    assert k&R==R and k not in allowed
    record('final_factor',{'status':'PASS','Q_representatives':n,'Q_raw_spaces':580,
       'pairs_checked':pairs,'identities_found':identities,'positive_controls_detected':1,
       'seconds':round(time.time()-t,3),
       'scope':'all k and R in the exact stated application domain, not arbitrary quartic functions'})
if __name__=='__main__':main()
