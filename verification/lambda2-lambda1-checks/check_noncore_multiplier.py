"""Full application domain of noncore multiplier rigidity modulo I.
For every k and R in z2+A satisfying kR=R, check k=1 modulo (a0*b0).
Both k and R may be cubic/quartic. No function pairs are sampled.
"""
from core import *
from lambda1_states import orbits
from check_core_cubic import core_supported
from check_ideal_extraction import KEEP
from collections import Counter

def check():
    t=time.time();c=Counter()
    for g,w,os in orbits(False):
        if degree(g)!=3 or core_supported(g):continue
        S=basis((P0,Z1,g));vals=[mob(v) for v in elements(AFF+S)]
        allowed={k for k in vals if not ((mob(k)^1)&KEEP)}
        targets=[v^mob(Z2) for v in vals]
        for k in vals:
            for R in targets:
                c['pairs']+=1
                if k&R==R:
                    assert k in allowed,(g,mob(k),mob(R))
                    c['identities']+=1
        c['cubic_orbits']+=1;c['first_plane_weight']+=w
    # Relaxing the target to a0 admits k=a0, which is not 1 modulo I.
    k=mob(X[0]);R=k
    assert k&R==R and ((mob(k)^1)&KEEP)
    return {'status':'PASS','counts':dict(c),'positive_controls_detected':1,
       'seconds':round(time.time()-t,3),
       'domain':'all 164 noncore cubic first-output orbits; every k in A and every R in z2+A'}
if __name__=='__main__':record('noncore_multiplier',check())
