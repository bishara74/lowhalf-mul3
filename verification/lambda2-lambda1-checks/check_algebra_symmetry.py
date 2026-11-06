"""Exact domains: all 4096 monomial pairs; all 32 transformations and
64 input points; all 606 rank-two-generated Q2 spaces. Positive controls
are deliberately corrupted identities/targets and must be rejected.
"""
from core import *

def main():
    start=time.time()
    for i in range(64):
        for j in range(64):
            assert mul(1<<i,1<<j) == 1<<(i|j)
    for f in (0,FULL,Z1,Z2,OMEGA)+X:
        assert mob(mob(f))==f
    assert mul_slow(Z2,Z1)==mul(Z2,Z1)
    assert len(R2)==651 and all(rank(r)==2 for r in R2)
    assert len(set(GROUP))==32
    affine0=v_basis((P0,))
    points_checked=0
    for g in GROUP:
        assert substitute(P0,g)==P0 and substitute(Z1,g)==Z1
        assert reduce(substitute(Z2,g)^Z2,affine0)==0
        assert substitute(OMEGA,g)==OMEGA
        mapped=[]
        tt=[mob(f) for f in g]
        for x in range(64):
            mapped.append(sum(((t>>x)&1)<<i for i,t in enumerate(tt)))
            points_checked+=1
        assert len(set(mapped))==64
        # Closure is separately checked by composing substitutions below.
    members=set(GROUP)
    for g in GROUP:
        for h in GROUP:
            assert tuple(substitute(f,h) for f in g) in members
    spaces=q2_spaces(); orb=q2_orbits()
    assert len(spaces)==606 and len(orb)==83 and sum(w for q,w in orb)==606
    # Mutation controls: an erroneous product identity and nonpreserving transform.
    assert mul(1<<3,1<<5) != (1<<(3|5))^1
    bad=list(X); bad[5]^=X[1]
    assert reduce(substitute(Z2,bad)^Z2,affine0)!=0
    out={'status':'PASS','monomial_products':4096,'rank_two_forms':651,
         'group_elements':32,'group_compositions':1024,'point_bijection_tests':points_checked,
         'Q2_spaces':606,'Q2_orbits':83,'positive_controls_detected':2,
         'seconds':round(time.time()-start,3)}
    record('algebra_symmetry',out)
if __name__=='__main__': main()
