"""Every cubic first-output space, all pairs of products from the enlarged
base A=Aff+<P0,Z1,c>. The product-coset set is enumerated completely;
intersection with its target translate tests all ordered pairs at once.
"""
from core import *
from lambda1_states import orbits
from check_lambda2_exact import products
from collections import Counter

def check():
    t=time.time();c=Counter()
    for g,w,os in orbits(False):
        if degree(g)!=3:continue
        S=basis((P0,Z1,g));pp=products(S,True);target=reduce(Z2,v_basis(S))
        assert target and all((r^target) not in pp for r in pp),(g,target)
        c['cubic_orbits']+=1;c['first_product_planes']+=sum(pp.values())
        c['product_cosets']+=len(pp)
    # Plant a reachable relaxed target in a genuine product-coset set.
    S=basis((P0,Z1,mul(P0,X[1])));pp=products(S,True)
    target=reduce(mul(P0^X[2],X[5]),v_basis(S))
    assert target and any((r^target) in pp for r in pp)
    return {'status':'PASS','counts':dict(c),'positive_controls_detected':1,
       'seconds':round(time.time()-t,3),
       'domain':'all 197 cubic first-output orbits, all four factors in the enlarged base A; every output correction in A'}
if __name__=='__main__':record('ordinary_pair',check())
