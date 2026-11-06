"""Compare exact placement screens with direct enumeration of EVERY g2
plane for EVERY cubic first-gate output coset in lambda=1 (no orbit reduction).
This independently tests the screen and its feedback-plane multiplicities.
"""
from core import *
from check_lambda2_exact import Screen,products
from lambda1_states import states
from collections import Counter

def main():
    t=time.time();n=0;planes_count=0;hits=Counter()
    z1=Screen((P0,),Z1)
    z2=Screen((P0,),Z2)
    z12=Screen((P0,),Z1^Z2)
    for g in states():
        if not g&HIGH2:continue
        B=basis((P0,g));allp=products(B)
        for tag,T,s in [('z1',Z1,z1),('z2',Z2,z2),('z12',Z1^Z2,z12)]:
            actual=allp.get(reduce(T,v_basis(B)),0)
            screened=sum(s.count(g))
            assert screened==actual,(tag,g,actual,screened)
            hits[tag]+=actual
        n+=1;planes_count+=sum(allp.values())
    # Relaxed ordinary and feedback products, using the same actual code paths.
    g=reduce(mul(P0^X[1],X[4]),v_basis((P0,)))
    relaxed=mul(P0^1,g)
    assert Screen((P0,),relaxed,{}).count(g)[1]>0
    assert Screen((P0,),mul(P0^X[1],X[4])).feasible(0)
    record('screen_bruteforce',{'status':'PASS','first_cubic_output_cosets':n,
      'direct_planes':planes_count,'target_counts':dict(hits),
      'positive_controls_detected':2,'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
