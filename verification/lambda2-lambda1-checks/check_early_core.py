"""Every cubic first-output coset, all exact next-gate placements of z1.
The screen has separately been cross-checked by direct enumeration on this
entire domain in check_screen_bruteforce.py.
"""
from core import *
from lambda1_states import states
from check_lambda2_exact import Screen
from check_core_cubic import core_supported
from collections import Counter

def main():
    t=time.time();s=Screen((P0,),Z1);c=Counter()
    for g,m in states().items():
        if degree(g)!=3:continue
        a,b=s.count(g)
        assert b==0,(g,a,b)
        if a:
            assert core_supported(g),(g,a,b)
            c['placing_output_cosets']+=1;c['placing_pairs']+=a
            c['weighted_placing_pairs']+=m*a
        c['cubic_cosets']+=1;c['cubic_planes']+=m
    # Relax the target to an already reachable noncore cubic signal.
    g=mul(P0,X[2]);assert not core_supported(g)
    assert Screen((P0,),g).feasible(g)
    record('early_core',{'status':'PASS','counts':dict(c),'positive_controls_detected':1,
       'seconds':round(time.time()-t,3),'domain':'all 1740 cubic first-output cosets and every next semantic nonlinear plane'})
if __name__=='__main__':main()
