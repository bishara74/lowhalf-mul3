"""Full finite rank and exterior-divisibility domains of the new lemmas.
Image membership covers EVERY 2-form theta, all 2^15 choices, exactly.
"""
from core import *
from check_annihilator import inside_U

def main():
    t=time.time();rank_tests=0;image_tests=0
    for a in (0,1):
        for e in (0,1):
            T=Q2_TARGET^(P0 if a else 0)^(Z1 if e else 0)
            assert rank(T)==6
            for P in R2:
                assert rank(T^P)>=4
                rank_tests+=1
    for P in R2:
        if inside_U(P):continue
        image=basis(mul(P,1<<m)&DEG[4] for m in MONS2)
        assert reduce(OMEGA,image)!=0
        image_tests+=1
    # Relax the outside-U hypothesis: a0*a1 divides Omega.
    P=wedge(1<<0,1<<1)
    image=basis(mul(P,1<<m)&DEG[4] for m in MONS2)
    assert reduce(OMEGA,image)==0
    # Removing a matching edge destroys the full-rank premise.
    assert rank(Q2_TARGET^(1<<((1<<1)|(1<<4))))<6
    record('rank_exterior',{'status':'PASS','rank_tests':rank_tests,
      'outside_rank_two_forms':image_tests,'theta_domain':'all 2^15 two-forms, exact image elimination for each P',
      'positive_controls_detected':2,'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
