"""All exact available-space identities used in the rank-two reordering
proposition, for all qualifying Q and all higher-degree first-gate products.
Equality of linear spaces checks every possible output correction and tail
factor function at once, rather than sampling such functions.
"""
from core import *
from check_lambda2_exact import products

def main():
    t=time.time();qcount=0;spaces=0;weighted=0
    for Q,w in q2_orbits():
        rho=next((Z1^q for q in elements(Q) if Z1^q in R2_SET),None)
        if rho is None:continue
        qcount+=1
        for g in products(Q):
            if not g&HIGH2:continue
            old=basis(AFF+Q+(g,Z1))
            new=basis(AFF+Q+(rho,g))
            assert old==new
            assert reduce(Z1,basis(AFF+Q+(g,)))!=0
            assert all(reduce(v,v_basis(Q+(rho,)))==0 for v in AFF+Q)
            spaces+=1;weighted+=w
    # Delete the proposed new direction: the needed z1 becomes unavailable.
    Q=next(Q for Q,w in q2_orbits() if any(Z1^q in R2_SET for q in elements(Q)))
    assert reduce(Z1,v_basis(Q))!=0
    record('rank_two_reordering',{'status':'PASS','Q_representatives':qcount,
       'higher_degree_output_spaces':spaces,'weighted_spaces':weighted,
       'positive_controls_detected':1,'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
