"""Complete check of the remaining OPEN human lemma: a noncore cubic
first gate, any next semantic nonlinear product, then free z1 and any final
product. A passing enumeration is not labelled a human proof.
"""
from core import *
from lambda1_states import orbits
from check_core_cubic import core_supported
from check_lambda2_exact import Screen,products
from collections import Counter

def main():
    t=time.time();c=Counter();rows=[]
    for idx,(g1,w,os) in enumerate(orbits(False)):
        if degree(g1)!=3 or core_supported(g1):continue
        B=basis((P0,g1));A=basis((P0,g1,Z1));VA=v_basis(A)
        final=Screen(A,Z2);pp=products(B)
        for g,m in pp.items():
            assert not final.feasible(reduce(g,VA)),(g1,g)
            c['g2_cosets']+=1;c['g2_planes']+=m
        c['g1_orbits']+=1;c['first_plane_weight']+=w
        rows.append({'orbit':idx,'g1':g1,'plane_weight':w,'g2_cosets':len(pp),'g2_planes':sum(pp.values())})
    assert c['g1_orbits']==164 and c['first_plane_weight']==1824
    target=mul(P0^X[2],X[5]);assert Screen((P0,),target).feasible(0)
    Path(__file__).with_name('noncore_onehigh_spaces.json').write_text(json.dumps(rows,indent=2)+'\n')
    record('noncore_onehigh',{'status':'PASS','counts':dict(c),'positive_controls_detected':1,
       'seconds':round(time.time()-t,3),'human_lemma_status':'OPEN: a nonenumerative argument is still missing',
       'scope':'all 164 noncore cubic first-output orbits, all next nonlinear products, every final product after freely adjoining z1'})
if __name__=='__main__':main()
