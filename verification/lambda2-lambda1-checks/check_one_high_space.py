"""All first nonlinear products g in V(Q), every Q, and all final products
in V(Q+<Z1>)+<g>. Stronger than checking only z1-admissible prefixes.
The screen tests the COMPLETE factor domain, not a necessary projection.
"""
from core import *
from check_lambda2_exact import products,Screen
from check_annihilator import inside_U
from collections import Counter

def main():
    t=time.time();c=Counter();rows=[]
    for idx,(Q,w) in enumerate(q2_orbits()):
        S=basis(Q+(Z1,));V=v_basis(S);screen=Screen(S,Z2)
        pp=products(Q,True)
        for g,m in pp.items():
            assert not screen.feasible(reduce(g,V)),(idx,Q,g)
            c['first_product_cosets']+=1;c['first_product_planes']+=m
        rows.append({'orbit':idx,'weight':w,'cosets':len(pp),'planes':sum(pp.values())})
    # Full coset-lemma extension domain: any g that is a product from V(S),
    # for each inside-U S needed in the proof, including non-rank-two-generated S.
    seen=set();extension=Counter()
    for Q,w in q2_orbits():
        if not all(inside_U(q) for q in Q):continue
        S=basis(Q+(Z1,))
        if S in seen:continue
        seen.add(S);screen=Screen(S,Z2)
        pp=products(S,True)
        for g,m in pp.items():
            assert not screen.feasible(g),(S,g)
            extension['g_cosets']+=1;extension['g_planes']+=m
    # Genuine reachable relaxed target; the same complete screen must admit it.
    target=mul(P0^X[1],X[4]);ctl=Screen((P0,),target)
    assert ctl.feasible(0)
    Path(__file__).with_name('one_high_spaces.json').write_text(json.dumps(rows,indent=2)+'\n')
    record('one_high_space',{'status':'PASS','Q_orbits':83,'Q_spaces':606,
      'counts':dict(c),'inside_U_extension':{'S_spaces':len(seen),**dict(extension)},
      'positive_controls_detected':1,'seconds':round(time.time()-t,3),
      'scope':'all g=f*h from V(Q), all F,H in V(Q+Z1)+<g>; and full imported-coset extension domains'})
if __name__=='__main__':main()
