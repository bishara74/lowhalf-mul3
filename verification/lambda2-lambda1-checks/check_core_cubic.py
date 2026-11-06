"""All cubic first-output spaces supported on U, all product g from the
enlarged base B=Aff+<P0,Z1,g1>, and every last product from B+<g>.
The screen covers the complete factor domain by exact binary elimination.
"""
from core import *
from lambda1_states import orbits
from check_lambda2_exact import Screen,products
from collections import Counter

def core_supported(g):
    return all(not((g>>m)&1) or m.bit_count()<2 or m&U==m for m in range(64))

def main():
    t=time.time();counts=Counter();rows=[]
    for idx,(g1,w,os) in enumerate(orbits(False)):
        if degree(g1)!=3 or not core_supported(g1):continue
        t0=time.time();S=basis((P0,Z1,g1));screen=Screen(S,Z2)
        Wvals=elements((1,)+tuple(X[i] for i in (0,1,3,4))+(P0,Z1,g1))
        for a in Wvals:
            assert not a&OMEGA
            assert not mul(a,a)&OMEGA
            assert all(not mul(a,r)&OMEGA for r in (1,X[0],X[3]))
        pp=products(S,True)
        for g,m in pp.items():
            assert not screen.feasible(g),(g1,g)
            counts['first_product_cosets']+=1;counts['first_product_planes']+=m
        counts['first_cubic_plane_weight']+=w
        row={'orbit':idx,'g1':g1,'weight':w,'g_cosets':len(pp),'g_planes':sum(pp.values()),'seconds':round(time.time()-t0,3)}
        rows.append(row);print(json.dumps(row),flush=True)
        Path(__file__).with_name('core_cubic_spaces.json').write_text(json.dumps(rows,indent=2)+'\n')
    assert len(rows)==33 and counts['first_cubic_plane_weight']==96
    # A reachable relaxed target exercises the same final-product predicate.
    S=basis((P0,Z1,mul(P0,X[1])));T=mul(P0^X[2],X[5])
    assert Screen(S,T).feasible(0)
    record('core_cubic',{'status':'PASS','first_cubic_orbits':len(rows),'counts':dict(counts),
       'positive_controls_detected':1,'seconds':round(time.time()-t,3),
       'domain':'all core cubic first-product spaces, all g products in their enlarged base, all last factors'})
if __name__=='__main__':main()
