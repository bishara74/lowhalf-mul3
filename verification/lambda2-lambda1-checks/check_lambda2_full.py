"""Full lambda=2 sanity check, including every low-degree/redundant first
nonlinear gate; independent of the imported lambda=3 theorem."""
from check_lambda2_exact import Screen,products
from core import *
from collections import Counter

def main():
    t=time.time();rows=[]
    for idx,(Q,w) in enumerate(q2_orbits()):
        t0=time.time();pp=products(Q);pa=products(Q,True)
        early=[Screen(Q,T,pa) for T in (Z2,Z1^Z2)]
        z1=Screen(Q,Z1,pp);S=basis(Q+(Z1,));VS=v_basis(S);final=Screen(S,Z2)
        c=Counter();bad=[];zr=reduce(Z1,v_basis(Q))
        for g,m in pp.items():
            c['g2_cosets']+=1;c['g2_planes']+=m
            if any(es.feasible(g) for es in early):bad.append(['early',g])
            if g==zr:
                c['A_g2_planes']+=m
                for g3,m3 in products(S).items():
                    c['A_pairs']+=m*m3
                    if final.feasible(g3):bad.append(['A_final',g,g3])
            else:
                n0,n1=z1.count(g)
                if n0+n1:
                    c['B_g2_planes']+=m;c['B_pairs']+=m*(n0+n1)
                    if final.feasible(reduce(g,VS)):bad.append(['B_final',g])
        row={'orbit':idx,'weight':w,'counts':dict(c),'witnesses':bad,'seconds':round(time.time()-t0,3)}
        rows.append(row);print(json.dumps(row),flush=True)
        Path(__file__).with_name('lambda2_full.json').write_text(json.dumps(rows,indent=2)+'\n')
        assert not bad,row
    c=Counter();wc=Counter()
    for row in rows:
        c.update(row['counts']);wc.update({k:row['weight']*v for k,v in row['counts'].items()})
    ctl=Screen((P0,),mul(X[1]^P0,X[4]))
    assert ctl.feasible(0)
    record('lambda2_full',{'status':'PASS','Q_spaces':606,'Q_orbits':83,
       'scope':'all first nonlinear degrees, all later semantic nonlinear planes; final gate relaxed to any product',
       'totals':dict(c),'weighted_totals':dict(wc),'positive_controls_detected':1,
       'seconds':round(time.time()-t,3),'human_theorem_status':'OPEN: computational exclusion only'})
if __name__=='__main__':main()
