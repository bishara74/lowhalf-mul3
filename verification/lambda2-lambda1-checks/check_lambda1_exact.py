"""Independent full normalized lambda=1 enumeration via function-space orbits.
All first nonlinear planes, including quadratic/redundant products, are covered.
For a fixed g1, the two z1-placement branches share one exact final-gate screen.
No imported lower-bound theorem, SAT code, or historical count is used.
"""
from check_lambda2_exact import Screen, products
from lambda1_states import orbits
from collections import Counter
from core import *

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=10000)
    args=ap.parse_args(); O=orbits(False); t=time.time(); rows=[]
    for idx,(g1,w,osize) in enumerate(O):
        if not args.start<=idx<args.stop:continue
        t0=time.time(); Q=basis((P0,g1)); pp=products(Q); pa=products(Q,True)
        z1=Screen(Q,Z1,pp); early=[Screen(Q,T,pa) for T in (Z2,Z1^Z2)]
        S=basis(Q+(Z1,)); final=Screen(S,Z2)
        VQ=v_basis(Q); VS=v_basis(S); z1res=reduce(Z1,VQ)
        counts=Counter(); bad=[]
        for g2,m in pp.items():
            counts['g2_cosets']+=1;counts['g2_planes']+=m
            if any(es.feasible(g2) for es in early):
                counts['early_target_cosets']+=1;bad.append(['early',g2])
            if g2==z1res:
                counts['A_g2_planes']+=m
                # All g3 products, not only those passing a z1-placement test.
                p3=products(S)
                for g3,m3 in p3.items():
                    counts['A_pairs']+=m*m3
                    if final.feasible(g3):bad.append(['A_final',g2,g3])
            else:
                n0,n1=z1.count(g2)
                if n0+n1:
                    counts['B_admissible_g2_cosets']+=1
                    counts['B_admissible_g2_planes']+=m
                    counts['B_pairs']+=m*(n0+n1)
                    if final.feasible(reduce(g2,VS)):
                        counts['final_feasible_cosets']+=1;bad.append(['B_final',g2])
        row={'orbit':idx,'g1':g1,'g1_degree':degree(g1),'plane_weight':w,'function_orbit_size':osize,
             'counts':dict(counts),'witnesses':bad,'seconds':round(time.time()-t0,3)}
        rows.append(row);print(json.dumps(row,sort_keys=True),flush=True)
        Path(__file__).with_name(f'lambda1_exact_{args.start}_{min(args.stop,len(O))}.json').write_text(json.dumps(rows,indent=2)+'\n')
        assert not bad,row
    total=Counter();weighted=Counter()
    for row in rows:
        total.update(row['counts']);weighted.update({k:row['plane_weight']*v for k,v in row['counts'].items()})
    # Genuine relaxed products exercise the ordinary and feedback paths.
    base=(P0,);g=mul(P0^X[1],X[4]);g=reduce(g,v_basis(base))
    relaxed=mul(P0^1,g)
    ctl=Screen(base,relaxed,{})
    assert ctl.feasible(g)
    ordinary=mul(X[1]^P0,X[4])
    ctl2=Screen(base,ordinary)
    assert ctl2.feasible(0)
    result={'status':'PASS' if args.start==0 and args.stop>=len(O) else 'PARTIAL_PASS',
        'scope':'all normalized lambda=1 circuits, all first nonlinear factor planes, all later semantic nonlinear planes; final gate relaxed to any product',
        'function_space_orbits_total':len(O),'orbits_checked':len(rows),
        'first_gate_plane_weight':sum(r['plane_weight'] for r in rows),
        'totals':dict(total),'weighted_totals':dict(weighted),'positive_controls_detected':2,
        'seconds':round(time.time()-t,3),'human_theorem_status':'OPEN: no complete human-style higher-degree exclusion'}
    record(f'lambda1_exact_{args.start}_{min(args.stop,len(O))}',result)
if __name__=='__main__':main()
