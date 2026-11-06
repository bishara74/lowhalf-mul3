"""Checkpointed exhaustive first nonlinear gate census; not a last-gate proof."""
from collections import Counter
from core import *

def census(Q, targets=None):
    V=v_basis(Q); out={}; degs=Counter(); hits=Counter()
    for f,h,p in gate_products(Q):
        r=reduce(p,V)
        out[r]=out.get(r,0)+1
        degs[str(degree(p))]+=1
        for tag,t in (targets or [('z1',Z1),('z2',Z2),('z1_plus_z2',Z1^Z2)]):
            if r==reduce(t,V): hits[tag]+=1
    return out,dict(degs),dict(hits)

def main():
    t=time.time(); stats=[]; total=Counter(); cache=[]
    for idx,(Q,w) in enumerate(q2_orbits()):
        out,degs,hits=census(Q)
        mr=min(rank(Z1^q) for q in elements(Q))
        high={p:c for p,c in out.items() if p&HIGH2}
        stats.append({'orbit':idx,'weight':w,'Q':list(Q),'minrank_Z1_coset':mr,
                      'distinct_output_cosets':len(out),'distinct_high_output_cosets':len(high),'hits':hits,'degrees':degs})
        cache.append({'orbit':idx,'weight':w,'Q':list(Q),'states':[[p,c] for p,c in sorted(high.items())]})
        total['representative_high_cosets']+=len(high)
        total['weighted_high_cosets']+=w*len(high)
        total['z1_placing_planes']+=hits.get('z1',0)
    path=Path(__file__).with_name('lambda2_prefixes.json')
    path.write_text(json.dumps(cache,separators=(',',':'))+'\n')
    all1,degs1,hits1=census((P0,))
    _,_,control=census((P0,),[('planted',mul(P0,X[1]))])
    assert control['planted']>0
    record('prefix_census',{'status':'PASS','scope':'first nonlinear gate only; no claim on completions',
          'Q2_orbits':stats,'totals':dict(total),'lambda1':{'distinct_output_cosets':len(all1),
          'distinct_high_output_cosets':sum(bool(p&HIGH2) for p in all1),'degrees':degs1,'hits':hits1},
          'positive_controls_detected':control['planted'],'seconds':round(time.time()-t,3)})
if __name__=='__main__': main()
