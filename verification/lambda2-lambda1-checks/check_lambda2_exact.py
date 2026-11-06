"""Independent exhaustive high-degree lambda=2 check, without SAT.
Collapses products only modulo the available space. For every actual first
nonlinear plane retain its multiplicity. Tests all possible placements at the
next and final gate using the exact multiplier identity k*(g+F).
The accompanying proof draft explains why the split is exhaustive.
"""
from collections import Counter
from core import *
from placement import eligible_data

def products(Q, all_planes=False):
    vals=elements(X+tuple(Q)); tts=[mob(v) for v in vals]
    B=v_basis(Q); out=Counter()
    pl=planes(len(X+tuple(Q)),None) if all_planes else PLANES[len(X+tuple(Q))]
    for i,j in pl: out[reduce(mob(tts[i]&tts[j]),B)]+=1
    return out

class Screen:
    def __init__(self,Q,target,prod=None):
        self.Q=Q; self.V=basis(tt_basis:=tuple(mob(v) for v in AFF+tuple(Q)))
        self.target=reduce(mob(target),self.V)
        self.prod=products(Q,True) if prod is None else prod
        self.target_anf=reduce(target,v_basis(Q))
        Fs=elements(X+tuple(Q)); Ft=[mob(f) for f in Fs]
        self.feedback=[]
        for ki,k,S in eligible_data(Q,target):
            d={}
            for j,F in enumerate(Ft):
                r=reduce(k&F,self.V)
                d.setdefault(r,[]).append(j)
            self.feedback.append((ki,k,d))
    def count(self,g,counts=True):
        # g is outside V. Each no-feedback plane appears once. In feedback
        # normalization, F and F+k give one plane; k and k+1 encode the two
        # output coefficients of g, and cannot both count the same plane.
        if self.target_anf in (0,g): return (1,0)
        if not g: return (self.prod.get(self.target_anf,0),0)
        ordinary=self.prod.get(self.target_anf,0)+self.prod.get(self.target_anf^g,0)
        if ordinary and not counts: return (ordinary,0)
        gt=mob(g); fb=0
        for ki,k,d in self.feedback:
            key=self.target ^ reduce(k&gt,self.V)
            found=d.get(key,())
            assert len(found)%2==0
            fb+=len(found)//2
            if fb and not counts: break
        return ordinary,fb
    def feasible(self,g): return any(self.count(g,False))

def main():
    import argparse
    ap=argparse.ArgumentParser(); ap.add_argument('--start',type=int,default=0); ap.add_argument('--stop',type=int,default=83)
    args=ap.parse_args(); t=time.time(); rows=[]
    for idx,(Q,w) in enumerate(q2_orbits()):
        if not args.start<=idx<args.stop: continue
        t0=time.time(); pnonlin=products(Q); pall=products(Q,True)
        early=[Screen(Q,T,pall) for T in (Z2,Z1^Z2)]
        z1=Screen(Q,Z1,pnonlin)
        S=basis(Q+(Z1,)); final=Screen(S,Z2)
        c=Counter(); witness=[]
        for g,mult in pnonlin.items():
            if not g&HIGH2: continue
            c['high_cosets']+=1; c['high_planes']+=mult
            if any(screen.feasible(g) for screen in early):
                c['early_target_cosets']+=1; witness.append(['early',g])
            n0,n1=z1.count(g)
            if n0+n1:
                c['z1_admissible_cosets']+=1
                c['z1_admissible_planes']+=mult
                c['placing_pairs']+=mult*(n0+n1)
                if final.feasible(reduce(g,v_basis(S))):
                    c['final_feasible_cosets']+=1; witness.append(['final',g])
        row={'orbit':idx,'weight':w,'Q':list(Q),'counts':dict(c),'witnesses':witness,'seconds':round(time.time()-t0,3)}
        rows.append(row)
        print(json.dumps(row,sort_keys=True),flush=True)
        assert not witness,row
        Path(__file__).with_name(f'lambda2_exact_{args.start}_{args.stop}.json').write_text(json.dumps(rows,indent=2)+'\n')
    totals=Counter(); weighted=Counter()
    for row in rows:
        totals.update(row['counts']); weighted.update({k:row['weight']*v for k,v in row['counts'].items()})
    # Positive controls: plant the target itself as a product and as a feedback
    # product (in a relaxed target problem), using exactly the same predicates.
    pc=Screen((P0,),Z1,{reduce(Z1,v_basis((P0,))):1})
    assert pc.feasible(OMEGA)
    Q=(P0,); g=mul(P0^X[1],X[4]); target=mul(P0^1,g)
    # target may be high degree; the general annihilator screen still applies.
    relax=Screen(Q,target,{})
    assert relax.feasible(reduce(g,v_basis(Q)))
    result={'status':'PASS' if args.start==0 and args.stop==83 else 'PARTIAL_PASS',
      'scope':'all higher-degree first nonlinear gates for normalized lambda=2; low degree excluded by replacement',
      'range':[args.start,args.stop],'totals':dict(totals),'weighted_totals':dict(weighted),
      'positive_controls_detected':2,'seconds':round(time.time()-t,3),
      'human_theorem_status':'OPEN: this exhaustive search is not a human-style exclusion proof'}
    record(f'lambda2_exact_{args.start}_{args.stop}',result)
if __name__=='__main__': main()
