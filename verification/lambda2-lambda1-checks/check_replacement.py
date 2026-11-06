"""Every nonlinear plane in V(Q)/<1> for all rank-two-generated Q containing
P0 with dim Q <= 2, exhaustive via the verified group (83 representatives).
Tests the exact rank-two increment and V containment for every quadratic product.
Also checks the lambda=1 application independently. No sampled domains.
"""
from collections import Counter
from core import *

def check_space(Q):
    V=v_basis(Q); qelts=elements(Q)
    rank2cosets={reduce(r,basis(Q)):r for r in R2}
    degs=Counter(); violations=[]; low=0; zero_increment=0; pc=0
    g_witness=None
    for f,h,p in gate_products(Q):
        d=degree(p); degs[str(d)]+=1
        if d>2: continue
        low+=1
        q=p&DEG[2]
        r=0 if reduce(q,basis(Q))==0 else rank2cosets.get(reduce(q,basis(Q)))
        if r is None:
            violations.append([f,h,p]); continue
        assert reduce(q^r,basis(Q))==0
        if r:
            l,m=R2_FACTORS[r]; gate=mul(linear(l),linear(m))
            assert gate&DEG[2]==r
        else:
            zero_increment+=1
            gate=0
        target_dim=len(Q)+1
        # Keep the existing independent linear prefix and insert one independent
        # rank-two direction; if r is already available, choose another direction.
        ext=list(Q)
        if r and reduce(r,basis(ext)): ext.append(r)
        for rr in R2:
            if len(ext)==target_dim: break
            if reduce(rr,basis(ext)): ext.append(rr)
        assert len(basis(ext))==target_dim
        assert reduce(p,v_basis(ext))==0
        assert all(reduce(v,v_basis(ext))==0 for v in AFF+tuple(Q)+(p,))
        # Constants and changes of basis of a factor plane preserve its output coset.
        for pp in (mul(f^1,h),mul(f,h^1),mul(f,f^h),mul(f^h,h)):
            assert reduce(pp^p,V)==0
        if g_witness is None:
            g_witness=(p,tuple(ext))
    # Mutation control on the same containment predicate: insert a quartic.
    p,ext=g_witness
    assert reduce(p^OMEGA,v_basis(ext))!=0
    pc+=1
    # Descriptions dependent modulo constants add an already available signal.
    # Check the complete dependent domain too, including nonaffine factors.
    dependent=0
    for f in elements(AFF+tuple(Q)):
        for p in (mul(f,f),mul(f,f^1),mul(f,0),mul(f,1)):
            assert degree(p)<=2 and reduce(p,V)==0
            dependent+=1
    assert not violations,violations[:1]
    return {'planes':sum(degs.values()),'degrees':dict(degs),'quadratic_products':low,
            'zero_increment':zero_increment,'violations':len(violations),
            'positive_controls_detected':pc,'dependent_descriptions':dependent}

def main():
    start=time.time(); total=Counter(); raw=Counter(); degree_counts=Counter(); raw_degrees=Counter()
    for i,(Q,weight) in enumerate(q2_orbits()):
        c=check_space(Q)
        for k in ('planes','quadratic_products','zero_increment','violations','positive_controls_detected','dependent_descriptions'):
            total[k]+=c[k]; raw[k]+=weight*c[k]
        degree_counts.update(c['degrees'])
        raw_degrees.update({k:weight*v for k,v in c['degrees'].items()})
    one=check_space((P0,))
    record('replacement',{'status':'PASS','domain':'all 606 Q spaces, all nonlinear planes modulo constants; 83 symmetry representatives',
       'representative_totals':dict(total),'weighted_totals':dict(raw),
       'representative_degrees':dict(degree_counts),'weighted_degrees':dict(raw_degrees),
       'lambda1_domain':one,'seconds':round(time.time()-start,3)})
if __name__=='__main__': main()
