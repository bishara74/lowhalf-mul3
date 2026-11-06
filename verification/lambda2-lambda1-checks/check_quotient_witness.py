"""Reconstruct and independently simulate the four-gate relaxed-domain
counterexample. It is not a circuit for the original six-variable targets.
"""
from core import *
from explore_lambda1_quotient import DOMAIN,AFFTT,space

def find_product(B,T):
    BB=basis(B);target=reduce(T,BB);vals=elements(B[1:])
    for i,j in planes(len(B)-1,None):
        p=vals[i]&vals[j]
        if reduce(p,BB)==target:return vals[i],vals[j],p
    raise AssertionError('reported relaxed solution has no product witness')

def expression(rows,t):
    piv={}
    for i,r in enumerate(rows):
        e=1<<i
        while r:
            p=r.bit_length()-1
            if p in piv:r^=piv[p][0];e^=piv[p][1]
            else:piv[p]=(r,e);break
    e=0
    while t:
        p=t.bit_length()-1
        assert p in piv
        t^=piv[p][0];e^=piv[p][1]
    return e

def evaluate(e,rows):return xor_many(r for i,r in enumerate(rows) if (e>>i)&1)

def main():
    t=time.time()
    # Fixed discovery fixture makes this witness check reproducible even when
    # results.json is rebuilt from scratch by run_all.py.
    case={'Q':[4096,512],'g2_tt':9570733332627490,'first_target_tt':1469951019806642176}
    Q=tuple(case['Q']);B=space(AFFTT+tuple(mob(q)&DOMAIN for q in Q))
    P=next(q for q in Q if q!=P0);l,r=R2_FACTORS[P]
    gates=[(mob(linear(l))&DOMAIN,mob(linear(r))&DOMAIN)]
    p1=gates[0][0]&gates[0][1]
    # The first product may differ from P's pure quadratic representative
    # by an affine function; the available space is unchanged.
    f,h,p2=find_product(B,case['g2_tt']);gates.append((f,h))
    B2=space(B+(p2,));T=case['first_target_tt']
    f,h,p3=find_product(B2,T);gates.append((f,h))
    B3=space(B2+(p3,));zt=mob(Z1)&DOMAIN;qt=mob(Q2_TARGET)&DOMAIN
    other=qt if T==zt else zt
    f,h,p4=find_product(B3,other);gates.append((f,h))
    rows=list(AFFTT);net=[]
    for f,h in gates:
        a=expression(rows,f);b=expression(rows,h)
        assert evaluate(a,rows)==f and evaluate(b,rows)==h
        p=f&h;net.append({'L_coefficients':a,'R_coefficients':b,'output_tt':p})
        rows.append(p)
    outputs={name:expression(rows,T) for name,T in [('z1',zt),('q2',qt)]}
    assert evaluate(outputs['z1'],rows)==zt and evaluate(outputs['q2'],rows)==qt
    assert evaluate(outputs['q2'],rows)^1!=qt
    witness={'domain':'48 points satisfying a0*b0=0; carry vanishes here',
       'coordinate_order':['1','a0','a1','a2','b0','b1','b2','t0','t1','t2','t3'],
       'gates':net,'outputs':outputs,'domain_tt':DOMAIN}
    Path(__file__).with_name('quotient_relaxed_witness.json').write_text(json.dumps(witness,indent=2)+'\n')
    record('quotient_witness',{'status':'PASS','gates':4,'input_points':DOMAIN.bit_count(),
       'positive_controls_detected':1,'seconds':round(time.time()-t,3),
       'meaning':'independent simulation verifies the quotient-only shortcut has a relaxed counterexample'})
if __name__=='__main__':main()
