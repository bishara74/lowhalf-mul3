"""Test a stronger lambda=1 intermediate-space obstruction without the
z1-placement screen. A counterexample is a relaxed prefix, not a circuit
computing the original target. Never label the hypothesis proved by this run.
"""
from core import *
from lambda1_states import orbits
from check_core_cubic import core_supported
from check_lambda2_exact import Screen,products
from collections import Counter

def main():
    t=time.time();c=Counter();bad=[]
    for idx,(g1,w,os) in enumerate(orbits(False)):
        if degree(g1)!=3 or core_supported(g1):continue
        B=basis((P0,g1));A=basis((P0,g1,Z1));VA=v_basis(A)
        last=Screen(A,Z2)
        for g,m in products(B).items():
            c['g2_cosets']+=1
            if last.feasible(reduce(g,VA)):
                bad.append({'orbit':idx,'g1':g1,'g2':g});break
        c['g1_orbits']+=1
        print(json.dumps({'orbit':idx,'bad':bad[-1:] if bad else []}),flush=True)
        if bad:break
    T=mul(P0^X[2],X[5]);assert Screen((P0,),T).feasible(0)
    record('noncore_onehigh_exploration',{'status':'RELAXED_SOLUTION' if bad else 'ALL_EXCLUDED',
      'counts':dict(c),'counterexamples':bad,'positive_controls_detected':1,
      'human_proof_status':'OPEN','seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
