"""Exhaustive multiplier identities by exact linear algebra, all input points.
For each k, solve (1+k)(target+v)=0 with v in the full stated base space.
This enumerates all k and proves feasibility/infeasibility for every v at once.
No symmetry reduction, no SAT, no sampling, no pre-existing scripts.
"""
from algebra import *
start=time.time(); results={}

def feasible(ktt,targettt,base_tt):
    zeros=FULL^ktt
    return contains(targettt&zeros,[v&zeros for v in base_tt])

def run_family(spaces,target,allowed,name):
    total=accepted=0; bad=[]
    targettt=transform(target)
    for key,bs in spaces:
        bs=canonical(bs); bt=[transform(v) for v in bs]
        funcs=span(bs); tables=span(bt)
        for k,kt in zip(funcs,tables):
            total+=1
            yes=feasible(kt,targettt,bt)
            if yes: accepted+=1
            if yes and not allowed(k):
                bad.append({'space':str(key),'k_anf':hex(k),'k':formula(k)})
                if len(bad)>=10: break
        if len(bad)>=10: break
    results[name]={'spaces':len(spaces),'all_k_tested':total,'feasible_k':accepted,'violations':bad}
    print(name,total,len(bad),flush=True)

K=[1^P0,1^X[0]^P0,1^X[3]^P0,X[0]^X[3]^P0]
qspaces=quadratic_spaces(); outside=[b for b in qspaces if any(not inside(p) for p in b)]
four_spaces=[('P0',aff()+[P0])]+[(str(b),aff()+list(b)) for b in outside]
run_family(four_spaces,Z1,lambda k:k==1 or k in K,'four_multipliers')
last_spaces=[(str(b),aff()+list(b)+[Z1]) for b in outside]
run_family(last_spaces,Z2,lambda k:k in (1,1^P0),'last_factor')
# All distinct cubic first-output cosets modulo V1, including core/noncore edge spaces.
v1=canonical(aff()+[P0]); cubics=set()
for b in range(1,64):
 for a in range(64):
    if a>(a^b): continue
    c=reduce(mul(P0^linear(a),linear(b)),v1)
    if degree(c)==3: cubics.add(c)
noncore=[c for c in sorted(cubics) if any(s&~U_MASK for s in bits(c&(DEG[2]|DEG[3])))]
noncore_spaces=[(hex(c),aff()+[P0,Z1,c]) for c in noncore]
run_family(noncore_spaces,Z2,lambda k:((k^1)&~IDEAL)==0,'noncore_multiplier')
# Positive controls use exactly the same feasibility engine and deliberately relaxed targets.
b=canonical(aff()+[P0]); bt=[transform(v) for v in b]
assert feasible(transform(P0),transform(P0),bt) and P0 not in [1]+K
b=canonical(aff()+[P0,Z1]+list(outside[0])); bt=[transform(v) for v in b]
assert feasible(transform(P0),transform(P0),bt) and P0 not in (1,1^P0)
c=noncore[0]; b=canonical(aff()+[P0,Z1,c]); bt=[transform(v) for v in b]
assert feasible(transform(c),transform(c),bt) and ((c^1)&~IDEAL)!=0
assert all(not v['violations'] for v in results.values())
save('multipliers',{'status':'pass','families':results,'all_cubic_cosets':len(cubics),'core_cubic_cosets':len(cubics)-len(noncore),'noncore_cubic_cosets':len(noncore),'positive_controls_detected':3},start)
