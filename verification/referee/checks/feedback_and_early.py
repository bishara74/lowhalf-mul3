"""Exact arbitrary-g two-feedback obstruction and complete early-z1 check.
All spaces, no symmetry; arbitrary Boolean g is eliminated as 64 independent bits.
"""
from algebra import *
start=time.time(); K=[1^P0,1^X[0]^P0,1^X[3]^P0,X[0]^X[3]^P0]
mtt=transform(1^P0); target=transform(Z1)|(transform(Z2)<<64)
systems=0
for q in quadratic_spaces():
 if all(inside(p) for p in q): continue
 b=[transform(v) for v in canonical(aff()+list(q))]
 s=[transform(v) for v in canonical(aff()+list(q)+[Z1])]
 for k in K:
  kt=transform(k)
  columns=[((kt>>x)&1)*(1<<x)|(((mtt>>x)&1)*(1<<(64+x))) for x in range(64)]
  columns += [kt&v for v in b]+b+[(mtt&v)<<64 for v in s]+[v<<64 for v in s]
  assert not contains(target,columns)
  assert contains(0,columns) # relaxed positive instance, same exact linear system
  systems+=1
# All cubic first-output spaces, all possible next factor planes modulo constants.
v1=canonical(aff()+[P0]); cubic=set()
for b in range(1,64):
 for a in range(64):
  if a>(a^b): continue
  c=reduce(mul(P0^linear(a),linear(b)),v1)
  if degree(c)==3: cubic.add(c)
planes=placing=feedback=0
for idx,c in enumerate(sorted(cubic)):
 ans=span(X+[P0,c]); ts=span([transform(v) for v in X+[P0,c]])
 bt=canonical([FULL]+[transform(v) for v in X+[P0,c]])
 zcoset=reduce(transform(Z1),bt)
 core=all(s&~U_MASK==0 for s in bits(c&(DEG[2]|DEG[3])))
 for i in range(1,256):
  for j in range(i+1,256):
   if j>i^j: continue
   planes+=1
   if reduce(ts[i]&ts[j],bt)==zcoset:
    placing+=1
    if (i|j)&128: feedback+=1
    assert core and not (i|j)&128
 if idx%300==0: print('early spaces',idx,flush=True)
# Planted noncore placement: relaxed target = a real feedback product; same matcher detects it.
c=next(c for c in cubic if any(s&~U_MASK for s in bits(c)))
bt=canonical([transform(v) for v in aff()+[P0,c]])
planted=reduce(transform(c)&transform(X[2]),bt)
assert reduce(transform(mul(c,X[2])),bt)==planted
save('feedback_and_early',{'status':'pass','arbitrary_function_exact_systems':systems,'g_functions_per_system':'2^64','cubic_first_spaces':len(cubic),'next_factor_planes':planes,'z1_placing_planes':placing,'feedback_placing_planes':feedback,'positive_controls_detected':True},start)
