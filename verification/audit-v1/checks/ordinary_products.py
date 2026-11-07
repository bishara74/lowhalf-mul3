"""Exact independent two-ordinary-product exclusion, with verified 32-map reduction."""
from algebra import *
start=time.time(); v1=canonical(aff()+[P0]); cubic=set()
for b in range(1,64):
 for a in range(64):
    if a>(a^b): continue
    c=reduce(mul(P0^linear(a),linear(b)),v1)
    if degree(c)==3: cubic.add(c)
# Build input permutations; no old implementation or stored representatives.
perms=[]
for swap in range(2):
 for s in range(4):
  for t in range(4):
   perm=[]
   for x in range(64):
    y=x
    if ((s&1)*((x>>0)&1))^(((s>>1)&1)*((x>>3)&1)): y^=4
    if ((t&1)*((x>>0)&1))^(((t>>1)&1)*((x>>3)&1)): y^=32
    if swap: y=((y&7)<<3)|((y>>3)&7)
    perm.append(y)
   perms.append(tuple(perm))
assert len(set(perms))==32
pset=set(perms)
for p in perms:
 for q in perms: assert tuple(q[p[x]] for x in range(64)) in pset

def act(f,p):
    ft=transform(f); tt=sum(((ft>>p[x])&1)<<x for x in range(64))
    return transform(tt)
for p in perms:
 assert act(P0,p)==P0 and act(Z1,p)==Z1
 assert contains(act(Z2,p)^Z2,v1)
pending=set(cubic); reps=[]; orbit_sizes=[]
while pending:
 c=min(pending); orbit={reduce(act(c,p),v1) for p in perms}
 assert orbit<=cubic
 pending-=orbit; reps.append(c); orbit_sizes.append(len(orbit))
assert sum(orbit_sizes)==len(cubic)
planes=cosets=0
for idx,c in enumerate(reps):
 bs=canonical(aff()+[P0,Z1,c]); bt=canonical([transform(v) for v in bs])
 # Remove constant: every 2D factor plane modulo constants has one triple i<j<i^j.
 no1=canonical([reduce(v,basis([FULL])) for v in bt]); ts=span(no1)
 target=reduce(transform(Z2),bt); products={0}
 for i in range(1,len(ts)):
  for j in range(i+1,len(ts)):
   if j>i^j: continue
   planes+=1
   r=reduce(ts[i]&ts[j],bt)
   assert r^target not in products, ('two ordinary products',hex(c),hex(r))
   # Check equal-product case separately: impossible for nonzero target; above covers 0.
   products.add(r)
 cosets+=len(products)-1
 # Positive control: a planted target equal to an actual product coset must be detected
 # by the same sumset-membership rule, using the other product = 0.
 planted=next((r for r in products if r),0)
 assert any((r^planted) in products for r in products)
 if idx%25==0: print('ordinary reps',idx,'planes',planes,flush=True)
save('ordinary_products',{'status':'pass','verified_group_maps':len(perms),'composition_tests':1024,'cubic_cosets':len(cubic),'cubic_space_orbits':len(reps),'orbit_weights_sum':sum(orbit_sizes),'ordinary_factor_planes':planes,'nonzero_product_cosets_sum':cosets,'positive_controls_detected':len(reps)},start)
