"""One million NONVACUOUS product/radical instances in six variables.
Sample uniformly from all admissible nonlinear four-coordinate factor planes,
then independently embed four linear coordinates into six. Every sampled pair
satisfies the product lemma's hypotheses; this is a stress test, not an exhaustive
proof on six-variable pairs. Rank-zero/2/4 edge types included explicitly.
"""
from algebra import *
from itertools import combinations
import random
start=time.time(); rng=random.Random(611271)
# Pool in four abstract coordinates, including all three product-lemma branches.
inds=[0,1,2,3]; mons=[0]+[1<<i for i in inds]+[(1<<i)|(1<<j) for i,j in combinations(inds,2)]
abstract=span([1<<s for s in mons[1:]])
tables=span([transform(1<<s) for s in mons[1:]])
pool=[]
for i in range(1,1024):
 for j in range(i+1,1024):
  if j>i^j: continue
  if not (abstract[i]|abstract[j])&DEG[2]: continue
  if degree(transform(tables[i]&tables[j]))<=2: pool.append((i,j))
assert len(pool)==7560
qmons=[s for s in range(64) if s.bit_count()==2]
qs=span([1<<s for s in qmons]); ranks={q:rank(q) for q in qs}
ss={}
for q in rank2forms(): ss[q]=sum(1<<v for v in span(support(q)) if v)
# Radical conclusion equivalent to support inclusion; compute using direction-kernel masks.
rad={}
for q in qs:
 if ranks[q]>=4: rad[q]=sum(1<<d for d in range(64) if not contraction(q,d))
counts={'P1':0,'P2':0,'P3':0}; checked=1_000_000; ordered_radicals=0
for trial in range(checked):
 while True:
  coords=[rng.randrange(1,64) for _ in range(4)]
  if len(basis(coords))==4: break
 vars=[transform(linear(v)) for v in coords]
 ims=vars+[vars[i]&vars[j] for i,j in combinations(range(4),2)]
 i,j=rng.choice(pool)
 ft=ht=0
 for k in bits(i): ft^=ims[k]
 for k in bits(j): ht^=ims[k]
 # Independent constants preserve the degree condition and quadratic conclusion.
 if rng.randrange(2): ft^=FULL
 if rng.randrange(2): ht^=FULL
 f,h=transform(ft),transform(ht); g=transform(ft&ht)
 assert degree(g)<=2
 w,e=f&DEG[2],h&DEG[2]; r=g&DEG[2]
 sp=span(basis([w,e])); rs=[v for v in sp if ranks[v]==2]
 assert any(r==p or (ranks[r^p]==2 and any(ss[r^p]&ss[t] for t in rs)) for p in sp)
 if not w or not e or w==e: counts['P1']+=1
 elif sum(ranks[q]==2 for q in [w,e,w^e])>=2: counts['P2']+=1
 else:
  counts['P3']+=1; assert contains(g,[1,f,h])
 for a,b in [(w,e),(e,w)]:
  if ranks[b]>=4:
   ordered_radicals+=1
   assert all(not contraction(a,d) for d in bits(rad[b]))
 if trial and trial%250000==0: print('conditioned pairs',trial,flush=True)
# Planted violation: the same conclusion detector rejects a rank-six output with Q=<P0>.
r=Q2; sp=[0,P0]; rs=[P0]
assert not any(r==p or (ranks[r^p]==2 and any(ss[r^p]&ss[t] for t in rs)) for p in sp)
# Degenerate, rank-zero and rank-two quadratics: exact nonrandom controls.
for f,h in [(0,0),(P0,1),(P0,P0),(Z1,1^Z1),(1,1)]:
 assert degree(mul(f,h))<=2
save('conditioned_products',{'status':'pass','random_pairs_satisfying_hypotheses':checked,'seed':611271,'pool_factor_planes':len(pool),'branch_counts':counts,'ordered_radical_implications_tested':ordered_radicals,'positive_controls_detected':True,'limitation':'random embeddings of four-coordinate quadratic pairs, not all six-variable pairs'},start)
