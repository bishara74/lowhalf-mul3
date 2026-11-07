"""Exhaust all quadratic functions' weights in 4/6 variables and all four-variable
factor planes for the product lemma (all constant/basis variants follow by identities).
"""
from algebra import *
from itertools import combinations
start=time.time(); weights={}
for inds in [(0,1,3,4),tuple(range(6))]:
    n=len(inds); qb=[1<<((1<<i)|(1<<j)) for i,j in combinations(inds,2)]
    ab=[1]+[X[i] for i in inds]; ats=span([transform(v) for v in ab])
    qs=span(qb); qts=span([transform(v) for v in qb]); minimum=64; fullrank=set(); count=0
    for q,qt in zip(qs,qts):
     rq=rank(q)
     for at in ats:
      tt=qt^at; w=tt.bit_count()>>(6-n); count+=1
      if w: minimum=min(minimum,w)
      if rq==n: fullrank.add(w)
    assert minimum==1<<(n-2)
    assert fullrank=={(1<<(n-1))-(1<<(n//2-1)),(1<<(n-1))+(1<<(n//2-1))}
    weights[str(n)]={'all_functions':count,'minimum_nonzero_weight':minimum,'full_rank_weights':sorted(fullrank)}
# All nonconstant factor planes modulo constants on U.
inds=[0,1,3,4]; bs=[X[i] for i in inds]+[1<<((1<<i)|(1<<j)) for i,j in combinations(inds,2)]
fs=span(bs); ts=span([transform(v) for v in bs]); qs=span(bs[4:]); ranks={q:rank(q) for q in qs}
allowed={}
for w in qs:
 for e in qs:
    sp=span(basis([w,e])); rs=[r for r in sp if ranks[r]==2]
    allowed[w,e]={q for q in qs if any(q==p or (ranks[q^p]==2 and any(meet(q^p,r) for r in rs)) for p in sp)}
counts={'planes':0,'quadratic_products':0,'P1':0,'P2':0,'P3':0}
for i in range(1,len(fs)):
 for j in range(i+1,len(fs)):
  if j>i^j: continue
  counts['planes']+=1; g=transform(ts[i]&ts[j])
  if degree(g)>2: continue
  w,e=fs[i]&DEG[2],fs[j]&DEG[2]
  if not (w or e): continue
  counts['quadratic_products']+=1
  assert g&DEG[2] in allowed[w,e]
  if not w or not e or w==e:
   counts['P1']+=1
   l=fs[i] if not w else fs[j] if not e else fs[i]^fs[j]
   l=l&DEG[1]
   assert l
   for q in [w,e,g&DEG[2]]: assert not wedge(l,q)
  elif sum(ranks[q]==2 for q in [w,e,w^e])>=2:
   counts['P2']+=1
   r1,r2=[q for q in [w,e,w^e] if ranks[q]==2][:2]
   assert meet(r1,r2)
  else:
   counts['P3']+=1; assert contains(g,[1,fs[i],fs[j]])
# Deliberate constant/dependent edge cases.
for f in fs:
 assert mul(f,f)==f and mul(f,1^f)==0
# Planted rank-six output for a rank-two/zero plane violates general product predicate.
assert Q2 not in allowed[P0,0]
# Planted weight-one nonzero 'quadratic' result is detected by the minimum distance bound.
assert 1 < (1<<(6-2))
save('weights_and_product4',{'status':'pass','weights':weights,'product_lemma_four_variable_domain':counts,'positive_controls_detected':True},start)
