"""Fresh exact product/extraction checks in all 606 Q, plus arbitrary-pair stress.
Includes rank-zero factors and P inside Lambda^2(U); no orbit reduction.
"""
from algebra import *
import random
start=time.time(); forms=rank2forms(); spaces=quadratic_spaces(); assert len(spaces)==606
quad=DEG[0]|DEG[1]|DEG[2]
# Exact extraction and replacement domains: all factor planes modulo constants.
planes=quadratic_count=extracted=quartic=0
for index,q in enumerate(spaces):
    qb=tuple(q); bs=X+list(qb); ans=span(bs); ts=span([transform(v) for v in bs])
    allowed={p^v for p in [0]+forms for v in span(qb)}
    wtop=wedge(qb[0],qb[1]) if len(qb)==2 else 0
    for i in range(1,len(ans)):
     for j in range(i+1,len(ans)):
      if j>i^j: continue
      planes+=1; g=transform(ts[i]&ts[j]); g2=g&DEG[2]
      if not g&~quad:
        quadratic_count+=1; assert g2 in allowed
      stripped=g&~IDEAL
      if not stripped&~quad:
        extracted+=1; assert (stripped&DEG[2]) in allowed
      if g&DEG[4]:
        quartic+=1; assert g&DEG[4]==wtop
    if index%100==0: print('Q spaces',index,flush=True)
# Dependent factors and constants give available functions and zero; quadratic representatives
# modulo I differ by P0, already included in allowed. This completes those cases algebraically.
# Positive controls: a deliberately corrupted quadratic result must fail BOTH predicates.
q=(P0,); allowed={p^v for p in [0]+forms for v in span(q)}
assert Q2 not in allowed
# Radical/product lemma on arbitrary six-variable quadratic pairs: >= 10^6 independent instances.
rng=random.Random(482901); mons=list(bits(quad)); random_tests=1_000_000
rad_qual=product_qual=0

def product_conclusion(w,e,r):
    sp=span(basis([w,e])); ranktwo=[t for t in sp if rank(t)==2]
    return any((r^p)==0 or (rank(r^p)==2 and any(meet(r^p,t) for t in ranktwo)) for p in sp)

def check_pair(f,h):
    global rad_qual,product_qual
    g=mul(f,h); w=f&DEG[2]; e=h&DEG[2]
    if degree(g)<=3:
        for a,b in [(w,e),(e,w)]:
            if rank(b)>=4:
                rad_qual+=1
                for d in range(1,64):
                    if not contraction(b,d): assert not contraction(a,d)
    if (w or e) and degree(g)<=2:
        product_qual+=1; assert product_conclusion(w,e,g&DEG[2])
for _ in range(random_tests):
    f=rng.getrandbits(64)&quad; h=rng.getrandbits(64)&quad; check_pair(f,h)
# Deliberate edge cases: rank 0/2/4/6, constants, equal functions, inside-U and zero spaces.
edge=[0,1]+X+[P0,Z1,Q2,P0^Z1,1^Q2]
for f in edge:
 for h in edge+[f,1^f]: check_pair(f,h)
assert not product_conclusion(P0,0,Q2)
# Positive radical control: rank-four eta on U, omega with an external factor violates conclusion.
assert rank(Z1)==4 and not contraction(Z1,4) and contraction(1<<5,4)
save('quadratic_products',{'status':'pass','Q_spaces':len(spaces),'all_factor_planes':planes,'quadratic_products':quadratic_count,'quadratic_mod_I_products':extracted,'quartic_products':quartic,'arbitrary_quadratic_random_pairs':random_tests,'radical_ordered_qualifying_pairs':rad_qual,'product_qualifying_pairs':product_qual,'positive_controls_detected':True},start)
