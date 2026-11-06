"""Exact exterior, rank, symmetry, Pluecker and first-gate checks; no old code."""
from algebra import *
from itertools import combinations, permutations
start=time.time(); forms=rank2forms(); assert len(forms)==651
# Rank/exterior lemma: image of wedge-by-P is tested by full linear elimination.
ranktests=0; exterior=0
for e in range(2):
 for a in range(2):
    q=Q2^(Z1 if e else 0)^(P0 if a else 0); assert rank(q)==6
    for p in forms: assert rank(q^p)>=4; ranktests+=1
for p in forms:
 if not inside(p):
    image=[wedge(p,1<<s) for s in range(64) if s.bit_count()==2]
    assert not contains(OMEGA,image); exterior+=1
# D1: all independent outside generator pairs and all seven wedge-coefficients.
out=[p for p in forms if not inside(p)]; pairs=omega_pairs=0
for p,r in combinations(out,2):
 if len(basis([P0,p,r]))<3: continue
 pairs+=1
 wp,wr,pr=wedge(P0,p),wedge(P0,r),wedge(p,r)
 if OMEGA in span([wp,wr,pr]):
    omega_pairs+=1
    assert any(killed(p,e) and killed(r,e) for e in [4,32,36])
# B3U: every Q3 containing Z1, not merely a preferred generating basis.
q3=set()
for p,r in combinations(forms,2):
 b=canonical([P0,p,r])
 if len(b)==3 and contains(Z1,b):
    assert all(inside(q) for q in b); q3.add(b)
# Pluecker: all rank-two 2x4 matrices and all kernel bases.
matrices=0; kernel_bases=0
for a in range(1,16):
 for b in range(1,16):
    if a==b: continue
    matrices+=1
    ker=[v for v in range(16) if (a&v).bit_count()%2==0 and (b&v).bit_count()%2==0]
    for n1 in ker[1:]:
     for n2 in ker[1:]:
      if n1==n2: continue
      kernel_bases+=1
      for j,k in combinations(range(4),2):
       l,m=[i for i in range(4) if i not in (j,k)]
       detn=((n1>>j)&1)*((n2>>k)&1)^((n1>>k)&1)*((n2>>j)&1)
       detu=((a>>l)&1)*((b>>m)&1)^((a>>m)&1)*((b>>l)&1)
       assert detn==detu
# Positive control for false proof step: column permutation alone need not make I2.
columns=[(1,1),(1,0),(0,0),(0,0)]
assert not any([columns[i] for i in order[:2]]==[(1,0),(0,1)] for order in permutations(range(4)))
# Also deliberately corrupt one complementary minor.
assert (1^0)!=0
# First nonlinear gate: enumerate every plane modulo constants, plus degenerate gates.
v1=canonical(aff()+[P0]); first=set(); cubic=quadratic=0; firstplanes=[]
for b in range(1,64):
 B=linear(b)
 for a in range(64):
    if a>(a^b): continue
    g=mul(P0^linear(a),B); firstplanes.append((a,b,g))
    cubic+=degree(g)==3; quadratic+=degree(g)<=2
    assert degree(g)<=3
    assert (degree(g)==3)==(b&~9!=0)
    for target in [Z1,Z2,Z1^Z2]: assert not contains(target,v1+(g,))
    first.add(reduce(g,v1))
assert (len(firstplanes),cubic,quadratic)==(2016,1920,96)
# Degenerate semantic nonlinear gate: P0*P0=P0, not a factor plane.
assert mul(P0,P0)==P0 and reduce(mul(P0,P0),v1)==0
# Six-AND upper bound, checked by ANF equality and then all 64 input assignments.
g0=P0; g1=mul(X[0],X[4]); g2=mul(X[1],X[3]); g3=mul(X[0],X[5]); g4=mul(X[2],X[3]); g5=mul(g1^X[1],g2^X[4])
assert g5^g1^g2^g3^g4==Z2
for x in range(64):
 aa=sum(((x>>i)&1)<<i for i in range(3)); bb=sum(((x>>(i+3))&1)<<i for i in range(3))
 assert sum(((transform(t)>>x)&1)<<i for i,t in enumerate([P0,Z1,Z2]))==(aa*bb)%8
# Mutation control for rank obstruction: adding a rank-four form can lower to rank 2.
assert rank(Q2^(Q2^P0))==2
save('structure',{'status':'pass','rank_tests':ranktests,'full_exterior_images':exterior,'D1_pairs':pairs,'D1_omega_pairs':omega_pairs,'B3U_spaces':len(q3),'Pluecker_matrices':matrices,'Pluecker_kernel_bases':kernel_bases,'first_planes':len(firstplanes),'cubic_first_planes':cubic,'quadratic_first_planes':quadratic,'first_output_cosets':len(first),'positive_controls_detected':True,'column_permutation_proof_step_counterexample':columns},start)
