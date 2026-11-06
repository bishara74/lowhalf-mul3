"""First-gate function-space orbits, retaining multiplicities of factor planes."""
from core import *
from collections import Counter

def states():
    V=v_basis((P0,)); out=Counter()
    for f,h,p in gate_products((P0,)):
        out[reduce(p,V)]+=1
    return out

def orbits(high_only=True):
    allstates=states()
    remaining={g for g in allstates if not high_only or g&HIGH2}
    V=v_basis((P0,)); out=[]
    while remaining:
        rep=min(remaining)
        orbit={reduce(substitute(rep,G),V) for G in GROUP}
        assert orbit<=remaining
        out.append((rep,sum(allstates[g] for g in orbit),len(orbit)))
        remaining-=orbit
    return out
if __name__=='__main__':
    st=states(); o=orbits()
    print('all cosets',len(st),'high orbits',len(o),'weight',sum(w for g,w,z in o))
