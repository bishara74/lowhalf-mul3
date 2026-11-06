"""Exact algebraic placement screens, with 64-bit truth tables internally."""
from core import *

def tt_basis(Q): return tuple(mob(f) for f in AFF+tuple(Q))

def eligible_data(Q,target=Z1):
    V=tt_basis(Q); B=basis(V); z=mob(target)
    # Factors k include constants. k=0,1 cannot add a missing target.
    vals=elements(V)
    out=[]
    for ki,k in enumerate(vals):
        if k in (0,FULL): continue
        # Any quadratic target R=k*(g+F) must satisfy (1+k)R=0.
        c=k^FULL
        SB=basis(c&v for v in V)
        if reduce(c&z,SB): continue
        S=basis(V+tuple(k&v for v in V))
        out.append((ki,k,S))
    return out

