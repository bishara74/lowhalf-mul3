"""All 2016 first nonlinear planes, exact cubic normal form and degree test."""
from core import *

def main():
    t=time.time();V=v_basis((P0,));seen=set();high=0;low=0
    for f,h,p in gate_products((P0,)):
        F,H=f,h
        if F&DEG[2] and H&DEG[2]:H^=F
        if not F&DEG[2]:F,H=H,F
        assert F&DEG[2]==P0 and not H&DEG[2]
        A=F^P0;B=H
        assert not(A&~DEG[1]) and not(B&~DEG[1])
        b=sum(((B>>(1<<i))&1)<<i for i in range(6))
        a=sum(((A>>(1<<i))&1)<<i for i in range(6))
        aa=min(a,a^b)
        seen.add((b,aa))
        assert reduce(p^mul(P0^linear(aa),B),V)==0
        iscubic=bool(b & ~(1|8))
        assert (degree(p)==3)==iscubic
        high+=iscubic;low+=not iscubic
    assert len(seen)==2016 and high==1920 and low==96
    assert degree(mul(P0,X[1]))==3 and degree(mul(P0,X[0]))<3
    record('lambda1_cubic_normal_form',{'status':'PASS','planes':2016,
      'cubic_planes':high,'quadratic_or_zero_planes':low,
      'positive_controls_detected':1,'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
