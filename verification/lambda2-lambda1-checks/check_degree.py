"""Exact top-degree statements on all first nonlinear planes in use."""
from core import *
from collections import Counter

def main():
    t=time.time();n=0;quartic=0;cubic=0;dependent=0
    for Q,w in q2_orbits():
        vals=elements(X+Q);tts=[mob(v) for v in vals]
        for i,j in planes(len(X+Q),None):
            f,h,p=vals[i],vals[j],mob(tts[i]&tts[j])
            n+=1;assert not p&(DEG[5]|DEG[6])
            assert p&DEG[4]==mul(f&DEG[2],h&DEG[2])&DEG[4]
            if p&DEG[4]:
                quartic+=1
                assert len(Q)==2 and basis((f&DEG[2],h&DEG[2]))==basis(Q)
                assert p&DEG[4]==mul(Q[0],Q[1])&DEG[4]
        for f in elements(AFF+Q):
            for p in (mul(f,f),mul(f,f^1),mul(f,0),mul(f,1)):
                assert degree(p)<=2
                dependent+=1
        if len(Q)==1:
            for f,h,p in gate_products(Q):
                assert not p&DEG[4]
                cubic+=bool(p&DEG[3])
    # Planted false quartic top part must disagree with the exact product.
    f=P0^X[1];h=X[4]
    assert (mul(f,h)^OMEGA)&DEG[4] != mul(f&DEG[2],h&DEG[2])&DEG[4]
    record('degree_structure',{'status':'PASS','planes':n,'dependent_descriptions':dependent,'quartic_products':quartic,
       'lambda1_cubic_planes':cubic,'positive_controls_detected':1,'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
