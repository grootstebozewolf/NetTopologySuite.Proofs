import random, itertools
from fractions import Fraction as Fr
# independent exact model with Fractions
def rnE(v,p):
    v=Fr(v)
    if v==0: return v
    s=1 if v>0 else -1; a=abs(v); e=0
    while a>=2**(e+1): e+=1
    while a<2**e: e-=1
    ul=Fr(2)**(e-p+1); q=a/ul; n=q.numerator//q.denominator; r=q-n
    if r>Fr(1,2) or (r==Fr(1,2) and n%2==1): n+=1
    return s*n*ul
def ulpE(x):
    a=abs(Fr(x)); e=0
    while a>=2**(e+1): e+=1
    while a<2**e: e-=1
    return Fr(2)**(e-prec+1)
def ratio(p,es,fs):
    global prec; prec=p
    g=sorted(es+fs,key=abs); Q=g[0]; Qs=[Q]
    for k in range(1,len(g)): Q=rnE(g[k]+Q,p); Qs.append(Q)
    best=Fr(0); at=None
    for k in range(2,len(g)):
        r=abs(Qs[k-1]-g[k-1])/ulpE(g[k])
        if r>best: best,at=r,k
    return best,at,g,Qs
def chainv(p,gap,els):
    # els: (sign,mant,gap_extra); first exponent given as first tuple's extra
    out=[];e=0
    for i,(sg,m,gp) in enumerate(els):
        if i>0: e-=gap+gp
        out.append(sg*Fr(m)*Fr(2)**e)
    return out
p,gap=3,2
spec=([(1,5,1),(1,6,1),(1,7,0),(1,7,0)],-3,[(-1,7,0),(1,7,0),(1,7,0),(1,7,0),(-1,7,1)])
def val(spec):
    a,off,b=spec
    return chainv(p,gap,a),[x*Fr(2)**off for x in chainv(p,gap,b)]
cur=spec
def r(s): e,f=val(s); return ratio(p,e,f)[0]
print('start',float(r(cur)))
changed=True
while changed:
    changed=False
    a,off,b=cur
    for which in (0,1):
        lst=[a,b][which]
        for i in range(len(lst)):
            l2=lst[:i]+lst[i+1:]
            if not l2: continue
            n=(l2,off,b) if which==0 else (a,off,l2)
            if r(n)>2: cur=n; changed=True; break
        if changed: break
e,f=val(cur); best,at,g,Qs=ratio(p,e,f)
print('minimal: e=',[str(x) for x in e],'f=',[str(x) for x in f]); print('ratio',best,'at k',at)
print('sorted g',[str(x) for x in g]); print('Q',[str(x) for x in Qs])
# check inputs: exponent gaps vs p
