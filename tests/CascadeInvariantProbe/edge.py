import sys, itertools
from inv import *
def chains(p,L,gaps):
    ms=sorted({1<<(p-1),(1<<(p-1))+1,(1<<p)-2,(1<<p)-1})
    out=[]
    def rec(cur,e,left):
        out.append(list(cur))
        if left==0: return
        for gp in gaps:
            for m in ms:
                for sg in (1,-1):
                    cur.append((sg*m,e-p-gp)); rec(cur,e-p-gp,left-1); cur.pop()
    for m in ms:
        for sg in (1,-1): rec([(sg*m,0)],0,L-1)
    return out
def val(ch,off): return [m<<(e+off+S) for m,e in ch]
def go(p,L,gaps,offs):
    C=chains(p,L,gaps); mx=0; viol=[]; n=0
    for e in C:
        for off in offs:
            for f in C:
                ev=val(e,0); fv=val(f,off)
                g=sorted(ev+fv,key=abs); Q=g[0]; n+=1
                for k in range(1,len(g)-1):
                    Q,h=twosum(g[k],Q,p); r=abs(h)/(1<<(bl(g[k+1])-p))
                    if r>mx: mx=r
                    if r>1: viol.append((ev,fv,k,r))
    print('p',p,'L',L,'pairs',n,'max ratio',mx,'viol',len(viol),flush=True)
    sc=lambda v:[(1 if x>0 else -1)*abs(x)/2**S for x in v]
    for ev,fv,k,r in viol[:3]: print(sc(ev),sc(fv),k,r)
for p in (3,4,5,6):
    go(p,3,(0,1),range(-p,1))
