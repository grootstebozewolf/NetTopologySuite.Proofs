import sys
from fractions import Fraction as Fr
from inv import *
from eq import chains
def lowbit(x): return (x & -x) if x else None
def steps(g,p):
    Q=g[0]; Qs=[Q]; hs=[0]
    for k in range(1,len(g)):
        Q,h=twosum(g[k],Q,p); Qs.append(Q); hs.append(h)
    for k in range(2,len(g)):
        U=1<<(bl(g[k])-p); rho=Qs[k-1]-g[k-1]; H=sum(hs[1:k])
        lb=lowbit(abs(rho)); dB=2*U if lb is None else min(2*U,lb)
        yield k,U,rho,H,abs(H)<dB,Qs,hs
def run(p,L,klo,maxtot,show=3):
    C=chains(p,0,L,klo); best=[]; mx=Fr(0)
    for e in C:
        for ftop in range(klo,1):
            for f in chains(p,ftop,L,klo):
                if len(e)+len(f)>maxtot: continue
                g=sorted(e+f,key=abs)
                for k,U,rho,H,ok,Qs,hs in steps(g,p):
                    if ok: continue
                    r=Fr(abs(rho),U)
                    if r>mx: mx=r; best=[]
                    if r==mx and len(best)<show: best.append((e,f,g,k,U,rho,H,Qs,hs))
    print('p',p,'max fail ratio',mx)
    sc=lambda v:[str(Fr(x,2**S)) for x in v]
    for e,f,g,k,U,rho,H,Qs,hs in best:
        print(' e',sc(e),'f',sc(f),'k',k,'U',Fr(U,2**S),'rho',Fr(rho,2**S),'H',Fr(H,2**S))
        print('   g',sc(g),'\n   Q',sc(Qs),'\n   h',sc(hs))
p,L,klo,mt=map(int,sys.argv[1:5]); run(p,L,klo,mt)
