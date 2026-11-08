import sys
from fractions import Fraction as Fr
from inv import *
from eq import chains
def lowbit(x): return (x & -x) if x else None
def run(p,L,klo,maxtot):
    C=chains(p,0,L,klo); n=0; nf=0; mxf=Fr(0); mxok=Fr(0)
    for e in C:
        for ftop in range(klo,1):
            for f in chains(p,ftop,L,klo):
                if len(e)+len(f)>maxtot: continue
                g=sorted(e+f,key=abs); n+=1
                Q=g[0]; Qs=[Q]; hs=[0]
                for k in range(1,len(g)):
                    Q,h=twosum(g[k],Q,p); Qs.append(Q); hs.append(h)
                for k in range(2,len(g)):
                    U=1<<(bl(g[k])-p); rho=Qs[k-1]-g[k-1]; H=sum(hs[1:k])
                    lb=lowbit(abs(rho)); dB=2*U if lb is None else min(2*U,lb)
                    r=Fr(abs(rho),U)
                    if not abs(H)<dB: nf+=1; mxf=max(mxf,r)
                    else: mxok=max(mxok,r)
    print('p',p,'pairs',n,'lattice failures',nf,'max |rho|/U among failures',float(mxf),'| among successes',float(mxok),flush=True)
p,L,klo,mt=map(int,sys.argv[1:5]); run(p,L,klo,mt)
