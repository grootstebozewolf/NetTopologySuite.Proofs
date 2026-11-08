import sys
from fractions import Fraction as Fr
from inv import *
from eq import chains
def lowbit(x): return (x & -x) if x else None
def check(g,p):
    Q=g[0]; Qs=[Q]; hs=[0]
    for k in range(1,len(g)):
        Q,h=twosum(g[k],Q,p); Qs.append(Q); hs.append(h)
    fails=[]
    for k in range(2,len(g)):
        U=1<<(bl(g[k])-p); rho=Qs[k-1]-g[k-1]; H=sum(hs[1:k])
        lb=lowbit(abs(rho))
        dA=U if lb is None else min(U,lb)
        dB=2*U if lb is None else min(2*U,lb)
        if not abs(H)<dB: fails.append(('B',k,U,rho,H,Qs,hs))
        elif not abs(H)<dA: fails.append(('A',k,U,rho,H,Qs,hs))
    return fails
def run(p,L,klo,maxtot):
    C=chains(p,0,L,klo); n=0; cnt={'A':0,'B':0}; ex={}
    for e in C:
        for ftop in range(klo,1):
            for f in chains(p,ftop,L,klo):
                if len(e)+len(f)>maxtot: continue
                g=sorted(e+f,key=abs); n+=1
                for fl in check(g,p):
                    cnt[fl[0]]+=1
                    key=fl[0]
                    if key not in ex or len(g)<len(ex[key][1]): ex[key]=(fl,g,e,f)
    print('p',p,'pairs',n,'fail only d|U (A):',cnt['A'],' fail even d|2U (B):',cnt['B'],flush=True)
    for key,(fl,g,e,f) in ex.items():
        sc=lambda v:[str(Fr(x,2**S)) for x in v]
        _,k,U,rho,H,Qs,hs=fl
        print(' ',key,'e',sc(e),'f',sc(f),'k',k,'U',Fr(U,2**S),'rho',Fr(rho,2**S),'H',Fr(H,2**S))
        print('    g',sc(g),'Q',sc(Qs),'h',sc(hs))
p,L,klo,mt=map(int,sys.argv[1:5]); run(p,L,klo,mt)
