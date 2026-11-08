import random
from fractions import Fraction as Fr
from inv import *
def go(p,L,N,gm,sp,seed,show=4):
    rng=random.Random(seed); mx=Fr(0); ex=[]; stats={'Q2':Fr(0),'h':Fr(0),'S':Fr(0)}
    for _ in range(N):
        e=chain(p,0,rng.randrange(1,L+1),rng,gm); f=chain(p,-rng.randrange(0,sp),rng.randrange(1,L+1),rng,gm)
        g=sorted(e+f,key=abs); Q=g[0]; Qs=[Q]; hs=[0]
        for k in range(1,len(g)):
            Q,h=twosum(g[k],Q,p); Qs.append(Q); hs.append(h)
        for k in range(2,len(g)):
            u=1<<(bl(g[k])-p)
            rho=Qs[k-1]-g[k-1]
            SS=sum(g[:k-1])
            stats['Q2']=max(stats['Q2'],Fr(abs(Qs[k-2]),u)); stats['h']=max(stats['h'],Fr(abs(hs[k-1]),u)); stats['S']=max(stats['S'],Fr(abs(SS),u))
            r=Fr(abs(rho),u)
            if r>=2 and len(ex)<show: ex.append((k,[float(Fr(x,2**S)) for x in g],[float(Fr(x,2**S)) for x in Qs],[float(Fr(x,2**S)) for x in hs],float(r)))
            mx=max(mx,r)
    print('p',p,'max rho/u',float(mx),{k:float(v) for k,v in stats.items()})
    for k,g,Qs,hs,r in ex[:show]: print(' k',k,'r',r,'\n  g',g,'\n  Q',Qs,'\n  h',hs)
go(2,6,60000,2,5,3,3); go(3,6,60000,2,6,3,2)
