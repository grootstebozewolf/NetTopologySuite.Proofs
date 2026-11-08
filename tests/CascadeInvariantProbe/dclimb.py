import random, sys
from fractions import Fraction as Fr
from inv import *
import climb
def lowbit(x): return (x & -x) if x else None
def fscore(p,spec):
    g=sorted(climb.build(p,spec),key=abs); Q=g[0]; Qs=[Q]; hs=[0]
    for k in range(1,len(g)):
        Q,h=twosum(g[k],Q,p); Qs.append(Q); hs.append(h)
    best=Fr(0)
    for k in range(2,len(g)):
        U=1<<(bl(g[k])-p); rho=Qs[k-1]-g[k-1]; H=sum(hs[1:k])
        lb=lowbit(abs(rho)); dB=2*U if lb is None else min(2*U,lb)
        if not abs(H)<dB: best=max(best,Fr(abs(rho),U))
    return best
def run(p,L,iters,seed):
    rng=random.Random(seed); best=Fr(0); bs=None
    for r in range(iters//400):
        cur=climb.rnd(p,rng,L); cs=fscore(p,cur)
        for _ in range(400):
            n=climb.mutate(p,cur,rng,L); ns=fscore(p,n)
            if ns>=cs: cur,cs=n,ns
        if cs>best: best,bs=cs,cur
    print('p',p,'max failure ratio found',best,float(best),flush=True)
    return best,bs
for p in map(int,sys.argv[1:]):
    b,s=run(p,6,48000,p)
    print('   spec',s)
