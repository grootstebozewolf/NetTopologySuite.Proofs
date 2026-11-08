import random
from inv import *
from fractions import Fraction as Fr
def go(p,L,N,gm,sp,seed):
    rng=random.Random(seed); mt=0; best=None
    for _ in range(N):
        e=chain(p,0,rng.randrange(1,L+1),rng,gm); f=chain(p,-rng.randrange(0,sp),rng.randrange(1,L+1),rng,gm)
        g=sorted(e+f,key=abs); Q=g[0]
        for k in range(1,len(g)):
            t=Fr(abs(Q-g[k-1]),1<<(bl(g[k])-p))   # Q = Q_{k-1}
            if t>mt: mt=t; best=(e,f,k)
            Q,h=twosum(g[k],Q,p)
    print('p',p,'max |Q_{k-1}-g_{k-1}|/ulp(g_k) =',float(mt),flush=True)
for p,gm,sp in [(2,2,5),(3,2,6),(4,1,8),(5,1,8)]:
    go(p,7,120000,gm,sp,3)
