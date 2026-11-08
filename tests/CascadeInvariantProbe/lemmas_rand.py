import random
from fractions import Fraction as Fr
from inv import *
def check(g,p,bad):
    ul=[1<<(bl(x)-p) for x in g]; Q=g[0]; Qs=[Q]; hs=[0]
    for k in range(1,len(g)):
        Q,h=twosum(g[k],Q,p); Qs.append(Q); hs.append(h)
        if abs(h)>ul[k]: bad['LA']=bad.get('LA',0)+1
    for k in range(2,len(g)):
        U=ul[k]; w=ul[k-1]; b=Qs[k-2]; rho=Qs[k-1]-g[k-1]
        if abs(b)>2*U: bad['B']=bad.get('B',0)+1
        if abs(rho)>2*U: bad['T']=bad.get('T',0)+1
        if 4*w<=U and not 4*abs(rho)<7*U: bad['c1']=bad.get('c1',0)+1
        if 2*w==U and not abs(b)<2*U: bad['c2']=bad.get('c2',0)+1
for p,gm,sp in [(4,1,6),(5,1,8),(6,1,8),(8,1,10)]:
    rng=random.Random(p); bad={}
    for _ in range(60000):
        e=chain(p,0,rng.randrange(1,8),rng,gm); f=chain(p,-rng.randrange(0,sp),rng.randrange(1,8),rng,gm)
        check(sorted(e+f,key=abs),p,bad)
    print('p',p,'violations',bad or 'none',flush=True)
