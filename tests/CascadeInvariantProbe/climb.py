import random, sys
from fractions import Fraction as Fr
from inv import *
def build(p,spec):
    # spec: (offset, [(sign,mant,gap)...]) per chain ; first element exponent = offset
    out=[]
    for off,els in spec:
        e=off
        for i,(sg,m,gp) in enumerate(els):
            if i>0: e-=p+gp
            out.append(sg*(m<<(e+S)))
    return out
def score(p,spec):
    g=sorted(build(p,spec),key=abs); Q=g[0]; Qs=[Q]
    for k in range(1,len(g)):
        Q,h=twosum(g[k],Q,p); Qs.append(Q)
    best=Fr(0)
    for k in range(2,len(g)):
        u=1<<(bl(g[k])-p)
        best=max(best,Fr(abs(Qs[k-1]-g[k-1]),u))
    return best
def rnd(p,rng,L):
    def ch(off):
        return (off,[(rng.choice((1,-1)),rng.randrange(1<<(p-1),1<<p),rng.randrange(0,3)) for _ in range(rng.randrange(1,L+1))])
    return [ch(0),ch(-rng.randrange(0,2*p))]
def mutate(p,spec,rng,L):
    s=[(o,list(e)) for o,e in spec]; c=rng.randrange(2); o,e=s[c]
    t=rng.randrange(5)
    if t==0 and c==1: o=o+rng.choice((-1,1))
    elif t==1 and e: i=rng.randrange(len(e)); e[i]=(-e[i][0],e[i][1],e[i][2])
    elif t==2 and e:
        i=rng.randrange(len(e)); m=e[i][1]+rng.choice((-1,1)); m=min(max(m,1<<(p-1)),(1<<p)-1); e[i]=(e[i][0],m,e[i][2])
    elif t==3 and e:
        i=rng.randrange(len(e)); gp=max(0,e[i][2]+rng.choice((-1,1))); e[i]=(e[i][0],e[i][1],gp)
    elif t==4:
        if len(e)<L and rng.random()<.5: e.append((rng.choice((1,-1)),rng.randrange(1<<(p-1),1<<p),rng.randrange(0,2)))
        elif len(e)>1: e.pop(rng.randrange(len(e)))
    s[c]=(o,e); return s
def climb(p,L,iters,seed):
    rng=random.Random(seed); best=Fr(0); bs=None
    for r in range(iters//400):
        cur=rnd(p,rng,L); cs=score(p,cur)
        for _ in range(400):
            n=mutate(p,cur,rng,L); ns=score(p,n)
            if ns>=cs: cur,cs=n,ns
        if cs>best: best,bs=cs,cur
    print('p',p,'L',L,'best rho/u',float(best),flush=True)
    return best,bs
for p in (3,4,5,7):
    b,s=climb(p,6,60000,p)
    if b>2: print('VIOLATION',s)
