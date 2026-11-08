import random, sys
from inv import *
def shape_ok(bs,Q):
    A=all(key(bs[i+1])<key(bs[i]) for i in range(len(bs)-1))
    r=[x for b in bs for x in red(b)]
    B=all(nonov(r[i],r[i+1]) for i in range(len(r)-1))
    C=True
    for i,b in enumerate(bs):
        if b[0]!='S' and not p2(b[1]): C=False
        if b[0]=='A':
            c=abs(b[1]).bit_length()-1
            if i>0:
                last=bs[i-1]; l=-last[1] if last[0]=='A' else last[1]
                if not(l==0 or tz(l)>=c): C=False
            elif Q is not None and Q!=0 and tz(Q)<c: C=False
    return A and B and C
def classify(g,p):
    Q=g[0];E=[];out=[];n=len(g)
    for k in range(n):
        if k>0:
            Q,h=twosum(g[k],Q,p); E=[h]+E
        ul=(1<<(bl(g[k+1])-p)) if k+1<n else None
        Ez=[x for x in E if x!=0]
        if len(E)>=2 and E[0]==0 and Q!=0 and Q==E[1]:
            bs0=blocks(E[2:]); h=abs(Q); mk=max([key(b) for b in bs0],default=0)
            ok=p2(Q) and shape_ok(bs0,None) and mk<h and (ul is None or 4*h<=ul)
            out.append('P' if ok else 'P!')
            continue
        bs=blocks(E); mk=max([key(b) for b in bs],default=0)
        base=shape_ok(bs,Q) and (Q==0 or mk<(1<<tz(Q)))
        if not base: out.append('X'); continue
        if ul is None or mk<ul: out.append('N')
        elif mk==ul: out.append('T')
        else: out.append('Y')   # keys exceed ulp(g_next): invariant would fail
    return out
def run(p,L,N,seed,gapmax,span):
    rng=random.Random(seed); from collections import Counter
    c=Counter(); ex={}
    for it in range(N):
        e=chain(p,0,rng.randrange(1,L+1),rng,gapmax)
        f=chain(p,-rng.randrange(0,span),rng.randrange(1,L+1),rng,gapmax)
        g=sorted(e+f,key=abs)
        cl=classify(g,p)
        for k,s in enumerate(cl):
            c[s]+=1
            if s in('X','Y','P!'): ex.setdefault(s,(k,g,cl))
    print('p',p,'L',L,'N',N,dict(c))
    for s,(k,g,cl) in ex.items(): print(' first',s,'k=',k,cl,[ (1 if x>0 else -1)*abs(x)/2**S for x in g])
for p,L,N,gm,sp in [(2,6,400000,2,6),(2,8,300000,1,5),(3,7,300000,2,8),(3,8,300000,1,8),(4,6,200000,1,8),(5,6,100000,1,10)]:
    run(p,L,N,7,gm,sp)
