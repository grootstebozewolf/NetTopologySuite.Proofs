import sys
from inv import *
from eq import chains
def run(p,L,klo,maxtot):
    C=chains(p,0,L,klo); n=0; gt=[]; mx=0
    for e in C:
        for ftop in range(klo,1):
            for f in chains(p,ftop,L,klo):
                if len(e)+len(f)>maxtot: continue
                g=sorted(e+f,key=abs); Q=g[0]; n+=1
                for k in range(1,len(g)-1):
                    Q,h=twosum(g[k],Q,p)
                    u=1<<(bl(g[k+1])-p)
                    r=abs(h)/u
                    if r>mx: mx=r
                    if abs(h)>u: gt.append((e,f,k))
    print('p',p,'L',L,'klo',klo,'tot',maxtot,'pairs',n,'max|h|/ulp(next)',mx,'violations',len(gt))
    return gt
p,L,klo,mt=map(int,sys.argv[1:5]); gt=run(p,L,klo,mt)
sc=lambda v:[(1 if x>0 else -1)*abs(x)/2**S for x in v]
for e,f,k in gt[:3]: print(sc(e),sc(f),k)
