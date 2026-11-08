import sys
from fractions import Fraction as Fr
from inv import *
from eq import chains
# checks every intermediate claim of the paper proof:
#  LA'(j): |h_j| <= ulp(g_j)                     (stronger than ulp(g_{j+1}))
#  B(k):   |Q_{k-2}| <= 2 ulp(g_k)
#  S(k):   |S_{k-2}| < 2 ulp(g_k)
#  Hsum:   |H_{k-2}| <= sum_{j<=k-2} ulp(g_j) < 2U/(2^p-1)
#  case w<=U/4: |rho| < 7U/4 ; case w=U/2: |rho| <= 2U and |b| < 2U ; case w=U: |rho|<=2U
def run(p,L,klo,maxtot):
    C=chains(p,0,L,klo); n=0; bad={}
    def flag(k,info):
        bad[k]=bad.get(k,0)+1
        if bad[k]==1: print('  VIOLATION',k,info,flush=True)
    for e in C:
        for ftop in range(klo,1):
            for f in chains(p,ftop,L,klo):
                if len(e)+len(f)>maxtot: continue
                g=sorted(e+f,key=abs); n+=1
                ul=[1<<(bl(x)-p) for x in g]
                Q=g[0]; Qs=[Q]; hs=[0]
                for k in range(1,len(g)):
                    Q,h=twosum(g[k],Q,p); Qs.append(Q); hs.append(h)
                    if abs(h)>ul[k]: flag('LA',(e,f,k))
                for k in range(2,len(g)):
                    U=ul[k]; w=ul[k-1]; b=Qs[k-2]; rho=Qs[k-1]-g[k-1]
                    if abs(b)>2*U: flag('B',(e,f,k))
                    if not abs(sum(g[:k-1]))<2*U: flag('S',(e,f,k))
                    Hs=sum(abs(x) for x in hs[1:k-1]); us=sum(ul[1:k-1])
                    if Hs>us or not Fr(us)<Fr(2*U,(1<<p)-1) and k>2: flag('Hsum',(e,f,k))
                    if 4*w<=U and not 4*abs(rho)<7*U: flag('c1',(e,f,k))
                    if 2*w==U and (abs(rho)>2*U or not abs(b)<2*U): flag('c2',(e,f,k))
                    if w==U and abs(rho)>2*U: flag('c3',(e,f,k))
    print('p',p,'pairs',n,'violations',bad if bad else 'none',flush=True)
p,L,klo,mt=map(int,sys.argv[1:5]); run(p,L,klo,mt)
