import itertools, sys
from inv import *
def chains(p,top,L,klo):
    # all priest chains: top exponent fixed, lengths 1..L, exponents >= klo
    res=[]
    def rec(cur,e,left):
        if cur: res.append(list(cur))
        if left==0: return
        for ne in range(klo, e-p+1):
            for m in range(1<<(p-1),1<<p):
                for sg in (1,-1):
                    cur.append(sg*(m<<(ne+S))); rec(cur,ne,left-1); cur.pop()
    for m in range(1<<(p-1),1<<p):
        for sg in (1,-1):
            rec([sg*(m<<(top+S))],top,L-1)
    return res
def find(p,L,klo,maxtot):
    best=None
    C=chains(p,0,L,klo)
    out=[]
    for e in C:
        for ftop in range(klo+p*0, 1):
            for f in chains(p,ftop,L,klo-0):
                if len(e)+len(f)>maxtot: continue
                g=sorted(e+f,key=abs)
                Q=g[0]
                for k in range(1,len(g)-1):
                    Q,h=twosum(g[k],Q,p)
                    if h!=0 and abs(h)==1<<(bl(g[k+1])-p):
                        out.append((len(e)+len(f),e,f,k)); break
    out.sort(key=lambda t:t[0]); return out
if __name__=='__main__':
    p=int(sys.argv[1]);L=int(sys.argv[2]);klo=int(sys.argv[3]);mt=int(sys.argv[4])
    r=find(p,L,klo,mt)
    print('p',p,'count',len(r))
    sc=lambda v:[(1 if x>0 else -1)*abs(x)/2**S for x in v]
    for t in r[:4]: print(t[0],sc(t[1]),sc(t[2]),'k',t[3])
