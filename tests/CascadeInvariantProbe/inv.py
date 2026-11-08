import random, sys, itertools
S=80  # scale: value = int * 2^-S ; exponents e => int<<(e+S)
def bl(x): return abs(x).bit_length()
def tz(x): x=abs(x); return (x&-x).bit_length()-1
def rn(v,p):
    if v==0: return 0
    s=-1 if v<0 else 1; a=abs(v); n=a.bit_length()
    if n<=p: return v
    sh=n-p; q=a>>sh; r=a-(q<<sh); half=1<<(sh-1)
    if r>half or (r==half and (q&1)): q+=1
    return s*(q<<sh)
def twosum(g,Q,p):
    Qn=rn(g+Q,p); return Qn,(g+Q-Qn)
def chain(p,top,L,rng,gapmax=6):
    out=[];e=top
    for i in range(L):
        m=rng.randrange(1<<(p-1),1<<p); sg=rng.choice((1,-1))
        out.append(sg*(m<<(e+S)))
        e-=p+rng.randrange(0,gapmax)
    return out
def blocks(E):
    E=[x for x in E if x!=0]; bs=[];i=0
    while i<len(E):
        if i+1<len(E) and E[i+1]==-E[i]: bs.append(('A',E[i]));i+=2
        elif i+1<len(E) and E[i+1]==E[i]: bs.append(('T',E[i]));i+=2
        else: bs.append(('S',E[i]));i+=1
    return bs
def key(b): return 2*abs(b[1]) if b[0]=='T' else abs(b[1])
def red(b): return [b[1]] if b[0]=='S' else ([2*b[1]] if b[0]=='T' else [])
def nonov(x,y):
    return abs(y)<(1<<tz(x)) or abs(x)<(1<<tz(y))
def p2(x): a=abs(x); return a&(a-1)==0
def mult(x,c): return x==0 or tz(x)>=c+S
def check(g,p):
    # g sorted ascending
    Q=g[0];E=[];res=[]
    for k in range(len(g)):
        if k>0:
            Q,h=twosum(g[k],Q,p); E=[h]+E
        bs=blocks(E)
        f={}
        f['A']=all(key(bs[i+1])<key(bs[i]) for i in range(len(bs)-1))
        r=[x for b in bs for x in red(b)]
        f['B']=all(nonov(r[i],r[i+1]) for i in range(len(r)-1))
        ok=True
        for i,b in enumerate(bs):
            if b[0]!='S' and not p2(b[1]): ok=False
            if b[0]=='A' and i>0:
                last=bs[i-1]; l=-last[1] if last[0]=='A' else last[1]
                c=abs(b[1]).bit_length()-1
                if not (l==0 or tz(l)>=c): ok=False
        f['C']=ok
        mk=max([key(b) for b in bs],default=0)
        f['D']=(Q==0) or mk<(1<<tz(Q))
        # alignment with Q on top: anti directly after Q
        if bs and bs[0][0]=='A' and Q!=0:
            c=abs(bs[0][1]).bit_length()-1; f['C']=f['C'] and tz(Q)>=c
        if k+1<len(g):
            ul=1<<(bl(g[k+1])-p); f['E']=mk<ul
            f['E1']=mk<=ul
        res.append(f)
    return res
def main(p,L,N,seed):
    rng=random.Random(seed); fails={}; first={}
    for it in range(N):
        e=chain(p,0,rng.randrange(1,L+1),rng)
        f=chain(p,-rng.randrange(0,3*p),rng.randrange(1,L+1),rng)
        g=sorted(e+f,key=abs)   # stable ascending
        for k,f_ in enumerate(check(g,p)):
            for c,v in f_.items():
                if not v:
                    fails[(c,k)]=fails.get((c,k),0)+1
                    first.setdefault((c,k),(e,f,g))
    print('p',p,'L',L,'N',N,'fails',dict(sorted(fails.items())))
    return first
if __name__=='__main__':
    p=int(sys.argv[1]);L=int(sys.argv[2]);N=int(sys.argv[3])
    first=main(p,L,N,1)
    for key_,(e,f,g) in sorted(first.items()):
        if key_[0] in('E','A','B','C','D'):
            sc=lambda v:[ (1 if x>0 else -1)*(abs(x)/2**S) for x in v]
            print(key_,'e=',sc(e),'f=',sc(f)); break
