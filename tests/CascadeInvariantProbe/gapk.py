import random
from fractions import Fraction as Fr
from inv import *
import climb
def run(p,mingap,L,iters,seed):
    # climb with chains whose gap is p-1+gp... monkeypatch build to use mingap
    def build(p_,spec):
        out=[]
        for off,els in spec:
            e=off
            for i,(sg,m,gp) in enumerate(els):
                if i>0: e-=mingap+gp
                out.append(sg*(m<<(e+S)))
        return out
    climb.build=build
    rng=random.Random(seed); best=Fr(0); bs=None
    for r in range(iters//400):
        cur=climb.rnd(p,rng,L); cs=climb.score(p,cur)
        for _ in range(400):
            n=climb.mutate(p,cur,rng,L); ns=climb.score(p,n)
            if ns>=cs: cur,cs=n,ns
        if cs>best: best,bs=cs,(cur)
    print('p',p,'mingap',mingap,'best rho/u',float(best),flush=True)
    return best,bs
for p in (3,4,5):
    for mg in (p,p-1):
        b,s=run(p,mg,6,40000,p+mg)
        if b>2:
            sc=[(o,[(sg,m,gp) for sg,m,gp in e]) for o,e in s]; print('  QEX-weak spec',sc)
