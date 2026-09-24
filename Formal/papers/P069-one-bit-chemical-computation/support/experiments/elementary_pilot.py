"""A retained-intermediate feasibility diagnostic, NOT a factory realization theorem."""
import json,math
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from numba import njit

# X,Y,H,W,DX,CX,EX,ZX,DY,CY,EY,ZY; repair subsystem only, nine residents + one fuel.
inp=[];out=[];coef=[]
for X,Y,D,C,E,Z in [(0,1,4,5,6,7),(1,0,8,9,10,11)]:
    pairs=[({X:2},{D:1},1.,1e-4),({D:1,Y:1},{C:1},1.,1e-5),
           ({C:1,2:1},{E:1},1.,1e-5),({E:1},{D:1,Z:1},1.,1e-5),
           ({Z:1},{X:1,3:1},1.,1e-4)]
    for a,b,k,l in pairs:
        for aa,bb,kk in [(a,b,k),(b,a,l)]:
            v=np.zeros(12,np.int64);w=v.copy()
            for i,n in aa.items():v[i]=n
            for i,n in bb.items():w[i]=n
            inp.append(v);out.append(w);coef.append(kk)
I=np.array(inp);D=np.array(out)-I;K=np.array(coef)
resident=np.array([1,1,0,0,2,3,3,1,2,3,3,1]);fuel=np.array([0,0,1,1,0,0,1,1,0,0,1,1])
assert np.all(D@resident==0) and np.all(D@fuel==0)

@njit
def samples(n,T,seed):
    np.random.seed(seed);done=0;sumfree=0.;sumbound=0.
    for _ in range(n):
        z=np.zeros(12,np.int64);z[0]=8;z[1]=1;z[2]=1;t=0.
        while True:
            rates=K.copy()
            for r in range(20):
                for i in range(12):
                    for j in range(I[r,i]):rates[r]*=z[i]-j
            total=rates.sum()
            if total<=0:break
            t+=np.random.exponential(1/total)
            if t>T:break
            pick=np.random.random()*total;c=0.
            for r in range(20):
                c+=rates[r]
                if pick<c:z+=D[r];break
        # Converted Y is in ZX or released X; CX/EX still contain an unconverted Y.
        done+=int(z[1]+z[5]+z[6]==0)
        sumfree+=z[0]+z[1];sumbound+=(z*resident).sum()-z[0]-z[1]
        # Carry intact species into complementary daughters; preserve moiety totals.
        a=z.copy()
        for i in range(12):a[i]=np.random.binomial(z[i],.5)
        b=z-a
        assert (a*resident).sum()+(b*resident).sum()==9 and (a*fuel).sum()+(b*fuel).sum()==1
    return done,sumfree/n,sumbound/n

def split(weights,m):
    p=[1]
    for w in weights:
        v=[0]*(len(p)+w)
        for i,a in enumerate(p):v[i]+=a;v[i+w]+=a
        p=v
    return F(sum(p[m:sum(weights)-m+1]),2**len(weights))

rows=[]
for i,t in enumerate([1/4e8,.1,1.,10.]):
    done,free,bound=samples(1000,t,2900+i)
    rows.append(dict(samples=1000,T=t,corrected=done,mean_free=free,mean_bound=bound))
out=dict(evidence='N repair-only candidate; exact moiety/partition checks',rows=rows,
    first_dimer_prefix_upper=str(F(56,400000000)),
    monomer32_split_ge8=str(split([1]*32,8)),dimer16_split_ge8=str(split([2]*16,8)),
    constants='association and unimolecular forward coefficients1 model-unit; reverses 1e-4/1e-5',
    thermodynamics='D formation ratio1e4; four catalytic conversion ratios1e5,1e5,1e5,1e4 multiply to1e19',
    scope='Full elementary factory would have15 species/15 pairs. No rate equivalence or full factory certificate claimed.')
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
