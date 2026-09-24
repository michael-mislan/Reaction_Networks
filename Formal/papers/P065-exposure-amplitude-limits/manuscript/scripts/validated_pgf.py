"""Outward dyadic Taylor enclosure. No floating arithmetic in the certificate.

Local remainder: coefficient p on the entire invariant cube bounds y^(p)/p!.
Global propagation: Metzler Jacobian row sums <=9/100 on the cube, hence flow
is exp(9t/100)-Lipschitz in sup norm. Rational 1/(1-9dt/100) bounds that factor.
"""
from fractions import Fraction as F
from pathlib import Path
import json, time, argparse
from exact_source_checks import source

S=1<<110
def ceildiv(a,b): return -((-a)//b)
class I:
    __slots__=('l','u')
    def __init__(self,x=0,u=None):
        if u is not None: self.l,self.u=x,u
        else:
            x=F(x); self.l=x.numerator*S//x.denominator
            self.u=ceildiv(x.numerator*S,x.denominator)
    def __add__(x,y):
        if not isinstance(y,I): y=I(y)
        return I(x.l+y.l,x.u+y.u)
    __radd__=__add__
    def __neg__(x): return I(-x.u,-x.l)
    def __sub__(x,y): return x+-y if isinstance(y,I) else x+I(-y)
    def __mul__(x,y):
        if not isinstance(y,I): y=I(y)
        v=[x.l*y.l,x.l*y.u,x.u*y.l,x.u*y.u]
        return I(min(v)//S,ceildiv(max(v),S))
    __rmul__=__mul__
    def __truediv__(x,n):
        assert isinstance(n,int) and n>0
        return I(x.l//n,ceildiv(x.u,n))

def pair(x,y):
    return [x[0]*y[0],(x[0]*y[1]+x[1]*y[0])/2,
            (x[0]*y[2]+x[2]*y[0]+2*x[1]*y[1])/4,
            (x[0]*y[3]+x[3]*y[0])/2,
            (x[0]*y[4]+x[4]*y[0]+x[1]*y[3]+x[3]*y[1])/4,
            (x[0]*y[5]+x[5]*y[0]+2*x[3]*y[3])/4]

def coefficients(e,z,p):
    Q=source(e)[0]; d=list(map(F,['.3','.3','.3','.01','.3','.01']))
    J=[[(j,I(Q[i][j]-(d[i]+F('.1') if i==j else 0)))
         for j in range(6) if Q[i][j] or i==j] for i in range(6)]
    cs=[z]
    for k in range(p):
        ds=[pair(cs[j],cs[k-j]) for j in range(k+1)]
        cs.append([(sum((a*cs[k][j] for j,a in J[i]),I())+
                    (I(d[i]) if k==0 else I())+
                    sum((x[i] for x in ds),I())/10)/(k+1) for i in range(6)])
    return cs

def phase(center,err,e,t,dt,p):
    count=t/dt; assert count.denominator==1
    cube=[I(0,S) for _ in range(6)]
    cp=coefficients(e,cube,p)[p]
    M=max(max(abs(x.l),abs(x.u)) for x in cp)
    remainder=ceildiv(M*dt.numerator**p,dt.denominator**p)
    dh=I(dt)
    g=1/(1-F(9,100)*dt)
    for _ in range(int(count)):
        cs=coefficients(e,[I(x,x) for x in center],p-1)
        interval=cs[-1]
        for k in range(p-2,-1,-1): interval=[x*dh+y for x,y in zip(interval,cs[k])]
        nxt=[min(S,max(0,(x.l+x.u)//2)) for x in interval]
        local=max(max(abs(c-x.l),abs(c-x.u)) for c,x in zip(nxt,interval))+remainder
        err=ceildiv(err*g.numerator,g.denominator)+local
        center=nxt
    return center,err,dict(e=str(e),duration=str(t),steps=int(count),remainder_scaled=remainder,
                           global_error=str(F(err,S)),derivative_bound=str(F(M,S)))

def certify(phases,terminal=F(0),dt=F(1,20),p=12):
    # Chronological phases, reversed for the backward extinction flow.
    start=I(terminal); center=[(start.l+start.u)//2]*6
    err=max(center[0]-start.l,start.u-center[0]); records=[]
    for e,t in reversed(phases):
        center,err,record=phase(center,err,e,t,dt,p); records.append(record)
    bounds=[(max(F(0),F(x-err,S)),min(F(1),F(x+err,S))) for x in center]
    return dict(phases=[[str(e),str(t)] for e,t in phases],terminal=str(terminal),
                step=str(dt),order=p,bits=110,records=records,
                extinction_bounds=[[str(a),str(b)] for a,b in bounds],
                survival_AA_upper=str(1-bounds[5][0]),
                survival_AA_upper_display=float(1-bounds[5][0]))

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--pilot',action='store_true'); args=ap.parse_args()
    before=time.time()
    if args.pilot:
        r=certify([(F('.3'),F(1))]); print(json.dumps(r,indent=2))
    else:
        # Finite mission: eraser at .3 for 40, then .01 for 60; killing continues.
        r=certify([(F('.3'),F(40)),(F('.01'),F(60))])
        assert F(r['survival_AA_upper'])<F(1,100)
        r['elapsed_seconds']=time.time()-before
        p=Path(__file__).resolve().parents[1]/'publication'
        p.mkdir(exist_ok=True); (p/'validated_policy.json').write_text(json.dumps(r,indent=2))
        print(json.dumps(r,indent=2))
