"""Exact dyadic Taylor enclosures, adapted from the persister campaign.

Soundness: coefficients on the invariant cube bound normalized derivatives;
Metzler Jacobian has row sums <=9/100, so global errors propagate by
exp(.09*dt)<=1/(1-.09*dt). No binary floating arithmetic in certificate.
"""
from fractions import Fraction as F
from pathlib import Path
import json,time,argparse
from source import exact_source

S=1<<110
def ceildiv(a,b):return -((-a)//b)
class I:
    __slots__=('l','u')
    def __init__(self,x=0,u=None):
        if u is not None:self.l,self.u=x,u
        else:
            x=F(x);self.l=x.numerator*S//x.denominator;self.u=ceildiv(x.numerator*S,x.denominator)
    def __add__(x,y):
        y=y if isinstance(y,I) else I(y)
        return I(x.l+y.l,x.u+y.u)
    __radd__=__add__
    def __neg__(x):return I(-x.u,-x.l)
    def __sub__(x,y):return x+-y if isinstance(y,I) else x+I(-y)
    def __mul__(x,y):
        y=y if isinstance(y,I) else I(y)
        v=[x.l*y.l,x.l*y.u,x.u*y.l,x.u*y.u]
        return I(min(v)//S,ceildiv(max(v),S))
    __rmul__=__mul__
    def __truediv__(x,n):
        assert isinstance(n,int) and n>0
        return I(x.l//n,ceildiv(x.u,n))

def prepare(e,c,eps,law):
    d,B,C=exact_source(e,c,eps,law)
    # Check logarithmic norm bound on entire cube using nonnegative quadratic coefficients.
    for i in range(7):
        assert all(B[i][j]>=0 for j in range(7) if i!=j)
        assert all(p>=0 for j,k,p in C[i])
        assert sum(B[i])+2*sum(p for j,k,p in C[i])<=F(9,100)
        assert d[i]+sum(B[i])+sum(p for j,k,p in C[i])==0
    return [I(v) for v in d],[[(j,I(v)) for j,v in enumerate(row) if v] for row in B],[[(j,k,I(p)) for j,k,p in row if p] for row in C]

def coefficients(src,z,p):
    d,B,C=src;cs=[z]
    for n in range(p):
        nxt=[]
        for i in range(7):
            val=d[i] if n==0 else I()
            val+=sum((v*cs[n][j] for j,v in B[i]),I())
            val+=sum((v*sum((cs[k][j]*cs[n-k][l] for k in range(n+1)),I()) for j,l,v in C[i]),I())
            nxt.append(val/(n+1))
        cs.append(nxt)
    return cs

def certify(phases,law='J',eps=F(1,10),dt=F(1,20),p=12,terminal=None):
    terminal=[F(1)]*6+[F(1,5)] if terminal is None else terminal
    zs=[I(v) for v in terminal];center=[(v.l+v.u)//2 for v in zs]
    err=max(max(c-v.l,v.u-c) for c,v in zip(center,zs));records=[]
    dh=I(dt);growth=1/(1-F(9,100)*dt)
    for e,c,t in reversed(phases):
        src=prepare(e,c,eps,law);count=t/dt;assert count.denominator==1
        cp=coefficients(src,[I(0,S) for _ in range(7)],p)[p]
        M=max(max(abs(v.l),abs(v.u)) for v in cp)
        remainder=ceildiv(M*dt.numerator**p,dt.denominator**p)
        for _ in range(int(count)):
            cs=coefficients(src,[I(c,c) for c in center],p-1);v=cs[-1]
            for k in range(p-2,-1,-1):v=[x*dh+y for x,y in zip(v,cs[k])]
            nxt=[min(S,max(0,(x.l+x.u)//2)) for x in v]
            local=max(max(abs(c-x.l),abs(c-x.u)) for c,x in zip(nxt,v))+remainder
            err=ceildiv(err*growth.numerator,growth.denominator)+local;center=nxt
        records.append(dict(e=str(e),c=str(c),t=str(t),steps=int(count),local_remainder=str(F(remainder,S)),global_error=str(F(err,S))))
    bounds=[(max(F(0),F(c-err,S)),min(F(1),F(c+err,S))) for c in center]
    return dict(law=law,eps=str(eps),phases=[[str(x) for x in ph] for ph in phases],terminal=list(map(str,terminal)),dt=str(dt),order=p,bits=110,records=records,bounds=[[str(a),str(b)] for a,b in bounds],display_AA=list(map(float,bounds[5])))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--pilot',action='store_true');args=ap.parse_args();t0=time.time()
    if args.pilot:
        out=certify([(F('.3'),F(0),F(1))]);name='validated_pilot.json'
    else:
        A=(F('.3'),F(0),F(10));B=(F('.01'),F('0.120553'),F(10))
        runs={law+order:certify([A,B] if order=='AB' else [B,A],law) for law in ['J','I'] for order in ['AB','BA']}
        margins={}
        for law in ['J','I']:
            a,b=runs[law+'AB']['bounds'][5],runs[law+'BA']['bounds'][5]
            lo,hi=F(a[0])-F(b[1]),F(a[1])-F(b[0])
            margins[law]=dict(exact=[str(lo),str(hi)],display=[float(lo),float(hi)])
        assert F(margins['J']['exact'][1])<-F(16,10**7)
        assert F(margins['I']['exact'][0])>F(16,10**7)
        out=dict(runs=runs,margins=margins);name='decision_certificate.json'
    out['elapsed_seconds']=time.time()-t0
    (Path(__file__).resolve().parents[1]/'results'/name).write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='runs'},indent=2))
