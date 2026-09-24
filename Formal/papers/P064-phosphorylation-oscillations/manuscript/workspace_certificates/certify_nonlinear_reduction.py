"""Actual C2 algebraic elimination: derivative jet and Hopf certificate."""
from interval_arithmetic import *
from certify_reduction import matrix,reduced
import preparation_pilot as src
from pathlib import Path
import json
import sys

ATTRACTING = '--attracting' in sys.argv
if ATTRACTING:
    from fractions import Fraction
    src.XQ = list(map(Fraction, ['2','12','1/5','2/5','23/10','2/5','23/50','3/10','17/10','23','9/50','4']))
    src.QFQ = list(map(Fraction, ['1/10','32/5','6/5']))

keep=[0,1,2,3,5,6,7,8];fast=4
def run():
    n=8
    p0=reduced(matrix(0)).charpoly().all_coeffs()
    pa=reduced(matrix(1)).charpoly().all_coeffs();p1=[b-a for a,b in zip(p0,pa)]
    assert reduced(matrix(2)).charpoly().all_coeffs()==[a+2*b for a,b in zip(p0,p1)]
    E0,O0=eo(p0);E1,O1=eo(p1);phi=s.Poly(O0*E1-E0*O1,t)
    intervals=s.polys.polytools.intervals(phi,eps=s.Rational(1,10**55))
    candidates=[]
    for (a,b),mult in intervals:
        if a<=0:continue
        ti=I(str(a),str(b));ee0=ipoly(E0,ti);ee1=ipoly(E1,ti);oo0=ipoly(O0,ti);oo1=ipoly(O1,ti)
        ri=-(ee0*ee1+ti*oo0*oo1)/(ee1*ee1+ti*oo1*oo1)
        if ri.a>0:candidates.append((ti,ri,mult))
    assert len(candidates)==1
    ti,ri,mult=candidates[0];assert mult==1
    omega=ti.sqrt();z=C(0,omega)
    j0=matrix(0);jd=matrix(1)-j0
    J=[[I(str(j0[i,j]))+ri*I(str(jd[i,j])) for j in range(9)] for i in range(9)]
    d=-J[fast][fast];assert d.a>0
    h1=[J[fast][j]/d for j in keep]
    bslow=[J[i][fast] for i in keep]
    Jr=[[J[i][j]+J[i][fast]*h1[k] for k,j in enumerate(keep)] for i in keep]
    Z=[[C(Jr[i][j])-(z if i==j else C()) for j in range(n)] for i in range(n)]
    right=solve([row[:-1] for row in Z[:-1]],[-Z[i][-1] for i in range(n-1)])+[C(1)]
    left=solve([[Z[j][i] for j in range(n-1)] for i in range(n-1)],[-Z[-1][i] for i in range(n-1)])+[C(1)]
    norm=dot(left,right);left=[v/norm for v in left]
    x=list(map(I,src.XQ));q=list(map(I,src.QFQ));ratios=[I('1/100')]*6;ratios[3]=ri
    rates=[(1+ratios[j])*q[j%3]/x[int(src.LEVEL[j])]/x[4+j//3] for j in range(6)]
    def B(u,v):
        out=[C() for _ in range(9)]
        for j in range(6):
            lev=int(src.LEVEL[j]);inds=range(3,6) if j<3 else range(6,9)
            su=sum((int(src.T[lev,k])*u[k] for k in range(3)),C())-sum((u[3+k] for k in range(6) if src.LEVEL[k]==lev),C())
            sv=sum((int(src.T[lev,k])*v[k] for k in range(3)),C())-sum((v[3+k] for k in range(6) if src.LEVEL[k]==lev),C())
            eu=-sum((u[k] for k in inds),C());ev=-sum((v[k] for k in inds),C())
            out[3+j]=C(rates[j])*(su*ev+sv*eu)
        return out
    ef=[C(int(i==fast)) for i in range(9)]
    def lift(u):
        out=[C() for _ in range(9)]
        for k,i in enumerate(keep):out[i]=u[k]
        out[fast]=dot(list(map(C,h1)),u)
        return out
    def h2(u,v):return B(lift(u),lift(v))[fast]/C(d)
    def Br(u,v):
        full=B(lift(u),lift(v));h=full[fast]/C(d)
        return [full[i]+C(bslow[k])*h for k,i in enumerate(keep)]
    def Cr(u,v,w):
        aa=B(lift(u),ef);bb=B(lift(v),ef);cc=B(lift(w),ef)
        uv=h2(u,v);uw=h2(u,w);vw=h2(v,w)
        full=[a*vw+b*uw+c*uv for a,b,c in zip(aa,bb,cc)]
        hh=full[fast]/C(d)
        return [full[i]+C(bslow[k])*hh for k,i in enumerate(keep)]
    qc=[v.conj() for v in right]
    u=solve(Jr,Br(right,qc))
    v=solve([[(2*z if i==j else C())-C(Jr[i][j]) for j in range(n)] for i in range(n)],Br(right,right))
    g21=dot(left,[a-2*b+c for a,b,c in zip(Cr(right,right,qc),Br(right,u),Br(qc,v))])
    l1=g21.re/(2*omega)
    assert l1.b<0 if ATTRACTING else l1.a>0
    coeff=[I(str(a))+ri*I(str(b)) for a,b in zip(p0,p1)]
    g=[]
    for k in range(n-1):g.append(coeff[k]-(ti*g[k-2] if k>=2 else I()))
    width=(len(g)+1)//2;routh=[g[::2],g[1::2]+[I()]]
    while len(routh)<len(g):
        aa,bb=routh[-2:]
        routh.append([(bb[0]*aa[k+1]-aa[0]*bb[k+1])/bb[0] for k in range(width-1)]+[I()])
    assert all(row[0].a>0 for row in routh)
    def ev(cs):
        val=C()
        for c in cs:val=val*z+C(c)
        return val
    derivative=(-ev(list(map(lambda a:I(str(a)),p1)))/ev([coeff[k]*(n-k) for k in range(n)])).re
    assert derivative.b<0
    out={'evidence':'C+I; nonlinear implicit C2 elimination, including induced cubic derivative',
         'r':ri.bounds(),'omega':omega.bounds(),'l1':l1.bounds(),'crossing':derivative.bounds(),
         'p0':list(map(str,p0)),'p1':list(map(str,p1)),'t':ti.bounds(),
         'routh':[row[0].bounds() for row in routh],
         'summary':{'r':ri.approx(),'omega':omega.approx(),'l1':l1.approx(),'crossing':derivative.approx()}}
    out['source']={'x':list(map(str,src.XQ)), 'q':list(map(str,src.QFQ)), 'normalization':'q_D3=1; ell^T q=1; original time'}
    name='attracting_reduction_certificate.json' if ATTRACTING else 'nonlinear_reduction_certificate.json'
    Path(__file__).with_name(name).write_text(json.dumps(out,indent=2));print(json.dumps(out['summary'],indent=2))
if __name__=='__main__':run()
