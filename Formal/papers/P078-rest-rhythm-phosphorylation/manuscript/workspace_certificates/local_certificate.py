"""Local rational-source Bautin certificate. mpmath interval arithmetic, no Lean claim.

Off Hopf: solve rows 0..7 of (iw-J)q=0 with q8=1; use the
remaining complex residual. Normalize a transpose minor vector by ell.q.
These are explicit smooth rational functions wherever the solved minors
and pairing are nonzero. They agree with eigenvectors at residual zero.
"""
from pathlib import Path
import json
from mpmath import mp, iv

W=Path(__file__).resolve().parent
PATCH=json.loads((W/'rational_patch.json').read_text())
LEVEL=[0,1,2,1,2,3]; EN=[4,4,4,5,5,5]
P=[[-1,0,0,-1,0,0,0,0,0],
   [1,-1,0,0,-1,0,-1,0,0],
   [0,1,-1,0,0,-1,0,-1,0],
   [0,0,1,0,0,0,0,0,-1],
   [0,0,0,-1,-1,-1,0,0,0],
   [0,0,0,0,0,0,-1,-1,-1]]+[[int(j==k) for j in range(9)] for k in range(3,9)]

class Jet:
    ctx=mp
    def __init__(self,x=0,d=None):
        if isinstance(x,Jet): self.v,self.d=x.v,x.d; return
        self.v=x if hasattr(x,'_mpci_') else self.ctx.mpc(x.real,x.imag) if isinstance(x,complex) else self.ctx.mpc(x)
        self.d=d or [self.ctx.mpc(0) for _ in range(3)]
    def __add__(a,b):
        b=Jet(b);return Jet(a.v+b.v,[x+y for x,y in zip(a.d,b.d)])
    __radd__=__add__
    def __neg__(a):return Jet(-a.v,[-x for x in a.d])
    def __sub__(a,b):return a+-Jet(b)
    def __rsub__(a,b):return Jet(b)+-a
    def __mul__(a,b):
        b=Jet(b);return Jet(a.v*b.v,[x*b.v+a.v*y for x,y in zip(a.d,b.d)])
    __rmul__=__mul__
    def __truediv__(a,b):
        b=Jet(b);return Jet(a.v/b.v,[(x-(a.v/b.v)*y)/b.v for x,y in zip(a.d,b.d)])
    def conj(a):return Jet(a.ctx.mpc(a.v.real,-a.v.imag),[a.ctx.mpc(x.real,-x.imag) for x in a.d])
    def real(a):return Jet(a.v.real,[x.real for x in a.d])
    def imag(a):return Jet(a.v.imag,[x.imag for x in a.d])

def dot(a,b):return sum((x*y for x,y in zip(a,b)),Jet())
def solve(A,b):
    c=Jet.ctx;n=len(b)
    A=[[Jet(x) for x in row] for row in A];b=list(map(Jet,b))
    V=c.matrix([[x.v for x in row] for row in A]); bv=c.matrix([x.v for x in b])
    # Each interval LU solve certifies every member of its interval system;
    # pivot divisions must exclude zero. No midpoint result is used as proof.
    x=c.lu_solve(V,bv)
    ds=[]
    for k in range(3):
        rhs=c.matrix([b[i].d[k]-sum(A[i][j].d[k]*x[j] for j in range(n)) for i in range(n)])
        ds.append(c.lu_solve(V,rhs))
    return [Jet(x[i],[d[i] for d in ds]) for i in range(n)]

def source(s,r):
    x=[Jet(a)+s*Jet(b) for a,b in zip(PATCH['x0'],PATCH['v'])]
    f=[Jet(a)+s*Jet(b) for a,b in zip(PATCH['q0'],PATCH['w'])]
    J=[[Jet() for _ in range(9)] for _ in range(9)]
    bind=[]
    for k in range(6):
        ratio=r if k==3 else Jet('0.01')
        v=(1+ratio)*f[k%3];a=v/(x[LEVEL[k]]*x[EN[k]])
        bind.append(a)
        J[k%3][3+k]=(1 if k<3 else -1)*f[k%3]/x[6+k]
        for j in range(9):
            J[3+k][j]=a*(x[EN[k]]*P[LEVEL[k]][j]+x[LEVEL[k]]*P[EN[k]][j])-v/x[6+k]*int(j==3+k)
    def B(u,v):
        pu=[dot(row,u) for row in P];pv=[dot(row,v) for row in P]
        return [Jet() for _ in range(3)]+[bind[k]*(pu[LEVEL[k]]*pv[EN[k]]+pv[LEVEL[k]]*pu[EN[k]]) for k in range(6)]
    return J,B

def evaluate(values,ctx=mp,quintic=False):
    Jet.ctx=ctx
    par=[Jet(v,[ctx.mpc(int(i==j)) for j in range(3)]) for i,v in enumerate(values)]
    s,r,om=par;J,B=source(s,r)
    mat=lambda m:[[m*1j*om*int(i==j)-J[i][j] for j in range(9)] for i in range(9)]
    A=mat(1)
    q=solve([row[:8] for row in A[:8]],[-row[8] for row in A[:8]])+[Jet(1)]
    ell=solve([[A[j][i] for j in range(8)] for i in range(8)],[-A[8][i] for i in range(8)])+[Jet(1)]
    pair=dot(ell,q);ell=[z/pair for z in ell];qb=[z.conj() for z in q]
    residual=dot(A[8],q)
    h20=solve(mat(2),B(q,q));h11=solve(mat(0),B(q,qb))
    rhs=[2*a+b for a,b in zip(B(q,h11),B(qb,h20))]
    c1=dot(ell,rhs)/2
    out={'F':[residual.real(),residual.imag(),c1.real()], 'J':J,'q':q,'ell':ell,'c1':c1,'pair':pair}
    if quintic:
        border=[A[i]+[q[i]] for i in range(9)]+[ell+[Jet()]]
        h21=solve(border,[rhs[i]-2*c1*q[i] for i in range(9)]+[Jet()])[:9]
        h30=solve(mat(3),[3*z for z in B(q,h20)])
        h31=solve(mat(2),[3*a+b+3*c-6*c1*d for a,b,c,d in zip(B(q,h21),B(qb,h30),B(h11,h20),h20)])
        h22=solve(mat(0),[2*a+2*b+c+2*d-4*(c1+c1.conj())*e for a,b,c,d,e in zip(B(q,[z.conj() for z in h21]),B(qb,h21),B(h20,[z.conj() for z in h20]),B(h11,h11),h11)])
        c2=dot(ell,[3*a+2*b+c+6*d+3*e for a,b,c,d,e in zip(B(q,h22),B(qb,h31),B([z.conj() for z in h20],h30),B(h11,h21),B([z.conj() for z in h21],h20))])/12
        out['c2']=c2
    return out

def main():
    mp.dps=55
    def ff(s,r,o):return tuple(z.v.real for z in evaluate([s,r,o])['F'])
    root=mp.findroot(ff,(0,'1.3837873770535','0.2418113888178'),tol=mp.mpf('1e-45'))
    a=evaluate(root,quintic=True)
    data={'evidence':'N high precision; certificate pending','root':[mp.nstr(v,50) for v in root], 'c1':str(a['c1'].v),'c2':str(a['c2'].v), 'DF':[[mp.nstr(v.real,40) for v in f.d] for f in a['F']]}
    (W/'patch_locator.json').write_text(json.dumps(data,indent=2))
    print(json.dumps(data,indent=2),flush=True)
    iv.dps=55
    radius=iv.mpf('1e-20')
    box=[iv.mpf(v)+iv.mpf(['-1e-20','1e-20']) for v in data['root']]
    z=evaluate(box,iv,quintic=True)
    c=evaluate([iv.mpf(v) for v in data['root']],iv)
    C=mp.inverse(mp.matrix([[d.real for d in f.d] for f in a['F']]))
    CI=iv.matrix([[iv.mpf(mp.nstr(v,50)) for v in row] for row in C.tolist()])
    DI=iv.matrix([[d.real for d in f.d] for f in z['F']])
    E=iv.eye(3)-CI*DI
    ab=lambda t:abs(t).b
    eta=max(sum((ab(E[i,j]) for j in range(3)),iv.mpf(0)).b for i in range(3))
    corr=CI*iv.matrix([f.v.real for f in c['F']])
    Y=max(ab(v) for v in corr)
    bound=Y+eta*radius
    cert={'arithmetic':'mpmath.iv 55 decimal digits; directed interval operations','radius':str(radius),'root_center':data['root'],'inverse':[[mp.nstr(v,50) for v in row] for row in C.tolist()], 'eta_upper':str(eta),'Y_upper':str(Y),'image_radius_upper':str(bound),'strict_inclusion':bool(bound<radius),'contraction':bool(eta<1),'c2_real':str(z['c2'].v.real),'DF':[[str(d.real) for d in f.d] for f in z['F']]}
    assert bound<radius and eta<1
    assert z['c2'].v.real.b<0
    # Faddeev-LeVerrier characteristic polynomial, then exact-root division
    # by z^2+omega^2. Intervals enclose the degree-seven quotient at the root.
    JI=iv.matrix([[v.v.real for v in row] for row in z['J']])
    H=iv.eye(9); coeff=[iv.mpf(1)]
    for k in range(1,10):
        H=JI*H
        ck=-sum((H[i,i] for i in range(9)),iv.mpf(0))/k
        coeff.append(ck); H=H+ck*iv.eye(9)
    u=box[2]*box[2]
    quotient=[]
    for k in range(8):quotient.append(coeff[k]-(u*quotient[k-2] if k>=2 else 0))
    # Standard Routh array: positive first column iff Hurwitz, no zero rows.
    rows=[quotient[0::2],quotient[1::2]]
    for k in range(2,8):
        prev,cur=rows[-2:]
        rows.append([(cur[0]*prev[j+1]-prev[0]*cur[j+1])/cur[0] for j in range(3)]+[iv.mpf(0)])
    first=[row[0] for row in rows]
    assert all(v.a>0 for v in first)
    # Hopf tangent and rank in (s,r): solve the first two residual equations.
    DD=[[d.real for d in f.d] for f in z['F']]
    tangent=iv.lu_solve(iv.matrix([[DD[i][1],DD[i][2]] for i in range(2)]),iv.matrix([-DD[i][0] for i in range(2)]))
    slope=DD[2][0]+DD[2][1]*tangent[0]+DD[2][2]*tangent[1]
    ar=sum((z['ell'][i].v*sum((z['J'][i][j].d[1]*z['q'][j].v for j in range(9)),iv.mpc(0)) for i in range(9)),iv.mpc(0)).real
    assert ar.b<0 and slope.b<0
    # Positivity on the entire declared rational patch, not just the root box.
    sd=iv.mpf(PATCH['s_domain']); rd=iv.mpf(PATCH['r_domain'])
    xpos=[iv.mpf(a)+sd*iv.mpf(b) for a,b in zip(PATCH['x0'],PATCH['v'])]
    qpos=[iv.mpf(a)+sd*iv.mpf(b) for a,b in zip(PATCH['q0'],PATCH['w'])]
    assert all(v.a>0 for v in xpos+qpos+[rd])
    # Determinant of fixed rational preconditioner: no singular C loophole.
    detC=sum(((-1 if (i,j,k) in [(0,2,1),(1,0,2),(2,1,0)] else 1)*CI[0,i]*CI[1,j]*CI[2,k] for i,j,k in [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]),iv.mpf(0))
    assert detC.a>0 or detC.b<0
    cert.update(routh_first_column=[str(v) for v in first],complement_hurwitz=True,
                cubic_Hopf_slope=str(slope),eigenvalue_r_derivative=str(ar),
                unfolding_product=str(ar*slope),patch_positive=True,preconditioner_det=str(detC))
    (W/'local_root_certificate.json').write_text(json.dumps(cert,indent=2))
    print(json.dumps(cert,indent=2))

if __name__=='__main__':main()
