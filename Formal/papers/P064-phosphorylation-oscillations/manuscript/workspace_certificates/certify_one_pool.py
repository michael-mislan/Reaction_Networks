from interval_arithmetic import *
from pathlib import Path
import json
import sys
ROBUST = "--robust" in sys.argv
COMPRESSED = "--compressed" in sys.argv or ROBUST
ATTRACTING = "--attracting" in sys.argv or COMPRESSED
KE = 1 if "--closed" in sys.argv or ATTRACTING else 0
def main():
    global solve
    if ROBUST:solve=solve_preconditioned
    import preparation_pilot as pilot
    x=list(map(s.Rational,pilot.XQ)); q=list(map(s.Rational,pilot.QFQ))
    if ATTRACTING:
        x=list(map(s.Rational,["50","12","1/5","2/5","23/10","2/5","23/50","7/250","17/10","23","9/50","4"]))
        q=list(map(s.Rational,["1/10","32/5","6/5"]))
        if COMPRESSED:
            x[0]=s.Rational(2);x[7]=s.Rational(3,10)
    def exactJ(r):
        rr=[s.Rational(1,100)]*6;rr[3]=r
        J=s.zeros(9)
        for j in range(6):
            lev=int(pilot.LEVEL[j]);enz=4+j//3;v=(1+rr[j])*q[j%3]
            J[j%3,3+j]=(1 if j<3 else -1)*q[j%3]/x[6+j]
            for i in range(3):J[3+j,i]=v/x[lev]*int(pilot.T[lev,i])
            for h in range(6):
                J[3+j,3+h]=-(v/x[6+j] if h==j else 0)-v/x[lev]*int(pilot.LEVEL[h]==lev)-(v/x[enz]*int(h//3==j//3) if j>=3 or KE else 0)
        return J
    j0=exactJ(0);j1=exactJ(1)
    p0=j0.charpoly().all_coeffs();pa=j1.charpoly().all_coeffs()
    p1=[b-a for a,b in zip(p0,pa)]
    assert exactJ(2).charpoly().all_coeffs()==[a+2*b for a,b in zip(p0,p1)]
    row=dict(x=list(map(str,x)),q=list(map(str,q)),ratios=['1/100']*6,p0=list(map(str,p0)),p1=list(map(str,p1)),clamp='closed source' if KE else 'free E fixed; F total and substrate total conserved')
    c0=list(map(I,row['p0']));c1=list(map(I,row['p1']))
    if ROBUST:
        endpoint=[]
        for xx in [s.Rational(199999999,100000000),s.Rational(200000001,100000000)]:
            x[0]=xx
            aa=exactJ(0).charpoly().all_coeffs();bb=exactJ(1).charpoly().all_coeffs()
            endpoint.append((aa,[b-a for a,b in zip(aa,bb)]))
        c0=[I(min(F(str(v)),F(str(w))),max(F(str(v)),F(str(w)))) for v,w in zip(endpoint[0][0],endpoint[1][0])]
        c1=[I(min(F(str(v)),F(str(w))),max(F(str(v)),F(str(w)))) for v,w in zip(endpoint[0][1],endpoint[1][1])]
    E0,O0=eo(list(map(F,row['p0'])));E1,O1=eo(list(map(F,row['p1'])))
    phi=s.Poly(O0*E1-E0*O1,t)
    intervals=s.polys.polytools.intervals(phi,eps=s.Rational(1,10**55))
    positives=[(a,b,m) for ((a,b),m) in intervals if a>0]
    assert len(positives)==1
    a,b,m=positives[0];assert m==1
    # Exact Sturm count, not reliance on floating roots.
    assert phi.count_roots(a,b)==1
    ti=I(str(a),str(b))
    if ROBUST:
        mid=(F(str(a))+F(str(b)))/2
        ti=I(mid-F('1e-9'),mid+F('1e-9'))
    omega=ti.sqrt()
    def parts(cs,tt):
        ee=I();oo=I()
        for k in range(9,-1,-1):
            cc=cs[9-k]*((-1)**(k//2))
            if k%2:oo=oo*tt+cc
            else:ee=ee*tt+cc
        return ee,oo
    if ROBUST:
        signs=[]
        for end in [ti.a,ti.b]:
            e0,o0=parts(c0,I(end));e1,o1=parts(c1,I(end))
            value=o0*e1-e0*o1
            signs.append(value)
        assert signs[0].b<0<signs[1].a or signs[1].b<0<signs[0].a, [v.approx() for v in signs]

    e0,o0=parts(c0,ti);e1,o1=parts(c1,ti)
    ri=-(e0*e1+ti*o0*o1)/(e1*e1+ti*o1*o1)
    assert ri.a>0
    x=list(map(I,row['x']));q=list(map(I,row['q']));r=list(map(I,row['ratios']));r[3]=ri
    if ROBUST:x[0]=I('199999999/100000000','200000001/100000000')
    T=[[-1,0,0],[1,-1,0],[0,1,-1],[0,0,1]]
    levels=[0,1,2,1,2,3]
    J=[[I() for _ in range(9)] for _ in range(9)]
    binding=[]
    for j in range(6):
        k=j%3; lev=levels[j];enz=4+j//3
        v=(1+r[j])*q[k];sub=v/x[lev];en=v/x[enz];cat=q[k]/x[6+j]
        J[k][3+j]=cat if j<3 else -cat
        for i in range(3):J[3+j][i]=sub*T[lev][i]
        for h in range(6):J[3+j][3+h]=-(v/x[6+j] if h==j else I())-sub*int(levels[h]==lev)-(en*int(h//3==j//3) if j>=3 or KE else I())
        binding.append(v/x[lev]/x[enz])
    z=C(0,omega)
    M=[[C(J[i][j])-(z if i==j else C()) for j in range(9)] for i in range(9)]
    right=solve([row[:8] for row in M[:8]],[-M[i][8] for i in range(8)])+[C(1)]
    left=solve([[M[j][i] for j in range(8)] for i in range(8)],[-M[8][i] for i in range(8)])+[C(1)]
    norm=dot(left,right);left=[v/norm for v in left]
    def bilinear(u,v):
        out=[C() for _ in range(9)]
        for j in range(6):
            lev=levels[j];er=range(3,6) if j<3 else range(6,9)
            su=dot(list(map(C,T[lev])),u[:3])-sum((u[3+h] for h in range(6) if levels[h]==lev),C())
            sv=dot(list(map(C,T[lev])),v[:3])-sum((v[3+h] for h in range(6) if levels[h]==lev),C())
            eu=-sum((u[h] for h in er),C()) if j>=3 or KE else C();ev=-sum((v[h] for h in er),C()) if j>=3 or KE else C()
            out[3+j]=C(binding[j])*(su*ev+sv*eu)
        return out
    conj=[v.conj() for v in right]
    b11=bilinear(right,conj);b20=bilinear(right,right)
    u=solve(J,b11)
    v=solve([[(2*z if i==j else C())-C(J[i][j]) for j in range(9)] for i in range(9)],b20)
    term=[-2*a+b for a,b in zip(bilinear(right,u),bilinear(conj,v))]
    l1=dot(left,term).re/(2*omega)
    if ROBUST: print("robust widths",ri.approx(),l1.approx(),flush=True)
    assert l1.a>0 or l1.b<0
    p=[a+ri*b for a,b in zip(c0,c1)]
    # Synthetic division by z^2+t. Exact zero remainder follows E=O=0.
    g=[]
    for k in range(8):g.append(p[k]-(ti*g[k-2] if k>=2 else I()))
    width=4
    routh=[g[::2],g[1::2]]
    while len(routh)<8:
        arow,brow=routh[-2:]
        routh.append([(brow[0]*arow[k+1]-arow[0]*brow[k+1])/brow[0] for k in range(3)]+[I()])
    assert all(v[0].a>0 for v in routh)
    dp=[p[k]*(9-k) for k in range(9)]
    def evalc(cs):
        out=C()
        for c in cs:out=out*z+C(c)
        return out
    crossing=(-evalc(c1)/evalc(dp)).re
    assert crossing.a>0 or crossing.b<0
    epsJ=[[(-J[i][j] if i>=3 else I()) for j in range(9)] for i in range(9)]
    epscross=dot(left,[dot(list(map(C,rw)),right) for rw in epsJ]).re
    # Physical log(alpha1) forcing: D1 binding contributes only complex row 3.
    forcing=[C() for _ in range(9)];forcing[6]=C((1+ri)*q[0])
    coupling=dot(left,forcing)
    residues={'free_S3':(right[2]-right[8])*coupling,'total_level3':right[2]*coupling}
    extra={'epsilon_crossing':epscross.bounds(),'residues':{k:{'real':v.re.bounds(),'imag':v.im.bounds()} for k,v in residues.items()},'right_eigenvector':[{'real':v.re.bounds(),'imag':v.im.bounds()} for v in right]}
    result={'robust_S0_interval':['199999999/100000000','200000001/100000000'] if ROBUST else None,'extra':extra,'precision_bits':BITS,'source':row,'t_interval':ti.bounds(),
      'sturm_count':1,'r_interval':ri.bounds(),'omega_interval':omega.bounds(),
      'crossing_interval':crossing.bounds(),'lyapunov_interval':l1.bounds(),
      'g7_routh_first_column':[v[0].bounds() for v in routh],
      'summary':{'t':ti.approx(),'r':ri.approx(),'omega':omega.approx(),
                 'crossing':crossing.approx(),'l1':l1.approx(),
                 'routh':[v[0].approx() for v in routh]},
      'normalization':'right eigenvector coordinate 8 = 1, left bilinear pairing = 1; B is full Hessian; C=0',
      'status':'exact rational interval computation, not Lean verification or analytic Hopf theorem'}
    Path(__file__).with_name('robust_attracting_certificate.json' if ROBUST else ('compressed_attracting_certificate.json' if COMPRESSED else ('attracting_certificate.json' if ATTRACTING else ('closed_certificate.json' if KE else 'one_pool_certificate.json')))).write_text(json.dumps(result,indent=2))
    print(json.dumps(result['summary'],indent=2))
if __name__=='__main__':main()
