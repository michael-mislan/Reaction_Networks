"""Correlation-preserving Taylor/QR enclosure of transverse monodromy.

Coordinates Q_j are exact dyadic matrices; interval transport retains a full
matrix enclosure in each moving frame. QR itself is only a coordinate choice.
Taylor tails use analytic Cauchy bounds; actual-orbit uncertainty comes from
the separately validated Fourier ball. Bounds include binary64 roundoff.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from pathlib import Path
import json,math
import numpy as np
from scipy.linalg import qr,solve_discrete_lyapunov,cholesky
from mpmath import iv
from finite_source import coefficients,mid,WEIGHTS
W=Path(__file__).resolve().parent

def main():
    iv.dps=55;up=lambda x:np.nextafter(float(x),np.inf)
    upper=lambda x:up(float(x.b))
    gamma=2.0**-40;gsmall=2.0**-45
    norm=lambda A:up(float(np.linalg.norm(A,1))*(1+gamma)+1e-100)
    a=np.load(W/'fourier_N40.npz');c=np.load(W/'finite_fourier_inverse.npz');z=c['z'];omega=float(c['omega']);N=40
    cert=json.loads((W/'finite_fourier_certificate.json').read_text());assert cert['strict_inclusion'] and cert['strict_contraction']
    rho=iv.mpf(cert['radius']);Ji,Bi,scales=coefficients(a);ks=np.arange(-N,N+1)
    Z=[[iv.mpc(float(t.real),float(t.imag)) for t in row] for row in z]
    Ai=[];coef_error=iv.mpf(0);jdelta=iv.mpf(0)
    for h in range(2*N+1):
        rowmat=[]
        for i in range(9):
            row=[]
            for j in range(9):
                v=sum((Bi[i][j][l]*Z[h][l] for l in range(9)),iv.mpc(0))+(Ji[i][j] if h==N else 0)
                row.append(v*scales[i]/scales[j])
            rowmat.append(row)
        Ai.append(rowmat)
    An=np.array([[[mid(v) for v in row] for row in mat] for mat in Ai])
    for mat,nom in zip(Ai,An):
        coef_error+=max(sum((abs(mat[i][j]-iv.mpc(float(nom[i,j].real),float(nom[i,j].imag))).b for i in range(9)),iv.mpf(0)).b for j in range(9))
    # Perturbation in physical-chart Jacobian per unit l1 Fourier error.
    baccess=max(sum((abs(Bi[i][j][l]*scales[i]/scales[j]).b for i in range(9)),iv.mpf(0)).b for j in range(9) for l in range(9))
    delta=baccess*rho
    anorm=np.array([norm(v) for v in An]);Kreal=upper(sum((iv.mpf(float(v)) for v in anorm),iv.mpf(0))+coef_error)
    # Reparameterize the true orbit to the approximate period, preserving
    # its monodromy; the unknown frequency differs by at most .2*rho.
    delta+=iv.mpf(float(.2))*rho/(iv.mpf(omega)-iv.mpf(float(.2))*rho)*(iv.mpf(Kreal)+delta)
    delta=upper(delta);coef_error=upper(coef_error)
    steps=8192;order=20;T=2*iv.pi/iv.mpf(omega);hi=T/steps;h=float(hi.mid)
    # Select an analytically justified complex-time Cauchy disk.
    tails=[]
    for ss in ['0.03','0.04','0.05','0.06','0.08','0.1']:
        radius=iv.mpf(ss)
        Kc=sum((iv.mpf(float(v))*iv.exp(abs(int(k))*iv.mpf(omega)*radius) for k,v in zip(ks,anorm)),iv.mpf(coef_error)*iv.exp(N*iv.mpf(omega)*radius))
        tails.append((upper(iv.exp(Kc*radius)*(hi/radius)**(order+1)/(1-hi/radius)),ss))
    tail,disk=min(tails)
    perturb=upper(hi*iv.mpf(delta)*iv.exp((iv.mpf(Kreal)+iv.mpf(delta))*hi))
    # Direct interval trig encloses each phase increment. Subsequent binary64
    # recurrence has total complex error <= steps*1e-14 (8 arithmetic ops).
    inc=[]
    for k in ks:
        angle=2*iv.pi*int(k)/steps;v=iv.mpc(iv.cos(angle),iv.sin(angle));u=mid(v)
        assert abs(v-iv.mpc(float(u.real),float(u.imag))).b<iv.mpf('2e-16')
        inc.append(u)
    inc=np.array(inc);phase=np.ones(2*N+1,complex);phase_error=steps*2e-15
    factors=np.array([(1j*ks*omega*h)**l/math.factorial(l)*h for l in range(order)])
    # Error in each scaled Taylor coefficient of J, uniformly in every step.
    jerrs=np.array([up((phase_error+gamma)*np.dot(abs(factors[l]),anorm)+coef_error*h*max(abs(factors[l]/h))+1e-15) for l in range(order)])
    physical_z=z*np.array([float(s.mid) for s in scales])[None,:]
    tangent=np.real(np.sum(1j*ks[:,None]*omega*physical_z,axis=0))
    Q0,_=qr(tangent[:,None],mode='full');Q=Q0.copy();C=np.eye(9);Crad=np.zeros((9,9));maxstep=0.
    I=np.eye(9)
    for step in range(steps):
        scaled=np.einsum('lk,kij->lij',factors*phase[None,:],An).real
        V=[I];errors=[0.];vnorm=[1.]
        for n in range(1,order+1):
            acc=np.zeros((9,9));er=0.;mag=0.
            for l in range(n):
                other=n-1-l;jn=norm(scaled[l]);acc+=scaled[l]@V[other]
                er+=jn*errors[other]+jerrs[l]*(vnorm[other]+errors[other])
                mag+=jn*vnorm[other]
            vn=acc/n;en=up(((er+gamma*mag)/n+1e-100)*(1+gamma))
            V.append(vn);errors.append(en);vnorm.append(norm(vn))
        Phi=sum(V,np.zeros((9,9)))
        err=up((sum(errors)+gamma*sum(vnorm)+tail+perturb+1e-13)*(1+gamma))
        Qnext,_=qr(Phi@Q)
        invQ=np.linalg.inv(Qnext);qn=norm(Q);iqn=norm(invQ)
        invres=norm(I-invQ@Qnext)+gsmall*iqn*norm(Qnext)
        assert invres<1e-10
        Tr=invQ@Phi@Q
        terr=up((iqn/(1-invres)*err*qn+invres/(1-invres)*iqn*norm(Phi)*qn+gsmall*iqn*norm(Phi)*qn)*(1+gamma))
        old=C;oldrad=Crad
        C=Tr@old
        Crad=abs(Tr)@oldrad+terr*np.ones((9,9))@(abs(old)+oldrad)+gsmall*(abs(Tr)@abs(old))+1e-100
        Crad=np.nextafter(Crad*(1+gsmall),np.inf)
        Q=Qnext;phase*=inc;maxstep=max(maxstep,terr)
        if step%2048==0:print('QR step',step,'radius',float(Crad.max()),'step error',terr,flush=True)
    Q0inv=np.linalg.inv(Q0)
    M=Q@C@Q0inv;Mr=abs(Q)@Crad@abs(Q0inv)+gamma*(abs(Q)@abs(C)@abs(Q0inv))+1e-100;Mr=np.nextafter(Mr*(1+gamma),np.inf)
    # Evaluate the true phase-zero tangent with interval Fourier uncertainty.
    rb=upper(rho)
    z0=[sum((row[j] for row in Z),iv.mpc(0)).real+iv.mpf([-rb,rb]) for j in range(9)]
    f=[]
    for i in range(9):
        f.append(scales[i]*(sum((Ji[i][j]*z0[j] for j in range(9)),iv.mpf(0))+sum((Bi[i][j][l]*z0[j]*z0[l]/2 for j in range(9) for l in range(9)),iv.mpf(0))))
    fn=np.array([mid(v) for v in f]);normal=list(map(iv.mpf,fn));pivot=int(np.argmax(abs(fn)));other=[j for j in range(9) if j!=pivot]
    U=iv.matrix([[iv.mpf(int(i==j)) if i!=pivot else -normal[j]/normal[pivot] for j in other] for i in range(9)])
    CI=iv.matrix([[iv.mpf(float(C[i,j]))+iv.mpf([-float(Crad[i,j]),float(Crad[i,j])]) for j in range(9)] for i in range(9)])
    Q0I=iv.matrix(Q0.tolist());Q0II=iv.matrix(9)
    for j in range(9):
        col=iv.lu_solve(Q0I,iv.matrix([int(i==j) for i in range(9)]))
        for i in range(9):Q0II[i,j]=col[i]
    nf=sum((x*y for x,y in zip(normal,f)),iv.mpf(0));assert nf.a>0
    event=iv.eye(9)-iv.matrix(f)*iv.matrix([normal])/nf
    full=(event*iv.matrix(Q.tolist()))*CI*(Q0II*U);DI=iv.matrix([[full[i,j].real for j in range(8)] for i in other])
    Dmid=np.array([[mid(DI[i,j]) for j in range(8)] for i in range(8)])
    Wm=solve_discrete_lyapunov(Dmid.T,np.eye(8));L=cholesky(Wm,lower=True)
    assert np.max(abs(L.imag))<1e-30
    S=iv.matrix(L.T.real.tolist())
    Sinv=iv.matrix(8)
    for j in range(8):
        rhs=iv.matrix([int(i==j) for i in range(8)]);col=iv.lu_solve(S,rhs)
        for i in range(8):Sinv[i,j]=col[i]
    DD=S*DI*Sinv;G=iv.eye(8)-DD.T*DD
    # Interval LDL pivots certify positive definiteness of I-D^T D.
    piv=[];GG=G.copy()
    for k in range(8):
        pk=GG[k,k];piv.append(str(pk))
        if not pk.a>0:break
        for i in range(k+1,8):
            for j in range(k+1,8):GG[i,j]-=GG[i,k]*GG[k,j]/pk
    passed=len(piv)==8 and all(GG[i,i].a>0 for i in range(8))
    quantitative=G-iv.eye(8)/1000
    for k in range(8):
        pk=quantitative[k,k]
        assert pk.a>0
        for i in range(k+1,8):
            for j in range(k+1,8):quantitative[i,j]-=quantitative[i,k]*quantitative[k,j]/pk
    result={'arithmetic':'Cauchy Taylor remainder + explicit binary64 error envelopes + interval event projection/LDL','steps':steps,'order':order,'cauchy_disk':disk,'local_cauchy_tail_upper':tail,'actual_J_perturbation_upper':delta,'phase_recurrence_error_upper':phase_error,'max_step_matrix_error_upper':maxstep,'monodromy_entry_radius_max':float(Mr.max()),'phase_transversality':str(nf),'LDL_pivots':piv,'transverse_attraction_pass':bool(passed),'metric_squared_contraction_upper':'999/1000 at the orbit; any slightly weaker bound holds on a sufficiently small section neighborhood','nominal_transverse_radius':float(max(abs(np.linalg.eigvals(Dmid))))}
    np.savez(W/'monodromy_enclosure.npz',M=M,radius=Mr)
    (W/'attraction_certificate.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2),flush=True)
    assert passed
if __name__=='__main__':main()
