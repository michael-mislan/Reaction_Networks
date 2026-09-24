"""Bounded sparse finite-inverse extension; numerical proof-feasibility only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from pathlib import Path
import json
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import splu,LinearOperator,onenormest
W=Path(__file__).resolve().parent

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--certify',action='store_true');args=ap.parse_args()
    a=np.load(W/'fourier_N40.npz');N=40;M=192;omega=float(a['omega']);d=9*(2*M+1)+1
    weights=np.array([.000212,1,.79,.000618,.000539,.2304,.1763,.01994,.1881])
    z=a['z']*weights[None,:];J=a['J']*weights[:,None]/weights[None,:]
    assert np.array_equal(z,z[::-1].conjugate())
    B=a['B']*weights[:,None,None]/weights[None,:,None]/weights[None,None,:]
    bm=np.einsum('ijk,lk->lij',B,z);ks=np.arange(-N,N+1)
    ri=[];ci=[];vv=[]
    def addblock(i,j,block):
        rows,cols=np.nonzero(block)
        ri.extend((9*i+rows).tolist());ci.extend((9*j+cols).tolist());vv.extend(block[rows,cols].tolist())
    for k in range(-M,M+1):
        addblock(k+M,k+M,1j*k*omega*np.eye(9)-J)
        for h in ks:
            if abs(k-h)<=M:addblock(k+M,k-h+M,-bm[h+N])
        if abs(k)<=N:
            for i,v in enumerate(1j*k*.2*z[k+N]):ri.append(9*(k+M)+i);ci.append(d-1);vv.append(v)
    for k,f in [(1,1/(2j)),(-1,-1/(2j))]:ri.append(d-1);ci.append(9*(M+k)+8);vv.append(f)
    D=coo_matrix((vv,(ri,ci)),shape=(d,d)).tocsc();lu=splu(D)
    print('sparse factored',d,D.nnz,flush=True)
    Aop=LinearOperator((d,d),matvec=lu.solve,rmatvec=lambda x:lu.solve(x,trans='H'),matmat=lu.solve,dtype=complex)
    Anorm=float(onenormest(Aop))
    if args.certify:
        return certify(a,z,J,B,bm,omega,D,lu,M,N,weights)
    # center defect
    conv=np.zeros((4*N+1,9),complex)
    for i in range(2*N+1):conv[i:i+2*N+1]+=z@bm[i].T/2
    F=np.zeros(d,complex)
    for k in range(-2*N,2*N+1):
        f=-conv[k+2*N]
        if abs(k)<=N:f=f+1j*k*omega*z[k+N]-J@z[k+N]
        F[9*(k+M):9*(k+M)+9]=f
    F[-1]=(z[N+1,8]-z[N-1,8])/(2j)
    Y=float(np.linalg.norm(lu.solve(F),1))
    columns=np.zeros(d);Ztail=0.
    R={k:np.linalg.inv(1j*k*omega*np.eye(9)-J) for k in range(M+1,M+2*N+1)}
    for k in range(M+1,M+N+1):
        for h in ks:
            j=k-h
            if abs(j)<=M:columns[9*(j+M):9*(j+M)+9]+=np.sum(abs(R[k]@bm[h+N]),axis=0)
    Zfinite=float(max(columns))
    for l in range(M+1,M+N+1):
        C=np.zeros((d,9),complex)
        for h in ks:
            k=l+h
            if abs(k)<=M:C[9*(k+M):9*(k+M)+9]=-bm[h+N]
        col=np.sum(abs(lu.solve(C)),axis=0)
        for h in ks:
            k=l+h
            if abs(k)>M:col+=np.sum(abs(R[k]@bm[h+N]),axis=0)
        Ztail=max(Ztail,float(max(col)))
    # Uniform far-tail column bound: componentwise supremum of the summed
    # row contributions, not a sum of unrelated individual harmonic suprema.
    # This is sampled in this pilot, so is NOT yet a rigorous bound.
    maximal=np.zeros((9,9));Rnorm=0.;kRnorm=0.
    for k in np.unique(np.r_[np.arange(M+1,M+301),np.geomspace(M+301,20000,300).astype(int)]):
        RR=np.linalg.inv(1j*k*omega*np.eye(9)-J)
        # To bound a column at input l, output is l+h: retain this dependency.
        pass
    for l in np.unique(np.r_[np.arange(M+N+1,M+N+301),np.geomspace(M+N+301,20000,300).astype(int)]):
        col=np.zeros(9)
        for h in ks:
            k=l+h;RR=np.linalg.inv(1j*k*omega*np.eye(9)-J)
            col+=np.sum(abs(RR@bm[h+N]),axis=0)
            Rnorm=max(Rnorm,np.linalg.norm(RR,1));kRnorm=max(kRnorm,k*np.linalg.norm(RR,1))
        maximal[0]=np.maximum(maximal[0],col)
    Zfar=float(max(maximal[0]));Z=max(Zfinite,Ztail,Zfar)
    Bnorm=float(np.max(np.sum(abs(B),axis=0)))
    L=float(max(Anorm,Rnorm)*Bnorm+2*.2*max(M*Anorm,kRnorm))
    result={'evidence':'N only: inverse norm estimate and sampled far tail','center_modes':N,'inverse_modes':M,'dimension':d,'nnz':D.nnz,'weights':weights.tolist(),'Y':Y,'Zfinite':Zfinite,'Ztail':Ztail,'Zfar':Zfar,'Z':Z,'A_norm_estimate':Anorm,'L_estimate':L,'radii_discriminant':float((1-Z)**2-2*L*Y),'feasible_estimate':bool(Z<1 and (1-Z)**2>2*L*Y)}
    (W/'sparse_fourier_pilot.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

def certify(a,z,J,B,bm,omega,D,lu,M,N,weights):
    """Finite binary64 operations with explicit conservative error budgets.

    All stored binary64 numbers define exact dyadic rationals. Matrix product
    error is bounded by gamma=2^-36 times product of absolute induced norms;
    this exceeds gamma_(16*d) for d=3466 and unit roundoff 2^-53. Scalar norm
    reductions receive the same envelope. No overflow/underflow-relevant
    magnitudes occur; absolute 1e-100 allowances dominate subnormal errors.
    """
    from mpmath import iv
    from finite_source import coefficients,mid
    iv.dps=55;gamma=2.0**-36;d=D.shape[0]
    up=lambda x:np.nextafter(float(x),np.inf)
    upper=lambda x:up(float(x.b))
    normup=lambda x:upper(iv.mpf(float(x))*(1+iv.mpf(gamma))+iv.mpf('1e-100'))
    Ji,Bi,scales=coefficients(a)
    jerr=max(sum((abs(Ji[i][j]-iv.mpf(float(J[i,j]))).b for i in range(9)),iv.mpf(0)).b for j in range(9))
    berr=max(sum((abs(Bi[i][j][k]-iv.mpf(float(B[i,j,k]))).b for i in range(9)),iv.mpf(0)).b for j in range(9) for k in range(9))
    bnorm=max(sum((abs(Bi[i][j][k]).b for i in range(9)),iv.mpf(0)).b for j in range(9) for k in range(9))
    zsum=normup(np.linalg.norm(z.ravel(),1))
    # Also covers assembling D and each B(z_h,.) in binary64.
    # <=128 operations per assembled entry, gamma_128 < 2^-44.
    # The induced magnitude bound is <5000, so 5e-10 is conservative.
    assert np.linalg.norm(J,1)+M*omega+500*zsum+1+.2*N*zsum<5000
    de=iv.mpf(jerr)+iv.mpf(berr)*iv.mpf(zsum)+iv.mpf('5e-10')
    assert de.b<iv.mpf('1e-9') and bnorm.b<500
    print('source coefficient errors',str(jerr),str(berr),flush=True)
    # A is an explicit dyadic approximate inverse, not the unchecked LU inverse.
    A=np.empty((d,d),complex)
    for j in range(0,d,96):
        n=min(96,d-j);rhs=np.zeros((d,n),complex);rhs[np.arange(j,j+n),np.arange(n)]=1
        A[:,j:j+n]=lu.solve(rhs)
    reverse=np.r_[np.arange(d-1).reshape(-1,9)[::-1].ravel(),d-1]
    A=(A+A[reverse][:,reverse].conjugate())*.5
    Anorm=normup(max(np.sum(abs(A),axis=0)));Dnorm=normup(max(np.asarray(abs(D).sum(axis=0)).ravel()))
    E=(D.T@A.T).T
    E[np.arange(d),np.arange(d)]-=1
    residual=normup(max(np.sum(abs(E),axis=0)))
    inverse_error=upper(iv.mpf(residual)+iv.mpf(gamma)*iv.mpf(Anorm)*iv.mpf(Dnorm)+iv.mpf(Anorm)*iv.mpf('1e-9'))
    assert inverse_error<.05
    print('inverse residual certified upper',inverse_error,'A norm',Anorm,flush=True)
    del E
    exactF=np.load(W/'finite_center_defect.npz');assert np.array_equal(z,exactF['z'])
    F=np.zeros(d,complex)
    F[9*(M-2*N):9*(M+2*N+1)]=exactF['F'].ravel();F[-1]=exactF['phase']
    Y=upper(iv.mpf(normup(np.linalg.norm(A@F,1)))+iv.mpf(gamma)*iv.mpf(Anorm)*iv.mpf(normup(np.linalg.norm(F,1)))+iv.mpf(Anorm)*iv.mpf('1e-24'))
    # Certified resolvents of the exact source J at every integer tail mode.
    K=20000;kk=np.arange(M+1,K+N+1);H=1j*kk[:,None,None]*omega*np.eye(9)[None,:,:]-J[None,:,:]
    RR=np.linalg.inv(H);rn=np.max(np.sum(abs(RR),axis=1),axis=1);hn=np.max(np.sum(abs(H),axis=1),axis=1)
    er=np.max(np.sum(abs(RR@H-np.eye(9)),axis=1),axis=1)
    rnupper=np.nextafter(rn*(1+gamma),np.inf);hnupper=np.nextafter(hn*(1+gamma),np.inf)
    eta=normup(np.max(er*(1+gamma)+gamma*rnupper*hnupper+rnupper*1e-9))
    assert eta<1e-6
    Rerr=upper(iv.mpf(normup(max(rn)))*iv.mpf('1e-6')/(1-iv.mpf('1e-6')))
    columns=np.zeros(d)
    for k in range(M+1,M+N+1):
        for h in range(-N,N+1):
            j=k-h
            if abs(j)<=M:columns[9*(j+M):9*(j+M)+9]+=np.sum(abs(RR[k-M-1]@bm[h+N]),axis=0)
    Zfinite=normup(max(columns))+inverse_error
    Ztail=0.
    for l in range(M+1,M+N+1):
        C=np.zeros((d,9),complex)
        for h in range(-N,N+1):
            k=l+h
            if abs(k)<=M:C[9*(k+M):9*(k+M)+9]=-bm[h+N]
        col=np.sum(abs(A@C),axis=0)
        for h in range(-N,N+1):
            k=l+h
            if abs(k)>M:col+=np.sum(abs(RR[k-M-1]@bm[h+N]),axis=0)
        Ztail=max(Ztail,float(max(col)))
    # Bound all remaining positive input modes l=M+N+1,...,K; conjugacy
    # gives the identical negative-frequency column sums.
    far=np.zeros((K-M-N,9))
    for h in range(-N,N+1):
        # output k=l+h: its lowest index in RR is N+h.
        products=RR[N+h:N+h+len(far)]@bm[h+N]
        far+=np.sum(abs(products),axis=1)
    Zfar=normup(float(far.max()))
    bmsum=normup(sum(np.linalg.norm(b,1) for b in bm))
    # Past K use the convergent geometric resolvent series.
    jnorm=normup(np.linalg.norm(J,1))+1e-9
    asym=iv.mpf(str(bmsum+1e-9))/(iv.mpf(K+1-N)*iv.mpf(omega)-iv.mpf(str(jnorm)))
    asymupper=up(float(asym.b));Zfar=max(Zfar,asymupper)
    cross_error=upper(iv.mpf(gamma)*iv.mpf(Anorm)*iv.mpf(bmsum)+iv.mpf(Anorm)*iv.mpf('1e-9')+iv.mpf(Rerr)*iv.mpf(bmsum)+iv.mpf(normup(max(rn)))*iv.mpf('1e-9')+iv.mpf('1e-6'))
    Zfinite=up(Zfinite+cross_error);Ztail=up(Ztail+cross_error);Zfar=up(Zfar+cross_error)
    Z=up(max(Zfinite,Ztail,Zfar))
    # Tail inverse and k*inverse bounds including the infinite asymptotic part.
    assert normup(max(rn))/(1-1e-6)<1e4
    assert normup(max(kk*rn))/(1-1e-6)<1e6
    assert (K+1)*float((1/(iv.mpf(K+1)*iv.mpf(omega)-iv.mpf(str(jnorm)))).b)<1e6
    L=upper(iv.mpf(max(Anorm,1e4))*500+2*iv.mpf(float(.2))*max(iv.mpf(M)*iv.mpf(Anorm),iv.mpf('1e6')))
    radius=iv.mpf('1.5e-12');YI=iv.mpf(Y);ZI=iv.mpf(Z);LI=iv.mpf(L)
    inclusion=YI+ZI*radius+LI*radius*radius/2
    contraction=ZI+LI*radius
    result={'evidence':'C+I finite Fourier existence with explicit IEEE error budgets; attraction separate','N_center':N,'M_inverse':M,'dimension':d,'gamma':gamma,'source_D_error_upper':'1e-9','center_defect_conversion_error_upper':'1e-24','A_norm_upper':Anorm,'A_D_inverse_error_upper':inverse_error,'Y_upper':Y,'Zfinite_upper':Zfinite,'Ztail_upper':Ztail,'Zfar_upper':Zfar,'Z_upper':Z,'L_upper':L,'radius':'1.5e-12','image_radius':str(inclusion),'contraction':str(contraction),'strict_inclusion':bool(inclusion.b<radius.a),'strict_contraction':bool(contraction.b<1),'tail_K':K,'resolvent_relative_error_upper':'1e-6','cross_error_upper':cross_error}
    (W/'finite_fourier_certificate.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2),flush=True)
    assert inclusion.b<radius.a and contraction.b<1
    # Store the exact dyadic inverse and finite center used by this certificate.
    np.savez_compressed(W/'finite_fourier_inverse.npz',A=A,z=z,omega=omega,weights=weights)
if __name__=='__main__':main()
