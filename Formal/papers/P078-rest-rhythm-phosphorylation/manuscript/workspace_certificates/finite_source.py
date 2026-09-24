"""Exact finite-source definition and interval coefficients for Fourier validation."""
from pathlib import Path
import numpy as np
from mpmath import iv
from local_certificate import P,LEVEL,EN
W=Path(__file__).resolve().parent
WEIGHTS=np.array([.000212,1,.79,.000618,.000539,.2304,.1763,.01994,.1881])

def coefficients(a):
    iv.dps=55
    x=list(map(iv.mpf,a['xstar']));q=list(map(iv.mpf,a['currents']));r=iv.mpf(float(a['r']))
    scale=[iv.mpf(s)/iv.mpf(w) for s,w in zip(a['scale'],WEIGHTS)]
    J=[[iv.mpf(0) for _ in range(9)] for _ in range(9)]
    B=[[[iv.mpf(0) for _ in range(9)] for _ in range(9)] for _ in range(9)]
    for k in range(6):
        ratio=r if k==3 else iv.mpf(1)/100
        v=(1+ratio)*q[k%3];binding=v/(x[LEVEL[k]]*x[EN[k]])
        J[k%3][3+k]=(1 if k<3 else -1)*q[k%3]/x[6+k]*scale[3+k]/scale[k%3]
        for j in range(9):
            J[3+k][j]=(binding*(x[EN[k]]*P[LEVEL[k]][j]+x[LEVEL[k]]*P[EN[k]][j])-v/x[6+k]*int(j==3+k))*scale[j]/scale[3+k]
            for l in range(9):B[3+k][j][l]=binding*(P[LEVEL[k]][j]*P[EN[k]][l]+P[LEVEL[k]][l]*P[EN[k]][j])*scale[j]*scale[l]/scale[3+k]
    return J,B,scale

def mid(v):
    return complex(float(v.real.mid),float(v.imag.mid)) if hasattr(v,'_mpci_') else float(v.mid)

def center_defect(a,z,omega):
    J,B,scale=coefficients(a);N=(len(z)-1)//2
    Z=[[iv.mpc(float(v.real),float(v.imag)) for v in row] for row in z]
    om=iv.mpf(omega);ii=iv.mpc(0,1)
    F=[[iv.mpc(0) for _ in range(9)] for _ in range(4*N+1)]
    # Sparse tensor multiplication avoids unnecessary interval zeros.
    nonzero=[(i,j,k,B[i][j][k]) for i in range(9) for j in range(9) for k in range(9) if B[i][j][k]!=0]
    for i,j,k,b in nonzero:
        for h in range(2*N+1):
            for l in range(2*N+1):F[h+l][i]-=b*Z[h][j]*Z[l][k]/2
    for k in range(-N,N+1):
        for i in range(9):F[k+2*N][i]+=ii*k*om*Z[k+N][i]-sum((J[i][j]*Z[k+N][j] for j in range(9)),iv.mpc(0))
    phase=(Z[N+1][8]-Z[N-1][8])/(2*ii)
    f=np.array([[mid(v) for v in row] for row in F])
    error=iv.mpf(0)
    for row,vrow in zip(F,f):
        for v,v0 in zip(row,vrow):error+=abs(v-iv.mpc(float(v0.real),float(v0.imag)))
    assert error.b<iv.mpf('1e-24')
    return f,mid(phase),str(error.b)

if __name__=='__main__':
    import json
    a=np.load(W/'fourier_N40.npz');z=a['z']*WEIGHTS[None,:]
    f,phase,err=center_defect(a,z,float(a['omega']))
    np.savez(W/'finite_center_defect.npz',F=f,phase=phase,z=z)
    (W/'finite_center_defect.json').write_text(json.dumps({'arithmetic':'directed mpmath.iv 55 digits','midpoint_conversion_l1_error_upper':err,'source':'all xstar, currents, r and original scales from fourier_N40.npz denote their exact binary64 values; WEIGHTS likewise; sigma other than r is exactly 1/100'},indent=2))
    print('center defect l1',np.linalg.norm(f.ravel(),1),'conversion error',err,flush=True)
