"""Directed interval quadratic Lyapunov capture ellipsoid at exact finite source."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import json
from pathlib import Path
import numpy as np
from scipy.linalg import solve_continuous_lyapunov,cholesky
from mpmath import iv
from finite_source import coefficients,WEIGHTS,mid
from local_certificate import P
W=Path(__file__).resolve().parent
def inverse(A):
    n=A.rows;out=iv.matrix(n)
    for j in range(n):
        col=iv.lu_solve(A,iv.matrix([int(i==j) for i in range(n)]))
        for i in range(n):out[i,j]=col[i]
    return out
def ldl(A):
    G=A.copy();p=[]
    for k in range(A.rows):
        v=G[k,k];assert v.a>0,(k,str(v));p.append(str(v))
        for i in range(k+1,A.rows):
            for j in range(k+1,A.rows):G[i,j]-=G[i,k]*G[k,j]/v
    return p
def main():
    iv.dps=65;a=np.load(W/'fourier_N40.npz');Ji,Bi,sc=coefficients(a)
    # Convert the certified source back to original amplitude-scaled coordinates.
    ww=list(map(iv.mpf,WEIGHTS));J=iv.matrix([[Ji[i][j]*ww[j]/ww[i] for j in range(9)] for i in range(9)])
    B=[[[Bi[i][j][k]*ww[j]*ww[k]/ww[i] for k in range(9)] for j in range(9)] for i in range(9)]
    Jn=np.array([[float(J[i,j].mid) for j in range(9)] for i in range(9)])
    Pn=solve_continuous_lyapunov(Jn.T,-np.eye(9));S0=cholesky(Pn,lower=False)
    S=iv.matrix(S0.tolist());Si=inverse(S);A=S*J*Si
    An=np.array([[float(A[i,j].mid) for j in range(9)] for i in range(9)])
    lam=float(np.min(np.linalg.eigvalsh(-(An+An.T)/2))*.45);LI=iv.mpf(lam)
    piv=ldl(-(A+A.T)/2-LI*iv.eye(9))
    # Frobenius tensor bound: ||Btilde(v,v)/2||2 <= ||Btilde||F ||v||2^2/2.
    BT=[iv.matrix([[B[i][j][k] for k in range(9)] for j in range(9)]) for i in range(9)]
    transformed=[Si.T*M*Si for M in BT];sq=iv.mpf(0)
    for i in range(9):
        for j in range(9):
            for k in range(9):
                val=sum((S[i,l]*transformed[l][j,k] for l in range(9)),iv.mpf(0));sq+=abs(val)**2
    K=iv.sqrt(sq)/2;Kup=iv.mpf(str(float(K.b)*1.000001));assert Kup.a>K.b
    R=iv.mpf('1e-10')
    proposed=float((LI/(4*Kup)).a)
    # Choose a simple decimal power radius, well within lambda/(4K).
    R=iv.mpf('1e'+str(int(np.floor(np.log10(proposed)))))
    lift=iv.matrix([[iv.mpf(P[i][j])*iv.mpf(float(a['scale'][j])) for j in range(9)] for i in range(12)])*Si
    phys=[iv.sqrt(sum((abs(lift[i,j])**2 for j in range(9)),iv.mpf(0))) for i in range(12)]
    assert R*Kup*2<LI
    assert all(iv.mpf(float(a['xstar'][i]))-R*phys[i]>0 for i in range(12))
    nS=iv.sqrt(sum((abs(S[i,j])**2 for i in range(9) for j in range(9)),iv.mpf(0)))
    out={'evidence':'I plus quadratic Lyapunov argument; not a pulse inclusion','coordinates':'v=S*(physical pool/complex displacement / a.scale)','S_exact_dyadics':[[float(v).hex() for v in row] for row in S0],'lambda':lam,'K_upper':str(Kup),'radius':str(R),'metric_decay_lower':str(LI-Kup*R),'strict_LDL_pivots':piv,'species_displacement_bounds':[str(R*v) for v in phys],'scaled_euclidean_preparation_radius_lower':str(R/nS),'formula':'Vdot<=-2 lambda r^2+2 K r^3; ||v||<=R invariant; r(t)<=r(0) exp(-(lambda-K R)t)'}
    np.savez(W/'sink_capture_metric.npz',S=S0)
    (W/'sink_capture_certificate.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
