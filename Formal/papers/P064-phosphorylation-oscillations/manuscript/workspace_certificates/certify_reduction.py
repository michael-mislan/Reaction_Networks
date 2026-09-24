"""Small exact rational common-Lyapunov certificates, not floating acceptance."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json
import numpy as np
import sympy as s
from scipy.linalg import solve_continuous_lyapunov
import preparation_pilot as p

def matrix(r,eps=s.Rational(1)):
    x=list(map(s.Rational,p.XQ));q=list(map(s.Rational,p.QFQ))
    rr=[s.Rational(1,100)]*6;rr[3]=r
    J=s.zeros(9)
    for j in range(6):
        lev=int(p.LEVEL[j]);v=(1+rr[j])*q[j%3]
        J[j%3,3+j]=(1 if j<3 else -1)*q[j%3]/x[6+j]
        for i in range(3):J[3+j,i]=v/x[lev]*int(p.T[lev,i])/eps
        for h in range(6):
            J[3+j,3+h]=(-(v/x[6+j] if j==h else 0)-v/x[lev]*int(p.LEVEL[h]==lev)-v/x[4+j//3]*int(h//3==j//3))/eps
    return J

def reduced(J):
    keep=[i for i in range(9) if i!=4] # remove only C2
    return J.extract(keep,keep)-J.extract(keep,[4])*J.extract([4],keep)/J[4,4]

def ldl_pivots(A):
    assert A==A.T
    B=A.copy();piv=[]
    for k in range(A.rows):
        d=B[k,k];piv.append(d)
        if d<=0:return None
        for i in range(k+1,A.rows):
            for j in range(i,A.rows):
                B[j,i]=B[i,j]=B[i,j]-B[i,k]*B[j,k]/d
    return piv

def rational_energy(J):
    a=np.array(J,float)
    P=solve_continuous_lyapunov(a.T,-np.eye(len(a)))
    return s.Matrix([[s.Rational(round(float(v)*10**10),10**10) for v in row] for row in (P+P.T)/2])

def run():
    # Pilot before interval-box enlargement; each successful endpoint is exact.
    out={'evidence':'I: exact rational LDL pivots; floating Lyapunov solution only proposes P','boxes':[]}
    for name,fun,rc,ec,rs,es in [
      ('full_relaxation',lambda j:j,s.Rational(28,100),s.Rational(7,10),[s.Rational(27,100),s.Rational(29,100)],[s.Rational(1,2),s.Rational(9,10)]),
      ('full_near_hopf',lambda j:j,s.Rational(28,100),s.Rational(1),[s.Rational(279,1000),s.Rational(281,1000)],[s.Rational(1)]),
      ('retain_all_except_C2',reduced,s.Rational(28,100),s.Rational(1),[s.Rational(279,1000),s.Rational(281,1000)],[s.Rational(1)])]:
        P=rational_energy(fun(matrix(rc,ec)))
        pp=ldl_pivots(P);assert pp
        vertices=[]
        for r in rs:
            for e in es:
                A=fun(matrix(r,e));Q=-(A.T*P+P*A)
                # Certify an explicit Euclidean dissipation floor, if available.
                piv=ldl_pivots(Q-s.eye(Q.rows)*s.Rational(1,100))
                vertices.append({'r':str(r),'epsilon':str(e),'pass':piv is not None,'pivots':[str(v) for v in piv] if piv else []})
        out['boxes'].append({'name':name,'P':[[str(v) for v in row] for row in P.tolist()],'P_pivots':[str(v) for v in pp],'q_lower':'1/100','vertices':vertices,'pass':all(v['pass'] for v in vertices),'P_norm_upper':str(max(sum(abs(P[i,j]) for j in range(P.cols)) for i in range(P.rows)))})
    Path(__file__).with_name('reduction_certificate.json').write_text(json.dumps(out,indent=2))
    print(json.dumps([{k:v for k,v in row.items() if k not in ['P','P_pivots','vertices']} for row in out['boxes']],indent=2))

if __name__=='__main__':run()
