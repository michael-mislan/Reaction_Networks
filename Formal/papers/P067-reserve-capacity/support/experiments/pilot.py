"""Small deterministic-source experiments; N unless explicitly rational E."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial, exp
import json
import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import expm
P=Path(__file__).resolve().parents[1]
STATES=[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)]

def source(e,k=0,independent=False):
    e,k=F(str(e)),F(str(k))
    Q=[[F(0) for _ in STATES] for _ in STATES]
    pairs=[]
    for x,(a,r) in enumerate(STATES):
        s=2-a-r
        for target,rate in [((a+1,r),s*(F(1,100)+F(a,2))),((a,r+1),s*(F(1,100)+F(r,2))),((a-1,r),a*(e+F(r,4))),((a,r-1),r*(e+F(a,4)))]:
            if rate:
                y=STATES.index(target); Q[x][y]+=rate; Q[x][x]-=rate
        row=[]
        for i in range(a+1):
            for j in range(r+1):
                row.append((STATES.index((i,j)),STATES.index((a-i,r-j)),F(comb(a,i)*comb(r,j),2**(a+r))))
        assert sum(p for _,_,p in row)==1
        if independent:
            marginal=[sum(p for i,j,p in row if i==y) for y in range(6)]
            row=[(i,j,marginal[i]*marginal[j]) for i in range(6) for j in range(6) if marginal[i]*marginal[j]]
        pairs.append(row)
    d=[(F(1,100) if a>r else F(3,10))+k for a,r in STATES]
    L=[[sum(p*((i==y)+(j==y)) for i,j,p in row) for y in range(6)] for row in pairs]
    A=[[Q[x][y]+F(1,10)*(L[x][y]-(x==y))-d[x]*(x==y) for y in range(6)] for x in range(6)]
    assert all(sum(row)==0 for row in Q)
    assert all(sum(row)==2 for row in L)
    return Q,d,pairs,A

def phi(e,x,k=0,independent=False):
    Q,d,pairs,A=source(e,k,independent)
    return [sum(Q[i][j]*x[j] for j in range(6))+d[i]*(1-x[i])+F(1,10)*(sum(p*x[j]*x[l] for j,l,p in pairs[i])-x[i]) for i in range(6)]

def cancer(phases,independent=False):
    q=np.zeros(6); M=np.eye(6)
    for e,k,t in reversed(phases):
        Q,d,pairs,A=source(e,k,independent)
        Q=np.array(Q,float);d=np.array(d,float)
        def rhs(t,x):
            offspring=np.array([sum(float(p)*x[j]*x[l] for j,l,p in row) for row in pairs])
            return Q@x+d*(1-x)+.1*(offspring-x)
        sol=solve_ivp(rhs,(0,t),q,rtol=2e-10,atol=2e-12)
        assert sol.success
        q=sol.y[:,-1]
    for e,k,t in phases:
        M=M@expm(np.array(source(e,k)[3],float)*t)
    return dict(single_survival=(1-q).tolist(),four_AA_survival=float(1-q[5]**4),four_AA_mean=float(4*(M@np.ones(6))[5]))

def healthy(phases,r,sigma=1,K=20,hmin=10):
    p=np.eye(K-hmin+1)[-1]; full=np.eye(K+1)[-1]
    for e,k,t in phases:
        mu=(.3+e-.01+k)/sigma
        B=np.zeros((K+1,K+1))
        for h in range(1,K+1):
            birth=r*h*(1-h/K);death=mu*h
            B[h,h]=-birth-death;B[h,h-1]=death
            if h<K:B[h,h+1]=birth
        p=p@expm(B[hmin:,hmin:]*t)
        full=full@expm(B*t)
    return dict(path_risk=float(1-p.sum()),terminal_risk=float(full[:hmin].sum()),mean=float(full@np.arange(K+1)))

def clock(n,m,h,sigma):
    ans=F(0)
    for j in range(n+1):
        term=F(1)
        for ell in range(sigma*j):term*=F(h+ell,m+1+ell)
        ans+=(-1)**j*comb(n,j)*term
    return ans

def exact():
    q=list(map(F,['.94','.982','.987','.27','.735','.235']))
    assert min(-x for x in phi('.01',q))>=F(1,5000)
    w=list(map(F,[14,11,10,84,43,107]))
    rows=[]
    for e in ['.29','.31']:
        A=source(e)[3]
        rows.append([-F(9,100)*w[i]-sum(A[i][j]*w[j] for j in range(6)) for i in range(6)])
    assert min(x for row in rows for x in row)==F(17,100)
    # Differentiate literal daughter polynomials at one: Q - dI + b(L-I).
    for e in ['.01','.3']:
        Q,d,pairs,A=source(e)
        J=[[Q[i][j]-d[i]*(i==j)+F(1,10)*(sum(p*((j==l)+(j==m)) for l,m,p in pairs[i])-(i==j)) for j in range(6)] for i in range(6)]
        assert J==A
    values={str(s):str(clock(4,20,10,s)) for s in [1,2,4,8,16]}
    assert values['1']=='13/138' and values['2']=='1618/4347'
    mu=F(61,100);r=F(12);T=F(100)
    upper=20*mu*T*(20*mu/r)**10/factorial(10)
    assert upper<F(1,1000)
    return dict(evidence='E',clock=values,source_drift_slacks=[[str(x) for x in row] for row in rows],healthy_robust_bound=str(upper),healthy_robust_bound_float=float(upper))

if __name__=='__main__':
    result={'exact':exact(),'source_schedule_reproduction':cancer([(.3,0,40),(.01,0,60)])}
    assert abs(result['source_schedule_reproduction']['single_survival'][5]-.00981826421447)<1e-9
    schedules={'constant_full':[(.3,0,100)],'constant_matched':[(.126,0,100)],'early':[(.3,0,40),(.01,0,60)],'late':[(.01,0,60),(.3,0,40)],'two_courses':[(.3,0,20),(.01,0,30)]*2}
    result['schedules']={name:{'cancer':cancer(s),'healthy_r2':healthy(s,2),'healthy_r12':healthy(s,12)} for name,s in schedules.items()}
    result['continuation']=[dict(r=r,sigma=s,**healthy(schedules['constant_full'],r,s)) for s in [1,2,4] for r in [0,.5,1,2,4,8,12]]
    result['baseline']={str(r):healthy([(.01,0,100)],r) for r in [0,2,12]}
    result['sister']={name:cancer(s,True) for name,s in schedules.items()}
    result['preparation']={str(t):{str(e):cancer([(e,0,t)])['single_survival'] for e in [.01,.3]} for t in [.1,1,10]}
    result['scaling']=[dict(r=r,**healthy([(.3,0,10)],r,K=6,hmin=4)) for r in [4,8,16,32,64]]
    result['evidence']='N except exact block. Source has stipulated baseline mortality; no clinical calibration.'
    (P/'results/pilot.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({'exact':result['exact'],'schedules':result['schedules'],'scaling':result['scaling']},indent=2))
