"""Literal seven-type source. All action inputs convertible to exact Fraction."""
from fractions import Fraction as F
from math import comb
import numpy as np

STATES=[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)]
PAIRS=[]
for a,r in STATES:
    PAIRS.append([(STATES.index((i,j)),STATES.index((a-i,r-j)),F(comb(a,i)*comb(r,j),2**(a+r))) for i in range(a+1) for j in range(r+1)])
L=[[sum((p for j,k,p in row if j==c),F(0)) for c in range(6)] for row in PAIRS]
INDEPENDENT=[[(j,k,L[i][j]*L[i][k]) for j in range(6) for k in range(6) if L[i][j]*L[i][k]] for i in range(6)]
D0=list(map(F,['.3','.3','.3','.01','.3','.01']))
KAPPA=list(map(F,['.1','.1','.1','.4','.1','.4']))

def exact_source(e=F('.3'),c=F(0),eps=F('.1'),law='J',bm=F('.1'),dm=F('.02')):
    e,c,eps,bm,dm=map(F,[e,c,eps,bm,dm]); assert e>=0 and c>=0 and bm>=0 and dm>=0
    mu=[eps*k for k in KAPPA]; assert all(0<=u<=1 for u in mu)
    Q=[[F(0) for _ in range(6)] for _ in range(6)]
    for i,(a,r) in enumerate(STATES):
        un=2-a-r
        for dst,rate in [((a+1,r),un*(F('.01')+F(a,2))),((a,r+1),un*(F('.01')+F(r,2))),((a-1,r),a*(e+F(r,4))),((a,r-1),r*(e+F(a,4)))]:
            if rate:
                j=STATES.index(dst); Q[i][j]+=rate; Q[i][i]-=rate
    # f(z)=constant+linear*z+sum quadratic coefficient*z_j*z_k.
    deaths=[d+c for d in D0]+[dm]
    lin=[Q[i]+[F(0)] for i in range(6)]+[[F(0)]*7]
    quad=[]
    kernel=PAIRS if law=='J' else INDEPENDENT
    for i in range(6):
        lin[i][i]-=deaths[i]+F('.1')
        quad.append([(j,k,F('.1')*(1-mu[i])*p) for j,k,p in kernel[i]]+[(j,6,F('.1')*mu[i]*L[i][j]) for j in range(6) if L[i][j]])
    lin[6][6]=-dm-bm; quad.append([(6,6,bm)])
    return deaths,lin,quad

def floating(e=.3,c=0,eps=.1,law='J',bm=.1,dm=.02):
    d,B,C=exact_source(str(e),str(c),str(eps),law,str(bm),str(dm))
    d=np.array(d,dtype=float); B=np.array(B,dtype=float)
    C=[[(j,k,float(p)) for j,k,p in row] for row in C]
    def rhs(t,z): return d+B@z+np.array([sum(p*z[j]*z[k] for j,k,p in row) for row in C])
    return rhs

def compose(phases,law='J',eps=.1,terminal=None):
    from scipy.integrate import solve_ivp
    z=np.r_[np.ones(6),.2] if terminal is None else np.array(terminal,dtype=float)
    for e,c,t in reversed(phases):
        sol=solve_ivp(floating(e,c,eps,law),(0,t),z,method='DOP853',rtol=2e-12,atol=2e-14)
        assert sol.success; z=sol.y[:,-1]
    return z

def no_appearance(phases,law='J',eps=.1):
    from scipy.integrate import solve_ivp
    z=np.ones(6)
    for e,c,t in reversed(phases):
        d,B,C=exact_source(str(e),str(c),str(eps),law)
        d=np.array(d[:6],float);B=np.array(B,float)[:6,:6]
        C=[[(j,k,float(p)) for j,k,p in row if j<6 and k<6] for row in C[:6]]
        def rhs(t,x):return d+B@x+np.array([sum(p*x[j]*x[k] for j,k,p in row) for row in C])
        sol=solve_ivp(rhs,(0,t),z,method='DOP853',rtol=2e-12,atol=2e-14)
        assert sol.success;z=sol.y[:,-1]
    return z

def exact_checks():
    for i,row in enumerate(PAIRS):
        assert sum(p for j,k,p in row)==1
        assert all(tuple(STATES[j][s]+STATES[k][s] for s in range(2))==STATES[i] for j,k,p in row)
        assert all(sum(p for j,k,p in row if k==c)==L[i][c] for c in range(6))
        assert all(sum(p for j,k,p in INDEPENDENT[i] if j==c)==L[i][c] for c in range(6))
    means=[]
    for law in ['J','I']:
        d,B,C=exact_source(law=law)
        assert all(d[i]+sum(B[i])+sum(p for j,k,p in C[i])==0 for i in range(7))
        A=[row[:] for row in B]
        for i in range(7):
            for j,k,p in C[i]: A[i][j]+=p; A[i][k]+=p
        means.append(A)
    assert means[0]==means[1]
    # Jacobian at 1 equals the augmented mean, with positive sign.
    return dict(normalized=True,complementarity=True,common_marginals=True,common_augmented_mean=True,linearization_sign='+A',augmented_mean=[[str(v) for v in r] for r in means[0]])
