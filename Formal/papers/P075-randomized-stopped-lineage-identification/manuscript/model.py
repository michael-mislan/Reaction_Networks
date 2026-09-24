"""Self-contained source model, stopped observation law and branching ODE.
Synthetic rates in hours^-1 and hours; no biological data are fitted."""
import os
for _k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[_k]='1'
import numpy as np
from scipy.linalg import expm
from scipy.integrate import solve_ivp

E_MARKER=np.array([[.9,.15],[.1,.85]])   # columns S,T; rows Y=0,1
SEED=20260922

def model(qST=.18):
    """Two-state synthetic source; state 0 = S (sensitive), 1 = T (tolerant)."""
    return dict(pi=np.array([.65,.35]),q=np.array([[0.,qST],[.07,0.]]),
                b=np.array([.22,.16]),d=np.array([.12,.04]),
                K=np.array([[.62,.12,.12,.14],[.10,.10,.10,.70]]))

def generator(m):
    return m['q']-np.diag(m['q'].sum(1)+m['b']+m['d'])

def exp_law(m,lam,E=E_MARKER,tau=0.):
    """Randomized-deadline record law.  Returns (obs, H, R, F, E[sigma], division yield)."""
    H=generator(m); R=np.linalg.inv(lam*np.eye(2)-H); A=lam*R; S=expm(tau*H)
    F=np.vstack([E@S.T,(1-S.sum(1))[None,:]]) if tau else E
    B=np.column_stack([m['d'],m['b'][:,None]*m['K']])
    C=np.zeros((1+len(F)**2,5)); C[0,0]=1.; C[1:,1:]=np.kron(F,F)
    obs=np.column_stack([E@np.diag(m['pi'])@A@E.T,E@np.diag(m['pi'])@R@B@C.T])
    assert abs(obs.sum()-1)<1e-12
    return obs,H,R,F,float(m['pi']@R@np.ones(2)),float(m['pi']@R@m['b'])

def mean_generator(m,K=None):
    K=m['K'] if K is None else K
    L=np.column_stack([K[:,0]+K[:,1],K[:,2]+K[:,3]])
    return m['q']-np.diag(m['q'].sum(1)+m['b']+m['d'])+2*m['b'][:,None]*L

def extinction(m,eps,T=24.,npts=241):
    """Branching PGF ODE at z=0 for the base kernel and its concordance shift."""
    K0=m['K']; K1=K0+np.array(eps)[:,None]*np.array([1.,-1.,-1.,1.])
    assert K1.min()>=0, 'perturbed kernel leaves the simplex'
    assert np.abs(mean_generator(m,K0)-mean_generator(m,K1)).max()<1e-14
    grid=np.linspace(0,T,npts); curves=[]
    for K in (K0,K1):
        def rhs(_,f):
            pair=np.array([f[0]*f[0],f[0]*f[1],f[1]*f[0],f[1]*f[1]])
            return m['d']*(1-f)+m['q']@f-m['q'].sum(1)*f+m['b']*(K@pair-f)
        sol=solve_ivp(rhs,[0,T],[0.,0.],t_eval=grid,rtol=1e-10,atol=1e-12)
        curves.append(m['pi']@sol.y)
    means=np.array([m['pi']@expm(t*mean_generator(m,K0))@np.ones(2) for t in grid])
    return dict(time=grid,old=curves[0],new=curves[1],mean=means,
                gap_final=float(curves[1][-1]-curves[0][-1]))

def strong_source():
    m=model(.01); m['q'][1,0]=.01
    m['b']=np.array([.6,.4]); m['d']=np.array([.5,.005])
    m['K']=np.array([[.5625,.1875,.1875,.0625],[.0625,.1875,.1875,.5625]])
    return m

def simulate_counts(n=50000,ncal=100000,lam=1.,seed=SEED):
    """Reproduces the retained worked dataset: calibration draw, then both arms."""
    rng=np.random.default_rng(seed)
    cal=rng.binomial(ncal,[.1,.85])
    out=[]
    for qST in (.05,.85):
        obs=exp_law(model(qST),lam)[0]
        out.append(rng.multinomial(n,obs.flatten()).reshape(2,7))
    return tuple(cal),out

if __name__=='__main__':
    cal,arms=simulate_counts()
    print('calibration successes',cal)
    for name,c in zip(('untreated','treated'),arms):
        print(name,'J=',c[0,0],c[0,1],c[1,0],c[1,1],' initial Y0=1:',c[1].sum(),
              ' exits: 0->',c[0,2:].sum(),' 1->',c[1,2:].sum())
