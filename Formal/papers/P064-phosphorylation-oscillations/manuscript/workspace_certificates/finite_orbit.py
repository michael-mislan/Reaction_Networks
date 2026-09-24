"""Bounded phase-fixed collocation and variational shooting. N evidence only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json
import numpy as np
from scipy.integrate import solve_bvp, solve_ivp
import preparation_pilot as p
P=Path(__file__).resolve().parent
xstar=np.array([2,12,.2,.4,2.3,.4,.46,.3,1.7,23,.18,4.])
qflux=np.array([.1,6.4,1.2])
p.X[:]=xstar;p.QF[:]=qflux
L=p.lift(); RN=p.RCH@p.N
def model(r,rate_scale=None,ft=0):
    ratios=np.array([.01,.01,.01,r,.01,.01])
    rates=np.empty(18)
    rates[0::3]=(1+ratios)*qflux[p.ARM]/xstar[p.LEVEL]/xstar[4+p.EN]
    rates[1::3]=ratios*qflux[p.ARM]/xstar[6:]
    rates[2::3]=qflux[p.ARM]/xstar[6:]
    if rate_scale:
        for k,v in rate_scale.items():rates[int(k)]*=v
    base=xstar.copy();base[5]+=ft
    def f(y):
        x=base[:,None]+L@y if y.ndim==2 else base+L@y
        v=np.empty((18,y.shape[1])) if y.ndim==2 else np.empty(18)
        v[0::3]=rates[0::3,None]*x[p.LEVEL]*x[4+p.EN] if y.ndim==2 else rates[0::3]*x[p.LEVEL]*x[4+p.EN]
        v[1::3]=rates[1::3,None]*x[6:] if y.ndim==2 else rates[1::3]*x[6:]
        v[2::3]=rates[2::3,None]*x[6:] if y.ndim==2 else rates[2::3]*x[6:]
        return RN@v
    def jac(y):
        x=base+L@y
        D=np.zeros((18,12))
        for j in range(6):
            D[3*j,p.LEVEL[j]]=rates[3*j]*x[4+p.EN[j]]
            D[3*j,4+p.EN[j]]=rates[3*j]*x[p.LEVEL[j]]
            D[3*j+1,6+j]=rates[3*j+1];D[3*j+2,6+j]=rates[3*j+2]
        return RN@D@L
    return f,jac,base,rates
def shoot_diagnostics(sol,f,jac):
    y0=sol.y[:,0];period=sol.p[0]
    def aug(t,z):return np.r_[f(z[:9]),(jac(z[:9])@z[9:].reshape(9,9)).ravel()]
    iv=solve_ivp(aug,[0,period],np.r_[y0,np.eye(9).ravel()],method='DOP853',rtol=2e-11,atol=2e-12,dense_output=True)
    M=iv.y[9:,-1].reshape(9,9);evals=np.linalg.eigvals(M)
    phase=f(y0);phase/=np.linalg.norm(phase)
    A=np.block([[M-np.eye(9),f(iv.y[:9,-1])[:,None]],[phase[None,:],np.zeros((1,1))]])
    resid=np.r_[iv.y[:9,-1]-y0,0.]
    rest=np.delete(evals,np.argmin(abs(evals-1)))
    samples=iv.sol(np.linspace(0,period,801))[:9]
    return dict(period=float(period),shooting_residual=float(np.max(abs(resid))),phase_fixed_inverse_norm=float(np.linalg.norm(np.linalg.inv(A),np.inf)),newton_correction=float(np.linalg.norm(np.linalg.solve(A,resid),np.inf)),multipliers=[[float(v.real),float(v.imag)] for v in evals],nontrivial_radius=float(max(abs(rest))),radial_recovery=float(-np.log(max(abs(rest)))/period),y0=y0.tolist(),samples=samples.tolist(),jacobian_norm_max=float(max(np.linalg.norm(jac(v),np.inf) for v in samples.T))),iv
def main():
    hopf,(v,ell)=p.hopf_pilot(1,1,(1.4,1.5))
    out={'evidence':'N: floating collocation and variational integration; no validated flow enclosure','hopf':hopf,'branch':[],'physical_probes':[]}
    prev=None
    for r in [1.42,1.4,1.35,1.325,1.3]:
        f,jac,base,rates=model(r)
        if prev is None:
            t=np.linspace(0,1,181);amp=np.sqrt((-hopf['crossing'][0])*(hopf['r']-r)/(-hopf['omega']*hopf['l1']))
            guess=2*amp*np.real(v[:,None]*np.exp(2j*np.pi*t));per=2*np.pi/hopf['omega']
        else:t=prev.x;guess=prev.y;per=prev.p[0]
        anchor=guess[:,0].copy();phase=f(anchor);phase/=np.linalg.norm(phase)
        sol=solve_bvp(lambda t,y,T:T[0]*f(y),lambda a,b,T:np.r_[a-b,phase@(a-anchor)],t,guess,p=[per],tol=1e-7,max_nodes=9000)
        if not sol.success:raise RuntimeError(sol.message)
        diag,iv=shoot_diagnostics(sol,f,jac)
        samples=np.array(diag.pop('samples'));x=base[:,None]+L@samples
        diag.update(r=r,min_species=float(x.min()),free_S3_amplitude=float(np.ptp(x[3])),total_S3_amplitude=float(np.ptp(x[3]+x[11])),D1_amplitude=float(np.ptp(x[9])),fuel=float(np.trapezoid(sum(rates[3*j+2]*x[6+j] for j in range(3)),np.linspace(0,diag['period'],801))),collocation_nodes=len(sol.x))
        out['branch'].append(diag);print(json.dumps(diag),flush=True)
        np.savez(P/f'orbit_r{str(r).replace(".","p")}.npz',phase=np.linspace(0,1,801),x=x,y=samples)
        prev=sol
        if r==1.4:chosen=sol
    # Independent physical changes at r=1.4; equilibrium is not reconstructed.
    for name,scales,ft in [('F_total_minus_1pct',None,-.2758),('F_total_plus_1pct',None,.2758),('c2_minus_1pct',{5:.99},0),('c2_plus_1pct',{5:1.01},0),('alpha1_minus_1pct',{9:.99},0),('alpha1_plus_1pct',{9:1.01},0)]:
        f,jac,base,rates=model(1.4,scales,ft)
        anchor=chosen.y[:,0];phase=f(anchor);phase/=np.linalg.norm(phase)
        sol=solve_bvp(lambda t,y,T:T[0]*f(y),lambda a,b,T:np.r_[a-b,phase@(a-anchor)],chosen.x,chosen.y,p=chosen.p,tol=1e-7,max_nodes=6000)
        row={'name':name,'success':sol.success,'message':sol.message}
        if sol.success:
            diag,_=shoot_diagnostics(sol,f,jac);x=base[:,None]+L@np.array(diag.pop('samples'))
            diag.update(min_species=float(x.min()),free_S3_amplitude=float(np.ptp(x[3])))
            row.update(diag)
        out['physical_probes'].append(row);print(name,row.get('free_S3_amplitude'),flush=True)
    # Local radial gap versus scalar Gronwall enclosure: interval overflow is a route failure, not nonexistence.
    (P/'finite_orbit_results.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()
