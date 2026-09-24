"""Theorem curves and explicitly numerical PGF diagnostics, with saved data."""
from pathlib import Path
from fractions import Fraction as F
import json, math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp
from exact_source_checks import source, daughter

root=Path(__file__).resolve().parents[1]; pub=root/'publication'
(pub/'figures').mkdir(exist_ok=True)
plt.rcParams.update({'font.size':9,'axes.spines.top':False,'axes.spines.right':False,
                     'pdf.fonttype':42,'savefig.bbox':'tight'})
def floor(n,delta): return max(0,73/67*math.log(.765/(-math.expm1(math.log1p(-delta)/n))))
def upper(n,delta): return 58/21*math.log(10.765*n/delta)
rows=[]
for n in [1,10,100,1000000]:
    rows.append(dict(n=n,necessary=floor(n,.01),sufficient=upper(n,.01),T=upper(n,.01)/.29))
(pub/'budget_rows.tex').write_text('\\begin{tabular}{rrrr}\n\\toprule\n$n$ & Necessary $B$ & Sufficient $B$ & Sufficient $T$\\\\\n\\midrule\n'+'\n'.join(f"{r['n']:,} & {r['necessary']:.6f} & {r['sufficient']:.6f} & {r['T']:.6f} \\\\" for r in rows)+'\n\\bottomrule\n\\end{tabular}\n')
fig,ax=plt.subplots(figsize=(6.7,3.35))
nn=np.logspace(0,6,100)
for delta,col in [(.01,'#155F83'),(.1,'#BD5B22')]:
    lo=[floor(n,delta) for n in nn]; hi=[upper(n,delta) for n in nn]
    ax.plot(nn,lo,color=col,label=f'Necessary, risk {delta:g}')
    ax.plot(nn,hi,'--',color=col,label=f'Achievable, risk {delta:g}')
    ax.fill_between(nn,lo,hi,color=col,alpha=.05)
ax.set_xscale('log');ax.set_xlabel('Number of AA founders, n');ax.set_ylabel('Reaction exposure B (dimensionless)')
ax.legend(ncol=2,frameon=False,loc='upper left');ax.grid(alpha=.15)
fig.tight_layout();fig.savefig(pub/'figures/budget.pdf');plt.close(fig)

d=np.array([.3,.3,.3,.01,.3,.01])
def flow(e,t,z):
    if not t:return np.array(z)
    Q=np.array(source(F(str(e)))[0],float)
    def fun(t,x):return Q@x+d*(1-x)+.1*(np.array(daughter(x,x),float)-x)
    sol=solve_ivp(fun,(0,t),z,rtol=2e-11,atol=2e-13)
    assert sol.success
    return sol.y[:,-1]
qoff=np.zeros(6);H=np.diag(d+.1)-np.array(source(F('.01'))[0],float)
for _ in range(20000):
    nxt=np.linalg.solve(H,d+.1*np.array(daughter(qoff,qoff),float))
    if max(abs(nxt-qoff))<1e-14:break
    qoff=nxt
BB=np.linspace(0,20,21); curves={name:[] for name in ['early','late','spread']}
for B in BB:
    t=B/.29
    curves['early'].append(1-flow(.3,t,flow(.01,100-t,np.zeros(6)))[5])
    curves['late'].append(1-flow(.01,100-t,flow(.3,t,np.zeros(6)))[5])
    curves['spread'].append(1-flow(.01+B/100,100,np.zeros(6))[5])
off={
 'Background retained':1-flow(.3,40,flow(.01,60,qoff)),
 'Full off at 100':1-flow(.3,40,flow(.01,60,np.full(6,.1))),
 'Full off at 40':1-flow(.3,40,np.full(6,.1))}
fig,axs=plt.subplots(1,2,figsize=(7.1,3.25),gridspec_kw={'width_ratios':[1.15,1]})
for name,col in zip(curves,['#155F83','#BD5B22','#777777']):
    axs[0].plot(BB,curves[name],color=col,label=name.capitalize())
cert=json.loads((pub/'validated_policy.json').read_text())
axs[0].scatter([11.6],[float(F(cert['survival_AA_upper']))],marker='D',color='black',s=22,label='Certified upper')
axs[0].axhline(.01,color='black',ls=':',lw=.8);axs[0].set_yscale('log')
axs[0].set_xlabel('Reaction exposure B');axs[0].set_ylabel('Survival risk at time 100')
axs[0].legend(frameon=False,fontsize=7);axs[0].grid(alpha=.15)
for j,(name,vals) in enumerate(off.items()):
    axs[1].bar(np.array([0,1])+(j-1)*.24,[vals[5],vals[2]],width=.22,label=name)
axs[1].set_xticks([0,1],['AA founder','RR founder']);axs[1].set_ylabel('Eventual survival risk')
axs[1].set_yscale('log');axs[1].legend(frameon=False,fontsize=7,loc='upper left')
axs[1].set_ylim(.0001,.15);axs[1].grid(axis='y',alpha=.15)
fig.tight_layout();fig.savefig(pub/'figures/policy.pdf');plt.close(fig)
data=dict(budget_table=rows,curve_exposure=BB.tolist(),curve_evidence='N only',curves=curves,
          off_comparison={k:v.tolist() for k,v in off.items()},qoff=qoff.tolist())
(pub/'figure_data.json').write_text(json.dumps(data,indent=2))
print(json.dumps(dict(budget_table=rows,off_comparison=data['off_comparison']),indent=2))
