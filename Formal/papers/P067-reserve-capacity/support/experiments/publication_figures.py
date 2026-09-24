"""Produce three publication figures and all underlying data; no stochastic simulation."""
from postproof import *
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap,BoundaryNorm
from matplotlib.patches import Patch
from scipy.sparse import diags
from math import log,ceil,floor

OUT=P/'publication/figures';OUT.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.titlesize':10,'axes.labelsize':9,'legend.fontsize':8,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42,'savefig.bbox':'tight'})
BLUE='#185e83';ORANGE='#c76c2f';GREEN='#36785b';GRAY='#5d6470'

def save(fig,name):
    fig.savefig(OUT/(name+'.pdf'));fig.savefig(OUT/(name+'.png'),dpi=180);plt.close(fig)

def curve():
    K=400;hmin=200;H0=278;r=1.;sigma=2.;nu=.005
    hs=np.arange(hmin,K+1);birth=r*hs*(1-hs/K)
    def concentration(t):return .29*(-np.expm1(-t)) if t<=112 else .29*(-np.expm1(-112))*np.exp(-(t-112))
    def rhs(t,y):
        mortality=((.3+concentration(t))/sigma+nu)*hs
        f=-(birth+mortality)*y[:-1]
        f[1:]+=birth[:-1]*y[:-2];f[:-1]+=mortality[1:]*y[1:-1]
        return np.r_[f,mortality[0]*y[0]]
    # Conservative sparse Jacobian pattern for the tridiagonal chain plus absorbing loss.
    pattern=diags([np.ones(len(hs)),np.ones(len(hs)+1),np.ones(len(hs))],[-1,0,1],shape=(len(hs)+1,len(hs)+1)).tolil();pattern[-1,0]=1
    t=np.unique(np.r_[np.linspace(0,8,65),np.linspace(8,112,105),np.linspace(112,120,65)])
    y0=np.zeros(len(hs)+1);y0[H0-hmin]=1
    sol1=solve_ivp(rhs,(0,112),y0,method='BDF',rtol=2e-9,atol=2e-15,t_eval=t[t<=112],jac_sparsity=pattern.tocsr())
    sol2=solve_ivp(rhs,(112,120),sol1.y[:,-1],method='BDF',rtol=2e-9,atol=2e-15,t_eval=t[t>112],jac_sparsity=pattern.tocsr())
    assert sol1.success and sol2.success
    y=np.concatenate([sol1.y,sol2.y],axis=1);risk=y[-1];means=hs@y[:-1] # killed expectation, used only internally
    assert risk.min()>-1e-12 and abs(y.sum(axis=0)-1).max()<1e-8
    concentrations=np.array([concentration(s) for s in t]);bound=float(anchor(400,200,278,1,F(61,200),1,False))*t
    fig,ax=plt.subplots(2,1,figsize=(6.4,4.6),sharex=True,layout='constrained')
    ax[0].step([0,112,112,120],[.29,.29,0,0],where='post',label='Administration $a(t)$',color=GRAY,ls='--')
    ax[0].plot(t,concentrations,label='Concentration / effect $c(t)$',color=BLUE)
    ax[0].fill_between([4,112],[.28,.28],[.30,.30],color=GREEN,alpha=.14,label='Certified effect band on [4, 112]')
    ax[0].set(ylabel='Effect-normalized rate',ylim=(-.01,.34),title='(a) Finite administration with a real washout tail')
    ax[0].legend(loc='lower left',ncol=1,frameon=False)
    valid=t>0
    ax[1].semilogy(t[valid],np.maximum(risk[valid],1e-16),color=BLUE,label='Killed-chain path risk (numerical)')
    ax[1].semilogy(t[valid],bound[valid],color=ORANGE,ls='--',label='Uniform proved product bound')
    ax[1].set(xlabel='Time (synthetic units)',ylabel='Reserve-loss probability',ylim=(1e-12,2e-5),title='(b) $K=400$, threshold 200, initial count 278')
    ax[1].legend(loc='lower right',frameon=False)
    save(fig,'delivered_course')
    return dict(t=t.tolist(),concentration=concentrations.tolist(),risk_N=risk.tolist(),bound_E_display=bound.tolist(),nominal=dict(K=K,hmin=hmin,H0=H0,r=r,sigma=sigma,nu=nu),numerical_method='BDF absorbing-loss forward equation, rtol=2e-9 atol=2e-15')

def best_simple(K,hmin,r,m,T):
    logprod=0.;best=(float('inf'),hmin)
    for M in range(hmin,K+1):
        val=log(M*float(m)*T)+logprod
        if val<best[0]:best=(val,M)
        if M<K:logprod+=log(K*float(m)/(float(r)*(K-M)))
    M=best[1]
    return anchor(K,hmin,M,r,m,T,False),M

def design_map():
    Ks=list(range(20,421,20));rs=[F(j,50) for j in range(1,102,2)]
    grid=np.ones((len(rs),len(Ks)),int);records=[]
    for a,r in enumerate(rs):
        for b,K in enumerate(Ks):
            hmin=K//2;cert,M=best_simple(K,hmin,r,F(61,200),120)
            status=2 if cert<F(1,100) else 1
            if r<F(3,20):
                x=(F(3,20)-r)*120;lower=sum(x**j/factorial(j) for j in range(31))
                if F(K,hmin)/lower<F(99,100):status=0
            grid[a,b]=status
            records.append(dict(K=K,r=str(r),M=M,healthy_bound_E=str(cert),status=['baseline_unsafe','unclassified','sufficient'][status]))
    fig,ax=plt.subplots(figsize=(6.4,3.6),layout='constrained')
    cmap=ListedColormap(['#d8b6af','#eee9dd','#91bfd0'])
    ax.pcolormesh(Ks,list(map(float,rs)),grid,cmap=cmap,vmin=0,vmax=2,shading='nearest',rasterized=True)
    ax.plot(400,1,'*',color='#143447',ms=12,label='Published robust witness')
    ax.set(xlabel='Healthy capacity $K$ (distinct units)',ylabel=r'Effective renewal $r_{\mathrm{eff}}$',title=r'Half-capacity threshold; $\sigma=2$, $T=120$')
    handles=[Patch(facecolor=cmap(i),label=l) for i,l in enumerate(['Baseline unsafe','Unclassified','Certified sufficient'])]
    handles.append(ax.get_legend_handles_labels()[0][0]);ax.legend(handles=handles,loc='upper left',frameon=True,fontsize=8)
    save(fig,'capacity_design_map')
    return records

def scaling():
    rows=[]
    for K in range(20,501,10):
        r=F(1);m=F(61,200);hmin=(K+1)//2;M=floor(K*(1-float(m)))
        if M<hmin:continue
        val=anchor(K,hmin,M,r,m,120,False)
        theta=.5;a=float(m);f=log((1-theta)/a);I=(1-theta)*f-(1-theta)+a
        action=K*a*120*np.exp(-K*I+2*f)
        rows.append(dict(K=K,M=M,finite_E=str(val),action_display=action))
    init=[];K=400;hmin=200;M=278;prod=F(1);ps=[prod]
    for h in range(hmin,M):prod*=F(122,400-h);ps.append(prod)
    denom=sum(ps);course=anchor(K,hmin,M,1,F(61,200),120)
    for h0 in range(200,401,2):
        p=F(0) if h0>=M else sum(ps[h0-(hmin-1):])/denom
        init.append(dict(h0=h0,initial_term_E=str(p),total_bound_E=str(min(F(1),p+course))))
    fig,ax=plt.subplots(1,2,figsize=(6.4,3.15),layout='constrained')
    ax[0].semilogy([x['K'] for x in rows],[min(1,float(F(x['finite_E']))) for x in rows],color=BLUE,label='Finite product')
    ax[0].semilogy([x['K'] for x in rows],[min(1,x['action_display']) for x in rows],color=ORANGE,ls='--',label='Action + rounding bound')
    ax[0].axhline(.01,color=GRAY,lw=.8,ls=':');ax[0].set(xlabel='Capacity $K$',ylabel='Reserve-loss upper bound',title='(a) Finite renewal $r=1$')
    ax[0].legend(frameon=False,loc='lower left')
    ax[1].semilogy([x['h0'] for x in init],[float(F(x['total_bound_E'])) for x in init],color=BLUE)
    ax[1].axvline(278,color=ORANGE,ls='--',lw=1);ax[1].axhline(.01,color=GRAY,lw=.8,ls=':')
    ax[1].set(xlabel='Initial healthy count $h_0$',title='(b) Initial filling, $K=400$',ylim=(1e-6,1))
    save(fig,'capacity_and_filling')
    return dict(capacity=rows,initial=init)

if __name__=='__main__':
    data=dict(course=curve(),design_map=design_map(),scaling=scaling())
    (P/'results/publication_figures.json').write_text(json.dumps(data,indent=2))
    print('Saved three figures and source data. Nominal final path risk:',data['course']['risk_N'][-1])
