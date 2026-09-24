"""Exact postproof certificates and bounded diagnostics. One BLAS thread."""
from pilot import *
from scipy.optimize import linprog

def anchor(K,hmin,M,r,m,T,denominator=True):
    r,m,T=map(F,(r,m,T)); product=F(1); denom=F(1)
    for h in range(hmin,M):
        product*=K*m/(r*(K-h));denom+=product
    return M*m*T*product/(denom if denominator else 1)

def coefficient(K,hmin,r,m,T,h0=None):
    p=np.eye(K-hmin+1)[(K if h0 is None else h0)-hmin]
    B=np.zeros((len(p),len(p)));loss=np.zeros(len(p));loss[0]=m*hmin
    for i,h in enumerate(range(hmin,K+1)):
        lam=r*h*(1-h/K);mu=m*h
        B[i,i]=-lam-mu
        if i>0:B[i,i-1]=mu
        if h<K:B[i,i+1]=lam
    # Absorbing loss column avoids subtracting nearly equal probabilities.
    C=np.zeros((len(p)+1,len(p)+1));C[:-1,:-1]=B;C[:-1,-1]=loss
    return float((np.r_[p,0]@expm(C*T))[-1])

def converse_pilot():
    # V=e^{-eta(T-t)} f(h)(1-q^z), after healthy failure use lambda.
    # G(1-q^z)>=-(67/73*v+k)(1-q^z) for the actual nominal source.
    T=120.;K=20;hmin=10;w0=1-.235**4;rows=[]
    for r in [4.,4.5,5.]:
        baseline=min((anchor(K,hmin,M,F(str(r)),F(3,10),120),M) for M in range(hmin,K+1))
        for eta in [0,.005,.01,.02,.04,.08]:
            constraints=[];labels=[]
            for v,k in [(0,0),(.3,0),(0,.1),(.3,.1)]:
                for h in range(hmin,K+1):
                    i=h-hmin;z=np.zeros(K-hmin+2)
                    lam=r*h*(1-h/K);mu=(.3+v+k)*h
                    z[i]=eta-67/73*v-k-lam-mu
                    if h<K:z[i+1]+=lam
                    z[i-1 if h>hmin else -1]+=mu
                    constraints.append(-z);labels.append([h,v,k])
            objective=np.r_[-w0*np.exp(-eta*T)*np.eye(K-hmin+1)[-1],.01]
            sol=linprog(objective,A_ub=constraints,b_ub=np.zeros(len(constraints)),bounds=[(0,1)]*(K-hmin+1)+[(0,100)],method='highs')
            assert sol.success
            active=np.argsort(np.array(constraints)@sol.x)[-5:]
            normalized=linprog(np.r_[np.zeros(K-hmin+1),1.],A_ub=constraints,b_ub=np.zeros(len(constraints)),bounds=[(0,1)]*(K-hmin)+[(1,1),(0,10**7)],method='highs')
            diag={'status':normalized.message}
            if normalized.success:
                slack=-np.array(constraints)@normalized.x
                diag.update(lambda_value=float(normalized.x[-1]),margin=float(w0*np.exp(-eta*T)-.01*normalized.x[-1]),active_rows=[labels[i] for i in np.argsort(slack)[:5]])
            rows.append(dict(r=r,eta=eta,baseline_bound_E=str(baseline[0]),baseline_anchor=baseline[1],lower_minus_alpha_lambda_N=-sol.fun,certificate_f_N=sol.x.tolist(),active_rows=[labels[i] for i in active],normalized_diagnostic=diag))
    return rows

def main():
    w=list(map(F,[14,11,10,84,43,107]));checks=[]
    for e in ['.01','.29','.31']:
        Q,d,pairs,A=source(e)
        drift=[sum(A[i][j]*w[j] for j in range(6))/w[i] for i in range(6)]
        env=[(sum(Q[i][j]*abs(w[j]-w[i]) for j in range(6) if j!=i)+F(1,10)*abs(sum(p*(w[j]+w[k]) for j,k,p in pairs[i])-w[i])+d[i]*w[i])/w[i] for i in range(6)]
        assert max(drift)<=F(67,500) and max(env)<=F(27,20)
        if e!='.01':assert max(drift)<=-F(99,1000)
        checks.append(dict(e=e,drift=list(map(str,drift)),relative_envelope=list(map(str,env))))
    simple=anchor(400,200,278,1,F(61,200),120,False)
    exact=anchor(400,200,278,1,F(61,200),120)
    assert simple<F(7,10**6)
    old9=anchor(20,10,20,9,F(61,100),120,False)
    assert old9<F(8452,10**6)<F(1,100)
    taylor=sum(F(43,5)**j/factorial(j) for j in range(31))
    assert taylor>5000
    assert 108*(F(99,1000)-F(27,2000))-4*(F(67,500)+F(27,2000))==F(2161,250)>F(43,5)
    assert sum(F(447,25)**j/factorial(j) for j in range(41))>20000000
    result=dict(evidence='E in exact, N in diagnostics',exact=dict(source_rows=checks,anchored_simple=str(simple),anchored_simple_display=float(simple),anchored_with_denominator=str(exact),anchored_denominator_display=float(exact),old_r9=str(old9),old_r9_display=float(old9),exp86_taylor=str(taylor),target_upper='107/12500',joint_success_lower='991433/1000000'),converse_pilot=converse_pilot(),coefficient_pilot=[dict(K=4,hmin=2,r=r,risk=coefficient(4,2,r,.5,2),scaled=r*r*coefficient(4,2,r,.5,2),predicted_limit=8) for r in [8,16,32,64,128]],initial_pilot=[dict(h0=h,r=r,risk=coefficient(4,2,r,.5,2,h),predicted_power=min(2,h-1)) for h in [2,3,4] for r in [16,32,64]],matched_inheritance={str(ind):cancer([(.126,0,100)],ind) for ind in [False,True]})
    (P/'results/postproof.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({'anchored_bound':float(simple),'r9_bound':float(old9),'max_converse_objective':max(x['lower_minus_alpha_lambda_N'] for x in result['converse_pilot']),'baseline_bounds':[(r['r'],float(F(r['baseline_bound_E']))) for r in result['converse_pilot'][::6]],'coefficient':result['coefficient_pilot']},indent=2))

if __name__=='__main__':main()
