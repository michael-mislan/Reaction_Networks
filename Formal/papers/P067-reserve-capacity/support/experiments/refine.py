"""Bounded root finding and exact certificate extraction, no parameter grid."""
from pilot import *
from scipy.optimize import brentq
from datetime import datetime, timezone

result={}
def taylor(e):
    Q,d,pairs,A=source(e)
    cs=[[F(0)]*6,d[:]]
    for n in range(1,4):
        cs.append([(sum(Q[i][j]*cs[n][j] for j in range(6))-(d[i]+F(1,10))*cs[n][i]+F(1,10)*sum(p*cs[t][j]*cs[n-t][k] for t in range(n+1) for j,k,p in pairs[i]))/F(n+1) for i in range(6)])
    return cs
lo,hi=taylor('.01'),taylor('.3')
assert all(lo[n][2]==hi[n][2] for n in range(4))
assert hi[4][2]-lo[4][2]==-F(49619,600000000)
result['exact_preparation_coefficients']={str(n):[str(hi[n][i]-lo[n][i]) for i in range(6)] for n in range(5)}
for independent in [False,True]:
    e=brentq(lambda e:cancer([(e,0,100)],independent)['four_AA_survival']-.01,.13,.30,xtol=1e-9)
    r=brentq(lambda r:healthy([(e,0,100)],r)['path_risk']-.01,2,12,xtol=1e-8)
    result['independent' if independent else 'complementary']={'erasure_boundary_N':e,'renewal_boundary_N':r}
result['scaling_N']=[dict(r=r,scaled_risk=r*r*healthy([(.3,0,10)],r,K=6,hmin=4)['path_risk']) for r in [64,128,256,512]]
w=list(map(F,[14,11,10,84,43,107]))
growth=[];pert=[]
for e in ['.01','.29','.31']:
    Q,d,pairs,A=source(e)
    growth.append([str(F(14,100)*w[i]-sum(A[i][j]*w[j] for j in range(6))) for i in range(6)])
    prow=[]
    for i in range(6):
        Lw=sum(p*(w[j]+w[k]) for j,k,p in pairs[i])
        bound=sum(Q[i][j]*abs(w[j]-w[i]) for j in range(6) if j!=i)/10000+abs(Lw-w[i])/100000+w[i]/100000
        assert bound<=w[i]/1000
        prow.append(str(bound/w[i]))
    pert.append(prow)
assert all(F(v)>=0 for row in growth for v in row)
series9=sum(F(9)**j/factorial(j) for j in range(26))
series396=sum(F(99,25)**j/factorial(j) for j in range(16))
assert series9>8000 and series396>50
mu=F(61,100);T=F(120);r=F(12)
health=20*mu*T*(20*mu/r)**10/factorial(10)
assert health<F(1,2000)
assert F(89,1000)*108-F(141,1000)*4>=9
result['exact']={'growth_slacks':growth,'weighted_perturbation_bound_rows':pert,'exp9_lower':str(series9),'exp396_lower':str(series396),'robust_healthy_risk_bound':str(health),'robust_healthy_risk_display':float(health),'robust_target_upper':'107/20000','exclusion_upper_sigma2_r001':str(clock(4,20,10,2)+F(20,4)*F(1,1000)*120),'timestamp':datetime.now(timezone.utc).isoformat()}
(P/'results/refinement.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
