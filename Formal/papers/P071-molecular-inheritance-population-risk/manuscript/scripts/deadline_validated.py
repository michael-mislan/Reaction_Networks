"""Outward integer interval Taylor integration, N=2 PGFs.

Order 20, h=1/50, complex analytic radius 1/4. Global l-infinity
logarithmic Lipschitz bound 9/100 on [0,1]^6. All recurrence arithmetic
is integer/rational. Round each endpoint to denominator 10^40.
"""
from fractions import Fraction as F
from pathlib import Path
import json,time
S=10**40; ORDER=20; STEPS=15000; ROOT=Path(__file__).resolve().parents[1]
# f(z) = c + L z + sum p z_j z_k; coefficients / 200.
L=[[-68,4,0,4,0,0],[2,-186,102,0,2,0],[0,4,-84,0,0,0],
   [2,0,0,-128,2,102],[0,52,0,52,-184,0],[0,0,0,4,0,-26]]
# first row diagonal Q=-.04, death=.3,b=.1 => -.44, i.e. -88/200.
L[0][0]=-88
C=[60,60,60,2,60,2]
P=[[(0,0,20)],[(0,1,20)],[(0,2,10),(1,1,10)],
   [(0,3,20)],[(0,4,10),(1,3,10)],[(0,5,10),(3,3,10)]]
def ceildiv(a,b):return -((-a)//b)
def integrate(initial):
    center=[initial*S//initial.denominator if False else int(initial*S)]*6
    # Accumulated local interval error can use the single global exp(27) bound.
    local_sum=F(0); maximum_round=0
    for step in range(STEPS):
        lo=[center];hi=[center]
        for n in range(ORDER):
            low=[];high=[]
            for i in range(6):
                a=C[i]*S if n==0 else 0;b=a
                for j,k in enumerate(L[i]):
                    if k>=0:a+=k*lo[n][j];b+=k*hi[n][j]
                    else:a+=k*hi[n][j];b+=k*lo[n][j]
                # Accumulate products before division, retaining exact endpoints.
                aa=0;bb=0
                for j,k,p in P[i]:
                    for v in range(n+1):
                        vals=(lo[v][j]*lo[n-v][k],lo[v][j]*hi[n-v][k],hi[v][j]*lo[n-v][k],hi[v][j]*hi[n-v][k])
                        aa+=p*min(vals);bb+=p*max(vals)
                low.append((a*S+aa)//(200*(n+1)*S))
                high.append(ceildiv(b*S+bb,200*(n+1)*S))
            lo.append(low);hi.append(high)
        # Horner evaluation at h=1/50.
        l=lo[-1][:];u=hi[-1][:]
        for n in range(ORDER-1,-1,-1):
            l=[lo[n][i]+l[i]//50 for i in range(6)]
            u=[hi[n][i]+ceildiv(u[i],50) for i in range(6)]
        center=[max(0,min(S,(l[i]+u[i])//2)) for i in range(6)]
        width=max(max(abs(center[i]-l[i]),abs(u[i]-center[i])) for i in range(6))
        maximum_round=max(maximum_round,width)
    # The analytic tail is uniform at every center in [0,1].
    tail=2*F(2,25)**21/(1-F(2,25))
    # exp(27) < 6e11, certified by rational Taylor sum plus geometric tail.
    terms=[F(1)]
    for n in range(1,201):terms.append(terms[-1]*27/n)
    exp_upper=sum(terms)+terms[-1]*F(27,201)/(1-F(27,202))
    assert exp_upper<6*10**11
    error=6*10**11*STEPS*(tail+F(maximum_round,S))+F(1,S)*6*10**11
    lower=F(center[5],S)-error;upper=F(center[5],S)+error
    return {'initial':str(initial),'AA_lower':str(lower),'AA_upper':str(upper),
      'AA_interval':[float(lower),float(upper)],'error':str(error),'error_decimal':float(error),
      'max_integer_round':maximum_round,'tail':str(tail)}
def main():
    t=time.time();a=integrate(F(0));print(a['AA_interval'],flush=True)
    b=integrate(F(299,300));print(b['AA_interval'],flush=True)
    assert F(a['AA_lower'])>F(22,100)
    assert F(b['AA_upper'])<F(227,1000)
    result={'method':'exact outward integer interval Taylor; analytic global remainder',
      'order':ORDER,'step':'1/50','steps':STEPS,'complex_radius':'1/4',
      'lognorm':'9/100','u0':a,'uz':b,'seconds':time.time()-t}
    (ROOT/'data/deadline_validated.json').write_text(json.dumps(result,indent=2))
    print('CERTIFIED',time.time()-t,flush=True)
if __name__=='__main__':main()
