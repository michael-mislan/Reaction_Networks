"""Exact pure-core return certificate; not a Lean certificate.
Same positive uniformization argument as GUIDE section 7. Strengthened partition
payoff requires at least m residents in EACH complementary daughter.
"""
import json, math, time, hashlib
from pathlib import Path
from fractions import Fraction
import numpy as np
from scipy.sparse import coo_matrix

def certify(K=80, m=8, T=1, theta=Fraction(1,2), eta=Fraction(9,10)):
    start=time.monotonic(); S=2**31
    states=[(n,p) for n in range(1,K+1) for p in range(K-n+1)]
    ix={s:i for i,s in enumerate(states)}
    entries=[]; exits=[]
    for i,(n,p) in enumerate(states):
        f=K-n-p; out=0
        for dst,r in [((n+1,p),100*n*f),((n-1,p),n*(n-1)),
                      ((n,p+1),100*n*f),((n,p-1),n*p)]:
            assert r>=0
            if r:
                assert dst in ix
                entries.append((i,ix[dst],r));out+=r
        exits.append(out)
    lam=(max(exits)+99)//100; D=100*lam
    entries.extend((i,i,D-r) for i,r in enumerate(exits))
    rr,cc,aa=zip(*entries)
    A=coo_matrix((np.array(aa,dtype=np.int64),(rr,cc)),shape=(len(states),len(states))).tocsr()
    assert np.all(A.data>=0) and np.all(np.asarray(A.sum(axis=1)).ravel()==D)
    e=sum((Fraction((-1)**j,math.factorial(j)) for j in range(26)),Fraction())
    weights=[int(S*e/math.factorial(j)) for j in range(19)]
    assert D*S<2**63 and S*sum(weights)<2**63 and sum(weights)<=S
    def bin_tail(n, lower, upper, prob):
        a,b=prob.numerator,prob.denominator
        return Fraction(sum(math.comb(n,j)*a**j*(b-a)**(n-j) for j in range(lower,upper+1)),b**n)
    split={n:bin_tail(n,m,n-m,theta) for n in range(1,K+1)}
    collect={p:bin_tail(p,4,p,eta) for p in range(K+1)}
    v=np.array([int(S*split[n]*collect[p]) for n,p in states],dtype=np.int64)
    assert v.min()>=0 and v.max()<=S
    last=max(j for j,w in enumerate(weights) if w)
    for _ in range(lam*T):
        term=v; acc=weights[0]*term
        for j in range(1,last+1):
            term=A.dot(term)//D
            acc+=weights[j]*term
        v=acc//S
    starts=[ix[(n,0)] for n in range(m,K+1)]
    worst=min(starts,key=lambda i:int(v[i]))
    return dict(evidence='E plus conventional uniformization proof, not K',K=K,m=m,T=T,
                quota=4,states=len(states),lambda_integer=lam,blocks=lam*T,
                numerator=int(v[worst]),denominator=S,worst=states[worst],
                display=float(v[worst]/S),elapsed_seconds=time.monotonic()-start,
                max_matrix_accumulator=D*S,max_weight_accumulator=S*sum(weights),
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())

if __name__=='__main__':
    results=[]
    for a in [49,48,45]:
        r=certify(theta=Fraction(a,100))
        results.append({'theta_exact':str(Fraction(a,100)),'eta_exact':'9/10',**r})
    assert [r['numerator'] for r in results]==[2147213192,2147153442,2146619325]
    Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2))
    print(json.dumps(results,indent=2))
