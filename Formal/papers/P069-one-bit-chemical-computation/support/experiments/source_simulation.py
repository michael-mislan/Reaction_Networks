"""Literal 14-channel SSA, actual complementary daughters, unchanged rates.
Labels occur only in scoring. Failure runs stay in denominator. N evidence.
"""
import json, time, hashlib, math
from pathlib import Path
import numpy as np
from numba import njit

# Species: X,Y,F,PX,PY,H,W. Reverses are adjacent.
STOICH=np.array([[1,0,-1,0,0,0,0],[-1,0,1,0,0,0,0],
 [0,1,-1,0,0,0,0],[0,-1,1,0,0,0,0],
 [0,0,-1,1,0,0,0],[0,0,1,-1,0,0,0],
 [0,0,-1,0,1,0,0],[0,0,1,0,-1,0,0],
 [-1,1,0,0,0,0,0],[1,-1,0,0,0,0,0],
 [1,-1,0,0,0,-1,1],[-1,1,0,0,0,1,-1],
 [-1,1,0,0,0,-1,1],[1,-1,0,0,0,1,-1]],dtype=np.int64)

@njit
def rates(z,gamma,beta,eps):
    x,y,f,px,py,h,w=z
    return np.array([x*f,.01*x*(x-1),y*f,.01*y*(y-1),
        x*f,.01*x*px,y*f,.01*y*py,eps*x,eps*y,
        gamma*h*x*(x-1)*y,beta*w*x*(x-1)*(x-2),
        gamma*h*y*(y-1)*x,beta*w*y*(y-1)*(y-2)])

@njit
def batch(z,gamma,beta,eps):
    t=0.; events=0
    while True:
        r=rates(z,gamma,beta,eps); total=r.sum()
        if total==0: break
        dt=np.random.exponential(1/total)
        if t+dt>1.000000001: break
        t+=dt
        pick=np.random.random()*total; c=0.
        for j in range(14):
            c+=r[j]
            if pick<c:
                z+=STOICH[j];break
        events+=1
        assert z.min()>=0 and z[:5].sum()==80 and z[5]+z[6]==1
    return z,events

@njit
def experiment(samples,cycles,gamma,seed,label=0):
    np.random.seed(seed)
    successes=0; causes=np.zeros(3,np.int64); event_total=0
    terminal=np.zeros((samples,5),np.int64)
    for run in range(samples):
        z=np.array([8,1,71,0,0,1,0]) if label==0 else np.array([1,8,71,0,0,1,0])
        ok=True; collected=0; supply=0
        for cycle in range(cycles):
            z,events=batch(z,gamma,1e-12,1e-9);event_total+=events
            good=z[3+label];wrong=z[4-label];collected+=good
            if good<4: causes[0]+=1;ok=False
            if wrong>1: causes[1]+=1;ok=False
            product=z[3]+z[4];z[3]=0;z[4]=0
            a=np.empty(7,np.int64)
            for j in range(7): a[j]=np.random.binomial(z[j],.5)
            b=z-a
            for d in (a,b):
                supply+=80-d[:5].sum()+1-d[5]
                d[2]+=80-d[:5].sum();d[5]=1;d[6]=0
            if a[label]<8 or b[label]<8 or a[1-label]>1 or b[1-label]>1:
                causes[2]+=1;ok=False
            z=a  # fixed preselected daughter, regardless of outcome
        successes+=int(ok)
        terminal[run]=np.array([collected,supply,z[0],z[1],int(ok)])
    return successes,causes,event_total,terminal

def summary(samples,cycles,gamma,seed,label=0):
    start=time.monotonic()
    wins,causes,events,rows=experiment(samples,cycles,gamma,seed,label)
    # Wilson 95% interval, descriptive only; no substitution for uniform proof.
    p=wins/samples;z=1.959963984540054;d=1+z*z/samples
    center=(p+z*z/(2*samples))/d
    half=z*math.sqrt(p*(1-p)/samples+z*z/(4*samples*samples))/d
    return dict(samples=samples,cycles=cycles,gamma=gamma,seed=seed,label=label,
        successes=wins,wilson95=[center-half,center+half],
        failure_causes_nonexclusive=causes.tolist(),events=events,
        mean_collected=float(rows[:,0].mean()),max_supply=int(rows[:,1].max()),
        first_unselected_run=rows[0].tolist(),elapsed_seconds=time.monotonic()-start)

if __name__=='__main__':
    result=dict(evidence='N; no runs omitted; Wilson interval is not uniform verification',
        source_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        rows=[summary(1000,1,1e9,17401),summary(1000,1,1e9,17402,1),
              summary(1000,1,1e-12,17403),summary(100,10,1e9,17404)])
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
