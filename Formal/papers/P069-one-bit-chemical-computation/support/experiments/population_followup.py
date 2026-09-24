"""Bounded literal-CTMC serial transfer; no label-driven rates or daughter manufacture."""
import json,math,time
from pathlib import Path
import numpy as np
from numba import njit
from source_simulation import STOICH,rates

@njit
def run_batch(z,gamma,beta,eps,T,L):
    t=0.
    while True:
        v=rates(z,gamma,beta,eps);tot=v.sum()
        if tot==0:break
        t+=np.random.exponential(1/tot)
        if t>T:break
        u=np.random.random()*tot;s=0.
        for k in range(14):
            s+=v[k]
            if u<s:z+=STOICH[k];break
        assert z.min()>=0 and z[:5].sum()==80 and z[5]+z[6]==L
    return z

@njit
def daughter_pair(z,L,theta,eta):
    q=np.array([np.random.binomial(z[3],eta),np.random.binomial(z[4],eta)])
    z[3]=0;z[4]=0
    a=np.empty(7,np.int64)
    for k in range(7):a[k]=np.random.binomial(z[k],theta)
    b=z-a;supply=0
    for d in (a,b):
        supply+=80-d[:5].sum()+L-d[5]
        d[2]+=80-d[:5].sum();d[5]=L;d[6]=0
    return a,b,q,supply

def classify(z,m=1):
    if z[0]>=8 and z[1]<=m:return 0
    if z[1]>=8 and z[0]<=m:return 1
    return 2

@njit
def seed_rng(seed):np.random.seed(seed)

def population(seed,neutral=False):
    seed_rng(seed);rng=np.random.default_rng(seed+1)
    pop=[np.array([8,1,71,0,0,1,0],dtype=np.int64) for _ in range(10)]
    pop +=[np.array([1,8,71,0,0,1,0],dtype=np.int64) for _ in range(10)]
    supply=1620;rows=[dict(round=0,counts=[10,10,0],supply=supply)]
    for rnd,target in enumerate([0,0,1,1,1],1):
        new=[];outside_mothers=0;failure=0
        for mother in pop:
            label=classify(mother)
            z=run_batch(mother.copy(),1e8,1e-11,1e-8,1+1/4e8,1)
            a,b,q,cost=daughter_pair(z,1,.48,.9);supply+=cost
            if label==2:outside_mothers+=1
            elif not(q[label]>=4 and q[1-label]<=1 and classify(a)==label and classify(b)==label):failure+=1
            retention=.5 if neutral or q[target]<4 else 1.
            for d in (a,b):
                if rng.random()<retention:new.append(d)
        pop=new
        counts=[sum(classify(z)==k for z in pop) for k in range(3)]
        rows.append(dict(round=rnd,environment='neutral' if neutral else ['PX','PY'][target],
                         counts=counts,supply=supply,chemical_failures=failure,outside_mothers=outside_mothers))
    return rows

def switching(seed=9291):
    seed_rng(seed);rows=[]
    for x,y in [(8,2),(10,0),(40,0)]:
        n=2000;opposite=0;outside=0;selected=0
        for _ in range(n):
            z=run_batch(np.array([x,y,80-x-y,0,0,64,0]),2e7,5e-11,1e-7,1.0000001,64)
            a,b,q,cost=daughter_pair(z,64,.5,1.)
            opposite+=int(q[1]>=4 and q[0]<=1 and classify(a,2)==1 and classify(b,2)==1)
            selected+=int(q[0]>=4 and q[1]<=1 and classify(a,2)==0 and classify(b,2)==0)
            outside+=int(classify(a,2)==2 or classify(b,2)==2)
        rows.append(dict(start=[x,y],n=n,opposite_pairs=opposite,selected_pairs=selected,
                         outside_pairs=outside,zero_count_95_upper=1-.05**(1/n)))
    return rows

if __name__=='__main__':
    t=time.monotonic()
    out=dict(evidence='N; no failures removed or outside states renormalized',
        selected=population(8201),neutral=population(8201,True),switching=switching(),
        elapsed_seconds=time.monotonic()-t,
        analytical_pure_start_switch_upper='(80*1e-7+64*80^3*5e-11)*(1+1e-7)',
        note='Pure-start bound is a first minority-creation bound, not an exact mutation rate.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
