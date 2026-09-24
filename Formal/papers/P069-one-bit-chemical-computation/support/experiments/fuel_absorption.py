"""Exact absorption/spent-fuel law; improves worst-case post-repair reverse hazard."""
from fractions import Fraction as F
from pathlib import Path
import json

def law(r,j,L):
    active={j:F(1)}; hits=[]
    if j in [0,r]:return [(0,j,F(1))]
    for k in range(1,L+1):
        nxt={}
        for y,p in active.items():
            for yy,qq in [(y-1,F(r-y-1,r-2)),(y+1,F(y-1,r-2))]:
                pp=p*qq
                if yy in [0,r]:hits.append((k,yy,pp))
                else:nxt[yy]=nxt.get(yy,F())+pp
        active=nxt
    assert sum(p for _,_,p in hits)+sum(active.values())==1
    return hits

def bound(r,j,endpoint=0):
    hits=law(r,j,64)
    v=sum(p for k,y,p in hits if y==endpoint)
    spent=sum(k*p for k,y,p in hits if y==endpoint)
    c=F(2147232289,2**31)
    b=(c-80*F(1,10**7))*v-80**3*F(5,10**11)*spent-F(3216,10**7)-F(1,10**12)
    return dict(r=r,j=j,endpoint=endpoint,v=str(v),spent_unnormalized=str(spent),
                mean_spent_conditional=float(spent/v) if v else None,lower=str(b),decimal=float(b))

rows=[bound(r,j) for j in [0,1,2] for r in range(8+j,81)]
worst=min(rows,key=lambda q:F(q['lower']))
flip=bound(10,2,10)
assert F(worst['lower'])>F(2479,2500)
assert F(flip['lower'])>F(37,5000)
out=dict(evidence='E exact finite recursion plus C source coupling',worst=worst,flip=flip,
    formula='(c-80*epsilon)*v - 80^3*beta*E[spent;absorb target] - B*tau - clock_error',
    all_rows=rows)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items() if k!='all_rows'},indent=2))
