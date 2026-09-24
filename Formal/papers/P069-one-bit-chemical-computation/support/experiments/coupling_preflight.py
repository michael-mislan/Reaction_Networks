"""Exact rational checks for the source-level coupling budget."""
from fractions import Fraction as F
from pathlib import Path
import json, hashlib

c=F(2147232289,2147483648)
assert 56**5>10**6*120
extra=80*F(1,10**9)+80**3*F(1,10**12)
assert extra<F(1,10**6)
baseline=2*80**2+F(2,100)*80**2
assert baseline+extra<13000
loss=F(15,10**6)
assert c-loss>F(9998,10000)
assert F(9998,10000)**10>F(998,1000)
starts=0
for x in range(8,81):
    for y in [0,1]:
        if x+y>80: continue
        starts+=1
        assert y*(y-1)*x==0
        if y:
            assert x*(x-1)>=56 and x+1<=80
        n=x+y
        assert 8<=n<=80
partitions=0
for n in range(16,77):
    for j in range(8,n-7):
        assert 8<=j<=80 and 8<=n-j<=80
        partitions+=1
result=dict(evidence='E rational algebra and finite restart checks; not K',
    starts=starts,good_partition_counts=partitions,baseline_bound=str(baseline),
    extra_hazard=str(extra),core_lower=str(c),total_loss=str(loss),
    joint_lower=str(c-loss),reported_lower='4999/5000',
    ten_cycle_reported_lower=str(F(4999,5000)**10),
    source_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
