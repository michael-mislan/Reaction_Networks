from fractions import Fraction as F
from math import comb, factorial
import json

c=F(2147232289,2**31)
def correction(r,L,y):
    d=r-2
    v=[0]*(r+1);v[0]=1
    den=1
    for _ in range(L):
        den*=d
        v=[den]+[(r-j-1)*v[j-1]+(j-1)*v[j+1] for j in range(1,r)]+[0]
    return F(v[y],den)

rows=[]
for r in [10,12,16,18]:
 for L in [2,8,16,32,64]:
  v=correction(r,L,2)
  rows.append({'r':r,'fuel':L,'correct_by_fuel':float(v),'infinite_fuel':1-F(1,2**(r-3))})
worst=min(((correction(r,64,2),r) for r in range(10,81)),key=lambda x:x[0])
# Exact bound for Erlang(64,144) tail using a positive lower Taylor sum for exp(144).
tail_poly=sum((F(144**j,factorial(j)) for j in range(64)),F())
exp_lower=sum((F(144**j,factorial(j)) for j in range(301)),F())
tail_upper=tail_poly/exp_lower
assert tail_upper<F(1,10**12)
# Other y=0/1 cases: no correction or a much faster single repair. At r>=9,
# H=64, gamma>=2e7 and tau=1e-7, exponent>=7168; exp(-7168)<1e-12.
assert F(7168**4,factorial(4))>10**12
B=F(3216)
loss_no_clock=(1-worst[0])+B*F(1,10**7)+80*F(1,10**7)+64*80**3*F(5,10**11)
new=c-loss_no_clock-F(1,10**12)
assert new>F(99,100)
# Imperfect-operation certificate numerator from operation_certificate.py.
operation_core=F(2147153442,2**31)
operation_loss=F(1,10**6)+F(3216,400000000)+80*F(1,10**8)+80**3*F(1,10**11)
operation_joint=operation_core-operation_loss
assert operation_joint>F(4999,5000)
# One-minority improved parameter box.
e14_lower=sum((F(14**j,factorial(j)) for j in range(19)),F())
assert e14_lower>10**6
one_loss=F(1,10**6)+F(3216,80000000)+80*F(1,10**7)+80**3*F(6,10**11)
one=c-one_loss
assert one>F(4999,5000)
# Verify the tight core prefix bound and allowance for rare channels.
core_max=max(2*r*(80-r)+F(r*(r-1),100) for r in range(8,81))
assert core_max+80*F(1,10**7)+64*80**3*F(5,10**11)<3216
# Finite population selection using original q.
q=F(4999,5000)
selection=[]
for cutoff in [15,16]:
 bad=F(1+sum(comb(20,j) for j in range(cutoff+1,21)),2**20)
 lower=1-20*(1-q)-bad
 selection.append({'max_Y':cutoff,'odds_gain':str(F(20,cutoff)),'lower':str(lower),'decimal':float(lower)})
# A source-derived opposite-program event from the (8,2) preparation.
wrong=correction(10,64,8)
mutation_lower=c+wrong-1-F(1,10**12)-F(3216,10**7)-80*F(1,10**7)-64*80**3*F(5,10**11)
assert mutation_lower>F(57,10000)
mutation_population=1-(1-F(57,10000))**128
assert mutation_population>F(1,2)
out={'core_prefix_max':str(core_max),'one_minority_improved_bound':str(one),'one_minority_decimal':float(one),
     'correction_rows':rows,'two_minority_worst_r':worst[1],'two_minority_correction_min':str(worst[0]),
     'two_minority_correction_decimal':float(worst[0]),'time_tail_upper':float(tail_upper),
     'two_minority_joint_lower':str(new),'two_minority_joint_decimal':float(new),'selection':selection,
     'imperfect_operation_joint_lower':str(operation_joint),'imperfect_operation_joint_decimal':float(operation_joint),
     'opposite_program_lower':str(mutation_lower),'opposite_program_decimal':float(mutation_lower),
     'at_least_one_opposite_pair_128_lower':float(mutation_population),
     'scope':'Exact arithmetic for new conventional arguments; not Lean checked; no repository mutation.'}
print(json.dumps(out,indent=2,default=str))
with open(__file__.replace('.py','.json'),'w') as f:json.dump(out,f,indent=2,default=str)
