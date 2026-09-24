import json, sys
from fractions import Fraction as F
from ctmc_certificate import certify, nominal_groups, payoff_biased, SCALE
T=999*SCALE
def show(tag,r):
    print(tag, r['lower'], r['lower']/SCALE, 'PASS' if 1000*r['lower']>=T else 'fail', r['lower_state'], r['clock'], r['seconds'], flush=True)
for th in [F(99,200),F(49,100),F(12,25),F(47,100),F(9,20),F(2,5)]:
    show(f'bias theta={th}', certify(32, nominal_groups(10,20), split=payoff_biased(th)))
show('untied kd,kr in [10,20]', certify(32, nominal_groups(10,20,tied=False)))
for e in [F(1,1000),F(1,200),F(1,100),F(1,50)]:
    show(f'eps={e} tied band', certify(32, nominal_groups(10,20,eps=e)))
