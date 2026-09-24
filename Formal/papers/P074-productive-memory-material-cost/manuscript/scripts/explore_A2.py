from fractions import Fraction as F
from ctmc_certificate import certify, nominal_groups, payoff_biased, SCALE
T=999*SCALE
def show(tag,r):
    print(tag, 'L',r['lower'], r['lower']/SCALE, 'PASS' if 1000*r['lower']>=T else 'fail', r['lower_state'],'U', r['upper'], r['upper']/SCALE, r['upper_state'], r['seconds'], flush=True)
for th in [F(7,20),F(1,3),F(3,10),F(1,4)]:
    show(f'bias theta={th}', certify(32, nominal_groups(10,20), split=payoff_biased(th)))
# vertex (kd,kr)=(20,10) nominal two-sided
g=[([0],[F(1)],F(1),F(1)),([1],[F(1)],F(1,100),F(1,100)),([2],[F(1)],F(2),F(2)),([5],[F(1)],F(1,50),F(1,50)),([3],[F(1)],F(20),F(20)),([4],[F(1)],F(10),F(10))]
show('vertex kd=20,kr=10', certify(32,g))
g[4]=([3],[F(1)],F(10),F(10)); g[5]=([4],[F(1)],F(20),F(20))
show('vertex kd=10,kr=20', certify(32,g))
show('K31 nominal', certify(31, nominal_groups(10,10)))
show('theta=9/20 eps=1/1000', certify(32, nominal_groups(10,20,eps=F(1,1000)), split=payoff_biased(F(9,20))))
