"""Replay every printed number and identity of the paper with exact arithmetic.

Run with the repository interpreter:  python check_paper.py
Needs only the standard library and sympy.  This is a certificate replay, not
an implementation of the decision algorithm of Theorem 1.1.
"""
from fractions import Fraction as Q
from itertools import permutations
import json
import sympy as S

out = {}

# ---------------------------------------------------------------- Section 2
x, y, a, b, t, r = S.symbols('x y a b t r', positive=True)
G = (a*x + 2*b*x**2)/(a + 2*b)
F = (a*x + b*x**2)/(a + b)
p, q = a*(x - y), b*(y - x**2)
assert S.simplify((2*q - p) - (a + 2*b)*(y - G)) == 0
assert S.simplify((p - q) - (a + b)*(F - y)) == 0
assert S.simplify((F - G) - a*b*x*(1 - x)/((a + b)*(a + 2*b))) == 0
assert S.simplify((2*q - p) + (p - q) - q) == 0            # R_u + R_v = q
# inverse of F in the ratio r = a/b
Fr = (r*x + x**2)/(r + 1)
Gr = (r*x + 2*x**2)/(r + 2)
kinv = (-r + S.sqrt(r**2 + 4*(r + 1)*(y + t)))/2
assert S.simplify(Fr.subs(x, kinv) - (y + t)) == 0
out['one_edge_identities'] = 'PASS'

# ---------------------------------------------------------------- Section 3
# worked unit edge, t = 1/100, boxes [1/10,9/10] x [1/100,9/10]
T = S.Rational(1, 100)
G1 = lambda z: (z + 2*z*z)/3
F1inv = lambda z: (-1 + S.sqrt(1 + 8*z))/2
Au, Av = S.Rational(1, 10), S.Rational(1, 100)
Pu = S.Max(Au, F1inv(Av + T)); Pv = S.Max(Av, G1(Au) + T)
assert Pu == Au and Pv == S.Rational(1, 20)
assert F1inv(Pv + T) > Pu                                  # violated implication v -> u
alpha = (5 - S.sqrt(13))/10
assert S.simplify(alpha*(1 - alpha) - 12*T) == 0
assert S.simplify(F1inv(G1(alpha) + 2*T) - alpha) == 0     # fixed root of the cycle map
zv = (43 - 10*S.sqrt(13))/100
assert S.simplify(G1(alpha) + T - zv) == 0
assert S.simplify((alpha + alpha**2)/2 - T - zv) == 0      # both constraints tight
assert alpha > Pu and float(alpha) < 0.14
# general unit-edge fixed-root equation and the double root at 1/48
u, TT = S.symbols('u T')
gap = S.factor(Fr.subs({r: 1, x: u}) - Gr.subs({r: 1, x: u}) - 2*TT)
assert S.expand(gap - (u*(1 - u) - 12*TT)/6) == 0
assert S.discriminant(S.expand(6*gap), u) == 1 - 48*TT
out['unit_edge_jump'] = dict(alpha=str(alpha), z_v=str(zv), alpha_float=float(alpha))

# tight-support counterexample (compiled in Interaction.lean)
def Gq(z, rr=Q(1)): return (rr*z + 2*z*z)/(rr + 2)
def Fq(z, rr=Q(1)): return (rr*z + z*z)/(rr + 1)
tau = Q(1, 64)
for (xs, ys) in [(Q(1, 4), Q(9, 64)), (Q(3, 4), Q(41, 64))]:
    assert Gq(xs) + tau <= ys <= Fq(xs) - tau
assert Gq(Q(1, 4)) + tau == Q(9, 64)                       # selected state is tight below
assert Fq(Q(1, 4)) - tau == Q(9, 64)                       # and tight above: a cycle root
assert not (Q(41, 64) + tau <= Fq(Q(1, 4)))                # omitted constraint fails
assert Fq(Q(1, 4)) - Q(41, 64) - tau == -Q(1, 2)           # ... by exactly 1/2
assert Gq(Q(3, 4)) + tau == Q(41, 64) == Fq(Q(3, 4)) - tau
out['tight_support_counterexample'] = 'PASS'

# matched diamond: identity at t = 0, strictly infeasible for t > 0
Fu = lambda z: (z + z*z)/2
diamond = S.factor(Fu(Fu(u) - TT) - TT - (Fu(Fu(u) + TT) + TT))
assert S.expand(diamond + TT*(u*u + u + 3)) == 0
assert S.simplify(Gr.subs(r, 2) - Fr.subs(r, 1)) == 0      # G_2 = F_1
out['identity_diamond'] = str(diamond)

# shortcut obstruction with unit factors
short = S.factor(Gr.subs({r: 1, x: u}) - Fu(Fu(u)))
assert S.expand(short - u*(1 - u)*(3*u*u + 9*u + 2)/24) == 0
out['shortcut_identity'] = str(short)

# ---------------------------------------------------------------- Section 5
# downward rounding constants: F', G' <= 2 on [0,1]
assert S.simplify(S.diff(F, x).subs(x, 1) - (a + 2*b)/(a + b)) == 0
assert S.simplify(S.diff(G, x).subs(x, 1) - (a + 4*b)/(a + 2*b)) == 0

# ---------------------------------------------------------------- Section 7
def longest_path(n, edges):
    adj = {i: set() for i in range(n)}
    for i, j in edges:
        adj[i].add(j); adj[j].add(i)
    best = 0
    def dfs(v, seen, length):
        nonlocal best
        best = max(best, length)
        for w in adj[v]:
            if w not in seen:
                dfs(w, seen | {w}, length + 1)
    for v in range(n):
        dfs(v, {v}, 0)
    return best
def windmill(k):
    e = []
    for i in range(k):
        bi, ci = 1 + 2*i, 2 + 2*i
        e += [(0, bi), (bi, ci), (0, ci)]
    return 2*k + 1, e
hs = {}
for k in range(1, 6):
    n, e = windmill(k)
    hs[k] = longest_path(n, e)
    assert len(e) <= max(hs[k], 1)*n                        # m <= h n
assert hs == {1: 2, 2: 4, 3: 4, 4: 4, 5: 4}
assert longest_path(6, [(0, i) for i in range(1, 6)]) == 2  # star
assert longest_path(5, [(i, j) for i in range(5) for j in range(i)]) == 4  # K_5
out['windmill_longest_paths'] = hs

# Proposition 1.3 (barrier): a directed path with box {x0} at the source and
# boxes [lam,1] elsewhere is compatible iff F_m o ... o F_1 (x0) > lam.
ratios = [Q(1), Q(2), Q(1, 2), Q(3), Q(5, 2), Q(1), Q(4)]
x0 = Q(9, 10)
FP, GP, bits = x0, x0, []
for rr in ratios:
    FP, GP = Fq(FP, rr), Gq(GP, rr)
    bits.append(FP.denominator.bit_length())
assert all(b2 >= 2*b1 - 2 for b1, b2 in zip(bits, bits[1:]))   # denominators square
assert GP < FP < x0
lam = FP - Q(1, 10**6)                                          # feasible side
theta, state = None, None
for kk in range(1, 60):
    th = 1 - Q(1, 2**kk)
    zz = [x0]
    for rr in ratios:
        zz.append((1 - th)*Gq(zz[-1], rr) + th*Fq(zz[-1], rr))
    if zz[-1] >= lam:
        theta, state = th, zz
        break
assert state is not None
for (xa, xb, rr) in zip(state, state[1:], ratios):
    assert Gq(xa, rr) < xb < Fq(xa, rr) and lam <= xb <= 1
# infeasible side: any productive state has z_m < F_P(x0), so lam >= F_P(x0) is impossible
out['barrier_path'] = dict(m=len(ratios), denominator_bits=bits, theta=str(theta))

# ---------------------------------------------------------------- Section 8
rho = S.symbols('rho', positive=True)
width = S.simplify(Fr.subs(r, rho) - Gr.subs(r, rho))
assert S.simplify(width - rho*x*(1 - x)/((rho + 1)*(rho + 2))) == 0
cap = rho/(8*(rho + 1)*(rho + 2))
crit = S.solve(S.diff(cap, rho), rho)
assert crit == [S.sqrt(2)]
assert S.simplify(cap.subs(rho, S.sqrt(2)) - (3 - 2*S.sqrt(2))/8) == 0
assert cap.subs(rho, 1) == S.Rational(1, 48)
assert Gq(Q(1, 2)) + Q(1, 48) == Q(17, 48) == Fq(Q(1, 2)) - Q(1, 48)
rm, rp = S.symbols('r_minus r_plus', positive=True)
rob = S.simplify(Fr.subs(r, rm) - Gr.subs(r, rp)
                 - (2*rm - rp)*x*(1 - x)/((rm + 1)*(rp + 2)))
assert rob == 0
assert S.simplify(S.diff(Fr, r) - x*(1 - x)/(r + 1)**2) == 0
assert S.simplify(S.diff(Gr, r) - 2*x*(1 - x)/(r + 2)**2) == 0
out['capacity'] = dict(universal=str((3 - 2*S.sqrt(2))/8),
                       universal_float=float((3 - 2*S.sqrt(2))/8), unit='1/48')

# ---------------------------------------------------------------- Section 9
edges = [('AB', Q(1, 10), Q(13, 200), Q(2), Q(1)),
         ('BC', Q(13, 200), Q(43, 1000), Q(2), Q(1)),
         ('AC', Q(1, 10), Q(43, 1000), Q(1), Q(1))]
rr_, eps = Q(1, 20), Q(1, 10000)
radii, normalized, worst, rows = [], [], [], []
food = Q(0); hub = Q(0)
for name, xx, yy, aa, bb in edges:
    pp, qq = aa*(xx - yy), bb*(yy - xx*xx)
    ru, rv = 2*qq - pp, pp - qq
    assert ru > 0 and rv > 0
    radii += [ru/(2*qq + pp), rv/(pp + qq)]
    normalized += [ru/(aa + 2*bb), rv/(aa + bb)]
    assert xx - eps > yy + eps and yy - eps > (xx + eps)**2
    lo_u = 2*bb*(1 - rr_)*(yy - eps - (xx + eps)**2) - aa*(1 + rr_)*(xx + eps - yy + eps)
    lo_v = aa*(1 - rr_)*(xx - eps - yy - eps) - bb*(1 + rr_)*(yy + eps - (xx - eps)**2)
    assert lo_u > 0 and lo_v > 0
    worst += [lo_u, lo_v]
    food += qq
    if name[0] == 'A':
        hub += ru
    rows.append(dict(edge=name, p=str(pp), q=str(qq), Ru=str(ru), Rv=str(rv),
                     Ru_box_min=str(lo_u), Rv_box_min=str(lo_v)))
assert min(radii) == Q(19, 301)
assert min(normalized) == Q(209, 120000)
assert min(worst) == Q(1175221, 2000000000)
assert food == Q(5071, 40000) and hub == Q(49, 1000)
# at r = 1/20 and fixed nominal activities the smallest residual is 869/800000
fixed = []
for name, xx, yy, aa, bb in edges:
    pp, qq = aa*(xx - yy), bb*(yy - xx*xx)
    fixed += [(2*qq - pp) - rr_*(2*qq + pp), (pp - qq) - rr_*(pp + qq)]
assert min(fixed) == Q(869, 800000)
out['triangle'] = dict(rows=rows, margin='209/120000', radius='19/301',
                       box_min='1175221/2000000000', food='5071/40000', hub='49/1000')
# directed triangle obstruction: each edge deletion leaves a productive path
for xx, yy in [(Q(1, 2), Q(7, 20)), (Q(7, 20), Q(23, 100))]:
    assert Gq(xx) < yy < Fq(xx)

# ---------------------------------------------------------------- Section 10
d = S.symbols('d', integer=True, positive=True)
for dd in range(2, 7):
    Gd = (a*x + dd*b*x**dd)/(a + dd*b)
    Fd = (a*x + b*x**dd)/(a + b)
    qd = b*(y - x**dd)
    assert S.simplify((dd*qd - p) - (a + dd*b)*(y - Gd)) == 0
    assert S.simplify((p - qd) - (a + b)*(Fd - y)) == 0
    assert S.simplify((Fd - Gd) - (dd - 1)*a*b*x*(1 - x**(dd - 1))/((a + b)*(a + dd*b))) == 0
    assert S.simplify(dd - S.diff(Fd, x).subs(x, 1)) .is_nonnegative is not False
    assert S.simplify(S.diff(Gd, x).subs(x, 1) - (a + dd*dd*b)/(a + dd*b)) == 0
    assert S.simplify(dd*(a + dd*b) - (a + dd*dd*b) - (dd - 1)*a) == 0   # G_d' <= d
    assert S.simplify(dd*(a + b) - (a + dd*b) - (dd - 1)*a) == 0          # F_d' <= d
out['degree_d_identities'] = 'PASS for d = 2..6'

out['status'] = 'PASS'
print(json.dumps(out, indent=2))
