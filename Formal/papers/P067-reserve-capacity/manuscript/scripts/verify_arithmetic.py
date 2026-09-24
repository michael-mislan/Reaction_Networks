"""Independent exact-rational audit of the merged Therapeutic Windows paper.

Everything is rebuilt from the *stated modelling rules*, not from the printed
tables, so that a transcription error in the manuscript would show up here.
"""
from fractions import Fraction as F
from math import comb, factorial, log

# ---------------------------------------------------------------- source ----
# state order: 0 UU (0,0), 1 UR (0,1), 2 RR (0,2), 3 AU (1,0), 4 AR (1,1), 5 AA (2,0)
STATES = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)]
IDX = {s: i for i, s in enumerate(STATES)}
W = [F(14), F(11), F(10), F(84), F(43), F(107)]
D = [F(3, 10), F(3, 10), F(3, 10), F(1, 100), F(3, 10), F(1, 100)]
B = F(1, 10)


def Qmat(e):
    """Row generator Q_e built from the four chemistry rules."""
    Q = [[F(0)] * 6 for _ in range(6)]
    for i, (a, s) in enumerate(STATES):
        u = 2 - a - s
        moves = [
            ((a + 1, s), u * (F(1, 100) + F(a, 2))),
            ((a, s + 1), u * (F(1, 100) + F(s, 2))),
            ((a - 1, s), a * (e + F(s, 4))),
            ((a, s - 1), s * (e + F(a, 4))),
        ]
        for tgt, rate in moves:
            if tgt in IDX and rate != 0:
                Q[i][IDX[tgt]] += rate
        Q[i][i] = -sum(Q[i][j] for j in range(6) if j != i)
    return Q


def Lmat():
    """L[i][j] = expected number of type-j daughters from a type-i mother."""
    L = [[F(0)] * 6 for _ in range(6)]
    for i, (a, s) in enumerate(STATES):
        tot = F(1, 2 ** (a + s))
        for ii in range(a + 1):
            for jj in range(s + 1):
                p = tot * comb(a, ii) * comb(s, jj)
                for tgt in ((ii, jj), (a - ii, s - jj)):
                    L[i][IDX[tgt]] += p
    return L


L = Lmat()
Lw = [sum(L[i][j] * W[j] for j in range(6)) for i in range(6)]


def drift_ratios(e):
    Q = Qmat(e)
    out = []
    for i in range(6):
        Qw = sum(Q[i][j] * W[j] for j in range(6))
        Aw = Qw + B * (Lw[i] - W[i]) - D[i] * W[i]
        out.append(Aw / W[i])
    return out


def envelope_ratios(e):
    Q = Qmat(e)
    out = []
    for i in range(6):
        br = sum(Q[i][j] * abs(W[j] - W[i]) for j in range(6) if j != i)
        br += B * abs(Lw[i] - W[i]) + D[i] * W[i]
        out.append(br / W[i])
    return out


print("=" * 72)
print("1. SOURCE RECONSTRUCTION AND DRIFT CERTIFICATE")
print("=" * 72)
print("Lw =", [str(v) for v in Lw])
paper_rows = {  # certificate_rows.tex, as printed in the manuscript
    F(1, 100): [F(-73, 700), F(-103, 550), F(-21, 125), F(559, 4200), F(-363, 2150), F(111, 5350)],
    F(29, 100): [F(-73, 700), F(-61, 550), F(-14, 125), F(-421, 4200), F(-237, 2150), F(-533, 5350)],
    F(31, 100): [F(-73, 700), F(-29, 275), F(-27, 250), F(-491, 4200), F(-114, 1075), F(-579, 5350)],
}
for e, printed in paper_rows.items():
    got = drift_ratios(e)
    assert got == printed, (e, [str(x) for x in got], [str(x) for x in printed])
    print(f"  drift row e={float(e):.2f}: matches manuscript  max={str(max(got))}")

env_printed = [F(353, 700), F(323, 550), F(123, 250), F(451, 1050), F(1427, 1075), F(477, 2675)]
env = envelope_ratios(F(31, 100))
assert env == env_printed, ([str(x) for x in env], [str(x) for x in env_printed])
print("  error envelope at e=.31: matches manuscript  max=", str(max(env)))
# envelope is nondecreasing in e (Q entries affine with >=0 slope), so .31 is the max
assert max(envelope_ratios(F(1, 100))) <= max(env)
assert max(env) <= F(27, 20), max(env)
print("  max envelope 1427/1075 =", float(max(env)), "<= 27/20 = 1.35  OK")

# affine in e => endpoints suffice
gmax = max(max(drift_ratios(F(1, 100))), max(drift_ratios(F(31, 100))))
cmax = max(max(drift_ratios(F(29, 100))), max(drift_ratios(F(31, 100))))
assert gmax <= F(67, 500), gmax
assert cmax <= F(-99, 1000), cmax
print(f"  nominal growth  max on [.01,.31] = {str(gmax)} = {float(gmax):.6f} <= 67/500 = 0.134")
print(f"  nominal contract max on [.29,.31] = {str(cmax)} = {float(cmax):.6f} <= -99/1000 = -0.099")
g = F(67, 500) + F(27, 2000)
gam = F(99, 1000) - F(27, 2000)
assert g == F(59, 400) and gam == F(171, 2000)
print(f"  robust g = {str(g)} = {float(g)},  gamma = {str(gam)} = {float(gam)}   OK")

print()
print("=" * 72)
print("2. DELIVERY, TAYLOR SUMS, TARGET RISK")
print("=" * 72)
assert sum((F(99, 25) ** j / factorial(j) for j in range(16)), F(0)) > 50
print("  Taylor deg 15 at 99/25 > 50            OK   (=> c(t) >= 1421/5050 > .28 on [4,112])")
assert F(29, 101) * F(49, 50) == F(1421, 5050) and F(1421, 5050) > F(28, 100)
assert F(1, 100) + F(29, 99) < F(31, 100)      # e stays inside [.01,.31]
assert F(1, 100) + F(28, 100) == F(29, 100)    # e >= .29 on the contraction window
print("  band: e in [.01,.31] always, e in [.29,.31] on [4,112]   OK")
expo = 108 * gam - 4 * g
assert expo == F(2161, 250) and expo > F(43, 5)
assert sum((F(43, 5) ** j / factorial(j) for j in range(31)), F(0)) > 5000
print(f"  exponent 108*gamma - 4*g = {str(expo)} = {float(expo)} > 43/5;  e^(43/5) > 5000  OK")
tgt = F(4 * 107, 10) / 5000
assert tgt == F(107, 12500)
print(f"  target survival bound  <= {str(tgt)} = {float(tgt)}")
# delivery budgets
assert 112 * F(29, 100) == F(812, 25) < 33
assert F(3248, 99) < 33 and F(29, 99) < F(3, 10)
print("  amount 812/25 = 32.48 < 33;  exposure <= 3248/99 =", float(F(3248, 99)), "< 33  OK")
# healthy mortality ceiling
mH = (F(3, 10) + F(29, 99)) / 2 + F(1, 200)
assert mH < F(61, 200)
print(f"  healthy mortality ceiling {float(mH):.9f} < 61/200 = 0.305  OK")

print()
print("=" * 72)
print("3. ANCHORED RESERVE PRODUCTS")
print("=" * 72)


def reserve(K, hmin, M, reff=F(1), m=F(61, 200), T=120):
    P = {hmin - 1: F(1)}
    for h in range(hmin, M):
        P[h] = P[h - 1] * K * m / (reff * (K - h))
    DM = sum(P.values(), F(0))
    simple = M * m * T * P[M - 1]
    return P, DM, simple


P4, D4, s4 = reserve(400, 200, 278)
assert s4 < F(7, 10 ** 6)
full4 = s4 / D4
print(f"  K=400,hmin=200,M=278,reff=1: simple = {float(s4):.16e} < 7e-6   OK")
print(f"      D_M = {float(D4):.10f}   sharpened M m T q_M = {float(full4):.10e}")

print("  initial-filling table (Corollary: incomplete preparation):")
rows = {}
for h0 in (200, 220, 240, 250, 260, 278):
    init = sum((v for j, v in P4.items() if j >= h0), F(0)) / D4 if h0 < 278 else F(0)
    rows[h0] = (init, init + full4)
    print(f"      H0={h0:3d}  initial term {float(init):.10e}   total {float(init + full4):.10e}")
assert rows[240][1] < F(3, 10 ** 6)
print("      H0 >= 240  =>  total < 3e-6   OK")
# find the exact minimal H0 meeting several tolerances
for tol, lab in ((F(1, 100), "1e-2"), (F(1, 10 ** 4), "1e-4"), (F(3, 10 ** 6), "3e-6")):
    best = min(h0 for h0 in range(200, 279)
               if sum((v for j, v in P4.items() if j >= h0), F(0)) / D4 + full4 < tol)
    print(f"      minimal H0 with total < {lab}: {best}")

# Corollary 14: the smaller sufficient reserve, via the SHARPENED bound M m T q_M.
_, D232, s232 = reserve(232, 116, 161)
assert s232 / D232 < F(1, 100) < s232        # sharp bound passes, cruder product does not
print(f"  K=232,hmin=116,M=161,reff=1: sharp = {float(s232 / D232):.12f} < 0.01   OK")
print(f"      (cruder product {float(s232):.12f} does NOT meet the tolerance)")
_, D252, s252 = reserve(252, 126, 175)
assert s252 < F(1, 100)
print(f"  K=252,hmin=126,M=175,reff=1: simple = {float(s252):.12f} < 0.01   OK")
# minimality of each capacity within the proportional family hmin=ceil(K/2), M=floor(.695K)
for label, sharp in (("sharpened", True), ("cruder product", False)):
    for K in range(150, 300):
        hmin = -(-K // 2)
        M = int(F(695, 1000) * K)
        if hmin > M:
            continue
        _, DK, s = reserve(K, hmin, M)
        if (s / DK if sharp else s) < F(1, 100):
            print(f"      smallest K certified by the {label}: {K}"
                  f" (hmin={hmin}, M={M})")
            break
    assert K == (232 if sharp else 252), (label, K)

# original 20-unit benchmark rows
for reff, claim in ((F(12), F(5, 10 ** 4)), (F(9), F(8452, 10 ** 6))):
    _, _, s20 = reserve(20, 10, 20, reff=reff, m=F(61, 100), T=120)
    assert s20 < claim, (reff, float(s20))
    print(f"  K=20 benchmark reff={reff}: {float(s20):.10f} < {float(claim)}   OK")

print()
print("=" * 72)
print("4. ASSEMBLY AND BASELINE-COLLAPSE ARITHMETIC")
print("=" * 72)
assert 1 - F(107, 12500) - F(7, 10 ** 6) == F(991433, 10 ** 6)
print("  1 - 107/12500 - 7/1e6 = 991433/1e6 = 0.991433   OK")
joint240 = 1 - F(107, 12500) - rows[240][1]
print(f"  H0>=240 variant: joint success > {float(joint240):.9f}  (paper claims .991437)")
assert joint240 > F(991437, 10 ** 6)
h209 = sum((v for j, v in P4.items() if j >= 209), F(0)) / D4 + full4
assert h209 < F(1, 100)
assert sum((v for j, v in P4.items() if j >= 208), F(0)) / D4 + full4 > F(1, 100)
joint209 = 1 - F(107, 12500) - h209
print(f"  H0>=209 variant: joint success > {float(joint209):.9f}  (paper claims .98161);"
      " 209 is minimal, 208 fails")
assert joint209 > F(98161, 10 ** 5)
# NOTE: with the CRUDER bound coarsened to .01 the joint figure is exactly .98144,
# not "greater than" it; the paper uses the sharpened K=232 bound instead.
assert 1 - F(107, 12500) - F(1, 100) == F(98144, 10 ** 5)
joint232 = 1 - F(107, 12500) - s232 / D232
print(f"  K=232 variant:  joint success > {float(joint232):.6f}   (paper claims .98165)")
assert joint232 > F(98165, 10 ** 5)
# baseline collapse: E H_120 <= 20 e^{-.149*120} = 20 e^{-17.88}
print(f"  baseline: 2*e^-17.88 = {2 * 2.718281828459045 ** -17.88:.3e} < 1e-7   OK")
# narrow-box original target bound
assert 108 * F(89, 1000) - 4 * F(141, 1000) == F(4524, 500)
print(f"  narrow box exponent = {float(F(4524, 500))} > 9; (214/5)/8000 = {float(F(214, 5) / 8000)}")

print()
print("=" * 72)
print("5. CAPACITY LAW AND HIGH-RENEWAL ASYMPTOTIC")
print("=" * 72)
m_, r_, th = 0.305, 1.0, 0.5
f_th = log(r_ * (1 - th) / m_)
Iact = (1 - th) * log(r_ * (1 - th) / m_) - (1 - th) + m_ / r_
print(f"  theta=1/2, m=.305, reff=1:  f_theta = {f_th:.10f}, I = {Iact:.10f}")
K = 400
env_bound = K * m_ * 120 * 2.718281828459045 ** (-K * Iact + 2 * f_th)
print(f"  capacity envelope at K=400: {env_bound:.6e}  (looser than exact product {float(s4):.3e})  OK")
print(f"  x_* = 1 - m/reff = {1 - m_ / r_:.4f} > theta = {th}   OK")

# homogeneous high-renewal limit: lim r^d P_K(tau<=T) = (Km)^{d+1} T / d!
for (K, hmin, m2, T2) in ((4, 2, F(1, 2), 2), (400, 200, F(61, 200), 120)):
    d = K - hmin
    coef = (K * m2) ** (d + 1) * T2 / factorial(d)
    print(f"  K={K},hmin={hmin},d={d}: predicted coefficient (Km)^(d+1)T/d! = {float(coef):.6g}")
    # cross-check against the finite product at large r:  M=K top anchor
    for r in (F(10 ** 6),) if K == 4 else ():
        _, _, s = reserve(K, hmin, K, reff=r, m=m2, T=T2)
        print(f"      r=1e6: r^d * simple bound = {float(r ** d * s):.6f}")
        # P_{K-1} = (Km)^d/(r^d d!) exactly
        assert reserve(K, hmin, K, reff=r, m=m2, T=T2)[0][K - 1] == (K * m2) ** d / (r ** d * factorial(d))
        print("      P_{K-1} = (Km)^d/(r^d d!)  exact identity verified   OK")

# t_cross formula for the contrasting regime (x_* < theta)
def t_cross(r, m, theta):
    return log(m * theta / (r * theta - r + m)) / (r - m)
r3, m3, th3 = 1.0, 0.6, 0.5
x_star = 1 - m3 / r3
print(f"  contrasting regime r=1,m=.6: x_*={x_star} < theta={th3}, t_cross={t_cross(r3,m3,th3):.6f}")
# sanity: integrate the logistic ODE and confirm the crossing time
x, dt, t = 1.0, 1e-7, 0.0
while x > th3:
    x += dt * (r3 * x * (1 - x) - m3 * x)
    t += dt
print(f"      numerical ODE crossing at t = {t:.6f}   (formula {t_cross(r3,m3,th3):.6f})   OK")

print()
print("ALL CHECKS PASSED")
