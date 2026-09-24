"""Exact certificate replay for every constant quoted in the paper.

Run:  python scripts/check_paper.py
It prints a labelled dump of all constants and ends with ALL CHECKS PASSED.
Everything is exact rational or symbolic arithmetic; no floating point enters a
proof step (floats appear only in the printed descriptive decimals).
"""
import json
import math
import os
import sys
from fractions import Fraction as F
from pathlib import Path

for _k in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_k] = '1'

sys.path.insert(0, str(Path(__file__).resolve().parent))
from exact_engine import reserves, log_enclosure, poly_eval_interval, upper  # noqa: E402

import sympy as sp  # noqa: E402

OUT = {}
CHECKS = []


def chk(name, cond):
    CHECKS.append((name, bool(cond)))
    assert cond, 'FAILED: ' + name


def fl(v):
    return float(v)


# =====================================================================
# 0.  rational enclosure of h = log(8/7) and of log(50/49)
# =====================================================================
h_lo, h_hi = log_enclosure(8, 7)
chk('h enclosure agrees with log(8/7)', abs(fl(h_lo) - math.log(8 / 7)) < 1e-14)
chk('h enclosure is ordered and tight', 0 < h_hi - h_lo < F(1, 10**30))
OUT['h_log87'] = {'lo': str(h_lo), 'hi': str(h_hi), 'float': math.log(8 / 7)}
# the simple upper bound quoted in the paper
chk('log(8/7) < 134657/1008420', h_hi < F(134657, 1008420))

# =====================================================================
# 1.  two-phase extinction formula, the contrast D, and the boundary c_p
# =====================================================================
z, cc = sp.symbols('x c')


def Bsym(r, s):
    return (z**(s + 1) - z**(r + s)) / (r - 1) + (z**2 - z**(s + 1)) / (s - 1)


def Fsym(r1, r2, s1, s2, c):
    return (1 - z**2 - Bsym(r1, s1) - Bsym(r2, s2)
            + (sp.Rational(1, 4) + c) * (Bsym(2 * r1, 2 * s1) + Bsym(2 * r2, 2 * s2))
            + (sp.Rational(1, 2) - 2 * c) * Bsym(r1 + r2, s1 + s2))


Apoly = (z**4 + z**3 + z**2 + z + 1) * (3 * z**5 + 6 * z**4 + 9 * z**3 + 12 * z**2 + 8 * z + 4)
Qpoly = 3 * z**8 + 12 * z**7 + 30 * z**6 + 60 * z**5 + 98 * z**4 + 137 * z**3 + 170 * z**2 + 159 * z + 66
Dsym = sp.factor(Fsym(2, 4, 3, 3, cc) - Fsym(3, 3, 2, 4, cc))
chk('factored contrast identity (9)',
    sp.cancel(Dsym - z**2 * (z - 1)**3 * (4 * cc * Apoly + (z - 1) * Qpoly) / 210) == 0)

cp_sym = sp.cancel((1 - z) * Qpoly / (4 * Apoly))
num, den = sp.fraction(sp.factor(sp.diff(cp_sym, z)))
Ppoly = sp.Poly(-num, z)
chk('c_p derivative = -P/(4A^2)', sp.simplify(den - 4 * Apoly**2) == 0)
chk('all coefficients of P are positive', all(q > 0 for q in Ppoly.all_coeffs()))
OUT['P_coefficients'] = [str(q) for q in Ppoly.all_coeffs()]
chk('P coefficients as printed',
    [int(q) for q in Ppoly.all_coeffs()] ==
    [735, 4410, 11655, 20580, 28560, 31290, 26740, 17850, 9030, 3080, 420])
chk('A(1)=210', Apoly.subs(z, 1) == 210)
chk('Q(1)=735', Qpoly.subs(z, 1) == 735)
chk('c_p(x) -> 33/8 as x -> 0', sp.limit(cp_sym, z, 0) == sp.Rational(33, 8))

# unique feasible boundary  c_p = 1/4
tie = sp.Poly(sp.expand((1 - z) * Qpoly - Apoly), z)
OUT['tie_polynomial'] = str(tie.as_expr())
chk('x_0 bracket', cp_sym.subs(z, sp.Rational(80120, 100000)) > sp.Rational(1, 4)
    > cp_sym.subs(z, sp.Rational(80121, 100000)))
chk('exactly one tie root in (0,1)', sp.polys.polytools.count_roots(tie, 0, 1) == 1)


def cp_s0(x):
    """Exact (c_p(x), s_0(x)) with D(c) = s_0 (c_p - c)."""
    x = F(x)
    A = (x**4 + x**3 + x**2 + x + 1) * (3 * x**5 + 6 * x**4 + 9 * x**3 + 12 * x**2 + 8 * x + 4)
    Q = (3 * x**8 + 12 * x**7 + 30 * x**6 + 60 * x**5 + 98 * x**4
         + 137 * x**3 + 170 * x**2 + 159 * x + 66)
    return (1 - x) * Q / (4 * A), 4 * A * x**2 * (1 - x)**3 / 210


x0 = F(7, 8)
cp, s0 = cp_s0(x0)
chk('c_p(7/8)', cp == F(8967219299, 65423564404))
chk('s_0(7/8)', s0 == F(114491237707, 32985348833280))
OUT['pulse'] = {'x': '7/8', 'c_p': str(cp), 'c_p_float': fl(cp),
                's_0': str(s0), 's_0_float': fl(s0)}


def Dexact(x, c):
    cpx, s0x = cp_s0(x)
    return s0x * (cpx - F(c))


chk('D(-1/5)', Dexact(x0, F(-1, 5)) == F(771817626293, 659706976665600))
chk('D(1/5)', Dexact(x0, F(1, 5)) == -F(48037425121, 219902325555200))
OUT['pulse']['D'] = {str(c): {'exact': str(Dexact(x0, c)), 'float': fl(Dexact(x0, c))}
                     for c in [F(-1, 4), F(-1, 5), F(1, 5), F(1, 4)]}

# extinction probabilities themselves at c = 1/5
FAB = F(sp.Rational(str(sp.nsimplify(Fsym(2, 4, 3, 3, sp.Rational(1, 5)).subs(z, sp.Rational(7, 8)),
                                     rational=True))))
FBA = FAB - Dexact(x0, F(1, 5))
chk('F_AB - F_BA reproduces D(1/5)', FAB - FBA == Dexact(x0, F(1, 5)))
OUT['pulse']['F_AB_c02'] = {'exact': str(FAB), 'float': fl(FAB)}
OUT['pulse']['F_BA_c02'] = {'exact': str(FBA), 'float': fl(FBA)}
chk('one-founder extinction near 3 percent', F(3, 100) < FAB < F(31, 1000))

# =====================================================================
# 2.  reserves:  published occupation V  vs  new sensitivity W
# =====================================================================
V_AB = reserves('AB', x0, sharp=False)
V_BA = reserves('BA', x0, sharp=False)
chk('occupation V_AB reproduces the published value', V_AB == {0: F(957367, 18874368)})
chk('occupation V_BA reproduces the published value', V_BA == {0: F(2552741, 50331648)})
chk('V_AB + V_BA published sum',
    V_AB[0] + V_BA[0] == F(15317159, 150994944))

W_AB_poly = reserves('AB', x0)
W_BA_poly = reserves('BA', x0)
W_AB = upper(W_AB_poly, h_lo, h_hi)
W_BA = upper(W_BA_poly, h_lo, h_hi)
chk('sensitivity reserve beats occupation for AB', W_AB < V_AB[0] / 5)
chk('sensitivity reserve beats occupation for BA', W_BA < V_BA[0] / 5)
OUT['reserves'] = {
    'V_AB': str(V_AB[0]), 'V_BA': str(V_BA[0]),
    'V_AB_float': fl(V_AB[0]), 'V_BA_float': fl(V_BA[0]),
    'W_AB_poly': {str(m): str(v) for m, v in W_AB_poly.items()},
    'W_BA_poly': {str(m): str(v) for m, v in W_BA_poly.items()},
    'W_AB_upper': str(W_AB), 'W_BA_upper': str(W_BA),
    'W_AB_float': fl(W_AB), 'W_BA_float': fl(W_BA),
    'ratio_AB': fl(V_AB[0] / W_AB), 'ratio_BA': fl(V_BA[0] / W_BA),
}
# the rounded rational upper bounds quoted in the paper
W_AB_q = F(58, 10000)
W_BA_q = F(61, 10000)
chk('quoted W_AB bound 0.0058', W_AB < W_AB_q)
chk('quoted W_BA bound 0.0061', W_BA < W_BA_q)

# =====================================================================
# 3.  certified epsilon ranges for the pulse reversal
# =====================================================================
OUT['epsilon'] = {}
for cw in [F(1, 5), F(1, 4)]:
    Dm = Dexact(x0, -cw)          # > 0 : AB preferred
    Dp = Dexact(x0, cw)           # < 0 : BA preferred
    chk(f'opposite signs at c = -+{cw}', Dm > 0 > Dp)
    e_star = min(Dm / W_AB, (-Dp) / W_BA)
    e_old = min(Dm, -Dp) / (V_AB[0] + V_BA[0])
    OUT['epsilon'][str(cw)] = {'eps_star': str(e_star), 'eps_star_float': fl(e_star),
                               'eps_published_style': fl(e_old),
                               'improvement_factor': fl(e_star / e_old)}
# round certified values quoted in the paper
eps5 = F(1, 30)
eps4 = F(1, 16)
chk('c = -+1/5 reversal holds for eps <= 1/30',
    Dexact(x0, F(-1, 5)) - eps5 * W_AB > 0 and -Dexact(x0, F(1, 5)) - eps5 * W_BA > 0)
chk('c = -+1/4 reversal holds for eps <= 1/16',
    Dexact(x0, F(-1, 4)) - eps4 * W_AB > 0 and -Dexact(x0, F(1, 4)) - eps4 * W_BA > 0)
gap5 = min(Dexact(x0, F(-1, 5)) - eps5 * W_AB, -Dexact(x0, F(1, 5)) - eps5 * W_BA)
gap4 = min(Dexact(x0, F(-1, 4)) - eps4 * W_AB, -Dexact(x0, F(1, 4)) - eps4 * W_BA)
chk('gap at eps=1/30 exceeds 1.7e-5', gap5 > F(17, 10**6))
chk('gap at eps=1/16 exceeds 1.5e-5', gap4 > F(15, 10**6))
OUT['epsilon']['gap_1_30'] = {'exact': str(gap5), 'float': fl(gap5)}
OUT['epsilon']['gap_1_16'] = {'exact': str(gap4), 'float': fl(gap4)}
# published certificate for comparison
chk('published occupation certificate gave eps <= 1/500',
    min(Dexact(x0, F(-1, 5)), -Dexact(x0, F(1, 5))) - F(1, 500) * (V_AB[0] + V_BA[0]) > 0)
chk('published certificate expires below 1/450',
    min(Dexact(x0, F(-1, 5)), -Dexact(x0, F(1, 5))) - F(1, 450) * (V_AB[0] + V_BA[0]) < 0)

# uniform decision band gamma_- , gamma_+
g_minus, g_plus = W_AB / s0, W_BA / s0
OUT['band'] = {'gamma_minus': str(g_minus), 'gamma_minus_float': fl(g_minus),
               'gamma_plus': str(g_plus), 'gamma_plus_float': fl(g_plus)}
chk('gamma bounds below 7/4', g_minus < F(7, 4) and g_plus < F(7, 4))

# =====================================================================
# 4.  short pulses: the whole range 0 <= eps <= 1
# =====================================================================
x1 = F(49, 50)
h1_lo, h1_hi = log_enclosure(50, 49)
cp1, s01 = cp_s0(x1)
W1_AB = upper(reserves('AB', x1), h1_lo, h1_hi)
W1_BA = upper(reserves('BA', x1), h1_lo, h1_hi)
chk('short pulse: AB certified at c = -1/4 for every eps <= 1',
    s01 * (cp1 + F(1, 4)) - 1 * W1_AB > 0)
chk('short pulse: BA certified at c = +1/4 for every eps <= 1',
    s01 * (F(1, 4) - cp1) - 1 * W1_BA > 0)
short_gap = min(s01 * (cp1 + F(1, 4)) - W1_AB, s01 * (F(1, 4) - cp1) - W1_BA)
OUT['short_pulse'] = {'x': '49/50', 'h_float': -math.log(49 / 50),
                      'c_p': str(cp1), 'c_p_float': fl(cp1),
                      's_0': str(s01), 's_0_float': fl(s01),
                      'W_AB': fl(W1_AB), 'W_BA': fl(W1_BA),
                      'eps_star': fl(min(s01 * (cp1 + F(1, 4)) / W1_AB,
                                         s01 * (F(1, 4) - cp1) / W1_BA)),
                      'gap_at_eps_1': str(short_gap), 'gap_at_eps_1_float': fl(short_gap)}
chk('short-pulse gap at eps=1 is strictly positive', short_gap > 0)
# the published cubic remainder certificate needs |c| > 16000 h
chk('published tiny-pulse rule is vacuous at h = log(50/49)',
    16000 * h1_lo > F(1, 4))
# ... and requires h <= 1e-6 to reach |c| = 1/5
chk('published tiny-pulse rule at c = 1/5 needs h <= 1/80000',
    16000 * F(1, 80000) == F(1, 5))
# asymptotic band constant  gamma/h  (descriptive)
band_tab = []
for xx in [F(7, 8), F(49, 50), F(99, 100), F(999, 1000), F(9999, 10000)]:
    lo, hi = log_enclosure(xx.denominator, xx.numerator)
    cpx, s0x = cp_s0(xx)
    gp = upper(reserves('BA', xx), lo, hi) / s0x
    band_tab.append({'x': str(xx), 'h': fl(hi), 'gamma_plus': fl(gp),
                     'gamma_plus_over_h': fl(gp / hi)})
OUT['band']['asymptotics'] = band_tab
chk('band constant stays below 25 h', all(b['gamma_plus_over_h'] < 25 for b in band_tab))

# =====================================================================
# 5.  constant actions
# =====================================================================
a = F(1684141, 335544320)
s = F(428807, 251658240)
b = F(6767, 1310720)
cstar = F(144633, 1715228)
chk('constant-action threshold', (b - a) / s == cstar)
# re-derive a, s, b by exact integration of the one-phase formula
xr = sp.Rational(7, 8)


def const_ext(dS, dT, c):
    t = sp.symbols('t')
    T = -sp.log(xr)
    sS = 1 - sp.exp(-dS * (T - t))
    sT = 1 - sp.exp(-dT * (T - t))
    G = (sp.Rational(1, 4) + c) * (sS**2 + sT**2) + (sp.Rational(1, 2) - 2 * c) * sS * sT
    return sp.nsimplify(sp.simplify(sp.integrate(G * sp.exp(-t), (t, 0, T))), rational=True)


FA_sym = sp.expand(const_ext(2, 4, cc))
chk('F_A = a + s c', sp.simplify(FA_sym - (sp.Rational(a.numerator, a.denominator)
                                           + sp.Rational(s.numerator, s.denominator) * cc)) == 0)
FB_sym = sp.expand(const_ext(3, 3, cc))
chk('F_B = b', sp.simplify(FB_sym - sp.Rational(b.numerator, b.denominator)) == 0)

W_A = upper(reserves('A', x0), h_lo, h_hi)
W_B = upper(reserves('B', x0), h_lo, h_hi)
V_A = reserves('A', x0, sharp=False)[0]
V_B = reserves('B', x0, sharp=False)[0]
OUT['constant'] = {'a': str(a), 's': str(s), 'b': str(b), 'c_star': str(cstar),
                   'c_star_float': fl(cstar),
                   'W_A': str(W_A), 'W_A_float': fl(W_A),
                   'W_B': str(W_B), 'W_B_float': fl(W_B),
                   'V_A_float': fl(V_A), 'V_B_float': fl(V_B)}
chk('quoted W_A bound 0.00061', W_A < F(61, 100000))
chk('quoted W_B bound 0.00049', W_B < F(49, 100000))
# published reserve, for comparison
rho_C_old = F(17209, 504210000)
chk('published constant reserve at eps=.001 exceeds the new one at eps=1/100',
    rho_C_old > F(1, 100) * W_A)
OUT['constant']['published_rho_C'] = str(rho_C_old)
OUT['constant']['published_rho_C_float'] = fl(rho_C_old)

# separated 40-division class: admissible epsilon
eps_sep = s / 10 / W_A
OUT['constant']['eps_separated_sup'] = fl(eps_sep)
chk('separated class tolerates eps = 1/4', F(1, 4) * W_A < s / 10 and F(1, 4) * W_B < s / 10)
chk('separated class fails by eps = 1/3', F(1, 3) * W_A > s / 10)

# =====================================================================
# 6.  exact binomial decision rules
# =====================================================================
k_att = F(16, 25)                      # (1-2*eta)^2 at eta = 1/10
chk('attenuation k', (1 - 2 * F(1, 10))**2 == k_att)


def weights(n, p):
    """Integer numerators of Bin(n,p) terms over the common denominator d^n."""
    aa, d = p.numerator, p.denominator
    bb = d - aa
    arr = [bb**n]
    for j in range(n):
        arr.append(arr[-1] * (n - j) * aa // ((j + 1) * bb))
    assert sum(arr) == d**n
    return arr, d**n


def upper_tail(n, p, j0):
    w, d = weights(n, p)
    return F(sum(w[j0:]), d)


def lower_tail(n, p, j1):
    w, d = weights(n, p)
    return F(sum(w[:j1 + 1]), d)


# --- 6a.  40-division separated rule (unchanged cutoffs, wider epsilon range)
pL = F(1, 2) + 2 * k_att * (cstar - F(1, 10))
pU = F(1, 2) + 2 * k_att * (cstar + F(1, 10))
chk('p_L', pL == F(51449691, 107201750))
chk('p_U', pU == F(78893339, 107201750))
errL = upper_tail(40, pL, 25)
errU = lower_tail(40, pU, 24)
chk('40-division error below 1/20 (B side)', errL < F(1, 20))
chk('40-division error below 1/20 (A side)', errU < F(1, 20))
OUT['forty'] = {'p_L': str(pL), 'p_U': str(pU),
                'error_B_side': fl(errL), 'error_A_side': fl(errU),
                'epsilon_range': '1/4'}

# --- 6b.  full-class abstention rules at eps <= 1/100
EPS_ASSAY = F(1, 100)


def abstention(m, t, s_slope, rho_lo, rho_hi, alpha=F(1, 20)):
    """Two-sided exact binomial test around threshold t on the c-axis.

    rho_lo / rho_hi are the reserves on the two sides (already in risk units).
    Returns cutoffs and the exact resolution probability map.
    """
    p_minus = F(1, 2) + 2 * k_att * (t - rho_lo / s_slope)
    p_plus = F(1, 2) + 2 * k_att * (t + rho_hi / s_slope)
    assert 0 < p_minus <= p_plus < 1
    wlo, dlo = weights(m, p_minus)
    whi, dhi = weights(m, p_plus)
    cum = 0
    low_cut = -1
    for j, q in enumerate(wlo):
        cum += q
        if 2 * cum <= alpha * dlo:
            low_cut = j
    rem = dhi
    high_cut = m + 1
    for j, q in enumerate(whi):
        if 2 * rem <= alpha * dhi:
            high_cut = min(high_cut, j)
            break
        rem -= q
    return p_minus, p_plus, low_cut, high_cut


def resolution(m, low_cut, high_cut, c):
    p = F(1, 2) + 2 * k_att * c
    w, d = weights(m, p)
    return F(sum(w[:low_cut + 1]) + sum(w[high_cut:]), d)


# constant actions: low c favours B, high c favours A
pm_c, pp_c, lo_c, hi_c = abstention(200, cstar, s, EPS_ASSAY * W_B, EPS_ASSAY * W_A)
res_c_plus = resolution(200, lo_c, hi_c, F(1, 5))
res_c_minus = resolution(200, lo_c, hi_c, F(-1, 5))
chk('constant-action resolution at c=.2 exceeds .95', res_c_plus > F(19, 20))
chk('constant-action resolution at c=-.2 exceeds .999999', res_c_minus > F(999999, 1000000))
OUT['abstain_constant'] = {'m': 200, 'epsilon': '1/100',
                           'p_minus': str(pm_c), 'p_plus': str(pp_c),
                           'B_if_X_le': lo_c, 'A_if_X_ge': hi_c,
                           'resolution_c_plus_0.2': fl(res_c_plus),
                           'resolution_c_minus_0.2': fl(res_c_minus)}

# pulses: low c favours AB, high c favours BA
pm_p, pp_p, lo_p, hi_p = abstention(1600, cp, s0, EPS_ASSAY * W_AB, EPS_ASSAY * W_BA)
res_p_plus = resolution(1600, lo_p, hi_p, F(1, 5))
res_p_minus = resolution(1600, lo_p, hi_p, F(-1, 5))
chk('pulse resolution at c=.2 exceeds .95', res_p_plus > F(19, 20))
chk('pulse resolution at c=-.2 exceeds .999999', res_p_minus > F(999999, 1000000))
OUT['abstain_pulse'] = {'m': 1600, 'epsilon': '1/100',
                        'p_minus': str(pm_p), 'p_plus': str(pp_p),
                        'AB_if_X_le': lo_p, 'BA_if_X_ge': hi_p,
                        'resolution_c_plus_0.2': fl(res_p_plus),
                        'resolution_c_minus_0.2': fl(res_p_minus)}

# a smaller pulse budget now also clears .95 resolution
for m_try in (800, 900, 1000, 1100, 1200):
    pm_t, pp_t, lo_t, hi_t = abstention(m_try, cp, s0, EPS_ASSAY * W_AB, EPS_ASSAY * W_BA)
    r = resolution(m_try, lo_t, hi_t, F(1, 5))
    if r > F(19, 20):
        OUT['abstain_pulse']['smallest_m_tested_clearing_095'] = {
            'm': m_try, 'AB_if_X_le': lo_t, 'BA_if_X_ge': hi_t, 'resolution': fl(r)}
        break
chk('a 1600-division pulse budget is no longer needed for .95 resolution',
    'smallest_m_tested_clearing_095' in OUT['abstain_pulse'])

# the published rule for comparison (eps <= .001, symmetric occupation reserve)
pm_o, pp_o, lo_o, hi_o = abstention(1600, cp, s0, F(1, 1000) * (V_AB[0] + V_BA[0]),
                                    F(1, 1000) * (V_AB[0] + V_BA[0]))
chk('published pulse cutoffs reproduced', (lo_o, hi_o) == (982, 1177))
OUT['abstain_pulse']['published_rule'] = {'AB_if_X_le': lo_o, 'BA_if_X_ge': hi_o,
                                          'resolution_c_plus_0.2':
                                          fl(resolution(1600, lo_o, hi_o, F(1, 5)))}

# =====================================================================
# 7.  matched direct-endpoint benchmark (Bernstein)
# =====================================================================
qmax = F(3, 500)
chk('extinction stays below qmax on the separated class at every eps',
    a + s / 4 < qmax and b < qmax)
g_bern = s / 10 - EPS_ASSAY * W_A
n_arm = math.ceil(6 * (2 * qmax + 2 * g_bern / 3) / g_bern**2)
chk('Bernstein exponent at least 3', F(n_arm) * g_bern**2 / (2 * (2 * qmax + 2 * g_bern / 3)) >= 3)
chk('exp(3) > 20', sum(F(3)**j / math.factorial(j) for j in range(14)) > 20)
OUT['endpoint'] = {'n_per_arm': n_arm, 'roots': 2 * n_arm, 'g': str(g_bern),
                   'g_float': fl(g_bern), 'published_n_per_arm': 3907136}
chk('endpoint budget improves on the published one', 2 * n_arm < 7814272)

# =====================================================================
# 8.  refinement kernels, effect sizes, regret
# =====================================================================
OUT['persistent'] = []
for p in [F(3, 5), F(2, 5)]:
    for kap in [F(-1, 10), F(1, 10)]:
        K = [p * p + kap, p * (1 - p) - kap, p * (1 - p) - kap, (1 - p)**2 + kap]
        chk(f'persistent kernel nonneg p={p} kappa={kap}', min(K) >= 0 and sum(K) == 1)
        OUT['persistent'].append({'p': str(p), 'kappa': str(kap), 'K': [str(v) for v in K]})

OUT['effect'] = {}
for n in (1, 2, 10):
    d = FAB**n - FBA**n
    OUT['effect'][f'n={n}'] = {'F_AB^n': fl(FAB**n), 'F_BA^n': fl(FBA**n), 'difference': fl(d)}
chk('ranking preserved at ten founders', FAB**10 < FBA**10)
chk('relative one-founder improvement near .72 percent',
    F(7, 1000) < (FBA - FAB) / FAB < F(8, 1000))
OUT['effect']['relative_one_founder'] = fl((FBA - FAB) / FAB)
OUT['effect']['absolute_risk'] = fl(FBA - FAB)

# marker agreement law and the asymmetric-channel identity
aa, bb, cco = sp.symbols('a b c')
chk('asymmetric channel covariance identity',
    sp.simplify(aa**2 + aa * bb + bb**2 * (sp.Rational(1, 4) + cco) - (aa + bb / 2)**2 - bb**2 * cco) == 0)
et = sp.symbols('eta')
chk('noisy agreement probability',
    sp.simplify((sp.Rational(1, 2) + 2 * cco) * ((1 - et)**2 + et**2)
                + (sp.Rational(1, 2) - 2 * cco) * (2 * et * (1 - et))
                - (sp.Rational(1, 2) + 2 * cco * (1 - 2 * et)**2)) == 0)
Lr, Ur = sp.symbols('L U')
chk('balanced minimax regret',
    sp.simplify((-Lr / (Ur - Lr)) * Ur - (1 - (-Lr / (Ur - Lr))) * (-Lr)) == 0)

# =====================================================================
# 9.  the two criteria for the supersolution condition
# =====================================================================
# (a) d_S <= d_T <= 2 d_S in every phase
for lab, ph in [('A', (2, 4)), ('B', (3, 3))]:
    chk(f'criterion (a) rate hypothesis for action {lab}', ph[0] <= ph[1] <= 2 * ph[0])

# (b) arbitrary descendant kernel: 2x^2 - x^6 >= 1, sharp at x_flat^2 = (sqrt5-1)/2
xflat_sq = (sp.sqrt(5) - 1) / 2
chk('x_flat^2 solves 2u - u^3 = 1', sp.simplify(2 * xflat_sq - xflat_sq**3 - 1) == 0)
chk('cubic factorisation A^3-2A+1 = (A-1)(A^2+A-1)',
    sp.expand((z - 1) * (z**2 + z - 1) - (z**3 - 2 * z + 1)) == 0)
for xx in [F(7, 8), F(49, 50)]:
    chk(f'criterion (b) holds at x={xx}', 2 * xx**2 - xx**6 >= 1)
chk('x_flat < x_0  (criterion (b) covers the whole reversal range)',
    xflat_sq < sp.Rational(80120, 100000)**2)
chk('criterion (b) is sharp: it fails just below x_flat',
    2 * F(785, 1000)**2 - F(785, 1000)**6 < 1)
# direct verification of (t^0)^2 <= s^0 on a fine grid, for all four schedules
import math as _m  # noqa: E402
_SCH = {'AB': [(3, 3), (2, 4)], 'BA': [(2, 4), (3, 3)], 'A': [(2, 4)], 'B': [(3, 3)]}
for xx in [F(7, 8), F(49, 50)]:
    hv = -_m.log(float(xx))
    worst = 1.0
    for name, sc in _SCH.items():
        for j in range(4001):
            u = hv * len(sc) * j / 4000
            RS = RT = 0.0
            for kk, (dS, dT) in enumerate(sc):
                w = min(max(u - kk * hv, 0.0), hv)
                RS += dS * w
                RT += dT * w
            s_0, t_0 = 1 - _m.exp(-RS), 1 - _m.exp(-RT)
            worst = min(worst, s_0 - t_0 * t_0)
    chk(f'(t^0)^2 <= s^0 on a fine grid at x={xx}', worst > -1e-12)

# =====================================================================
here = Path(__file__).resolve().parent
(here.parent / 'certificates.json').write_text(json.dumps(OUT, indent=2))
print(json.dumps(OUT, indent=2))
print()
for name, ok in CHECKS:
    print(('  ok   ' if ok else '  FAIL ') + name)
print(f'\n{len(CHECKS)} checks')
assert all(ok for _, ok in CHECKS)
print('ALL CHECKS PASSED')
