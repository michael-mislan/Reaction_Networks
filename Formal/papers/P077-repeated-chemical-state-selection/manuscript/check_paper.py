"""Exact replay of every constant printed in main.tex.

Rigorous comparisons use fractions.Fraction with rational enclosures of log and
exp (series with explicit remainders).  mpmath is used only to print decimal
summaries and for the clearly labelled grid diagnostics at the end; no
statement of the paper rests on a floating-point comparison.

This script proves nothing about the chemical source.  It replays arithmetic
consequences of formulas whose status (Lean-verified or conventionally proved)
is stated in the paper.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from pathlib import Path
import json

from mpmath import mp, mpf, exp as mexp, log as mlog

mp.dps = 60
CHECKS = []
OUT = {}


def check(name, cond):
    CHECKS.append((name, bool(cond)))
    assert cond, name


# ---------------------------------------------------------------- enclosures
def atanh_enclosure(x, terms=40):
    """Rational enclosure of 2*atanh(x) = log((1+x)/(1-x)) for 0 < x < 1."""
    s = F(0)
    for k in range(terms):
        s += x ** (2 * k + 1) / (2 * k + 1)
    rem = x ** (2 * terms + 1) / ((2 * terms + 1) * (1 - x * x))
    return 2 * s, 2 * (s + rem)


LOG2 = atanh_enclosure(F(1, 3))            # log 2
LOG5149 = atanh_enclosure(F(1, 50))        # log(51/49)
LOG32 = atanh_enclosure(F(1, 5))           # log(3/2)


def exp_lower(y, terms=80):
    """Rational lower bound of exp(y) for rational y >= 0 (partial sum)."""
    assert y >= 0
    s, t = F(0), F(1)
    for k in range(terms):
        s += t
        t = t * y / (k + 1)
    return s


def exp_neg_upper(y):
    """Rational upper bound of exp(-y), y >= 0.  The argument is first rounded
    down to a multiple of 1/1000 and capped at 60, which only weakens it."""
    y = min(F(int(y * 1000), 1000), F(60))
    return 1 / exp_lower(y, terms=260)


def exp_neg_lower(y, terms=60):
    """Rational lower bound of exp(-y) for 0 <= y <= 1 (alternating series,
    even number of terms ends on a negative term)."""
    assert 0 <= y <= 1 and terms % 2 == 0
    s, t = F(0), F(1)
    for k in range(terms):
        s += t
        t = -t * y / (k + 1)
    return s


def dec(x, n=12):
    return mp.nstr(mpf(x.numerator) / mpf(x.denominator), n)


# ------------------------------------------------------------ basic constants
EPS = F(1, 50)
RHO = (1 - EPS) / (4 * (1 + EPS))
R = 1 / RHO
LAM = F(3, 2)
RHOS = RHO * LAM
RS = 1 / RHOS
check("rho = 49/204", RHO == F(49, 204))
check("R = 204/49", R == F(204, 49))
check("rho_* = 49/136", RHOS == F(49, 136))
check("R_* = 136/49", RS == F(136, 49))

# g = (3/5) log 4 - 19/500 - log(51/49), enclosure
g_lo = F(6, 5) * LOG2[0] - F(19, 500) - LOG5149[1]
g_hi = F(6, 5) * LOG2[1] - F(19, 500) - LOG5149[0]
check("g > 3/4", g_lo > F(3, 4))
check("g in (0.753771282, 0.753771283)", F(753771282, 10**9) < g_lo and g_hi < F(753771283, 10**9))
b_lo = F(6, 5) * LOG2[0] - F(19, 500)
check("b > 0.7937", b_lo > F(7937, 10000))

# minority growth factor: 4^(8/25) e^(-19/500) > 3/2
lam_margin_lo = F(16, 25) * LOG2[0] - F(19, 500) - LOG32[1]
check("(8/25) log 4 - 19/500 > log(3/2)", lam_margin_lo > 0)
OUT["lambda_margin"] = dec(lam_margin_lo, 8)

gm = mpf(3) / 5 * mlog(4) - mpf(19) / 500 - mlog(mpf(51) / 49)
OUT["g"] = mp.nstr(gm, 15)
OUT["exp_g"] = mp.nstr(mexp(gm), 10)
OUT["coef_necessary_1_over_g"] = mp.nstr(1 / gm, 9)
OUT["coef_compiled_1_over_logR"] = mp.nstr(1 / mlog(mpf(204) / 49), 9)
OUT["coef_refined_1_over_logRstar"] = mp.nstr(1 / mlog(mpf(136) / 49), 9)
OUT["R"] = mp.nstr(mpf(204) / 49, 8)
OUT["R_star"] = mp.nstr(mpf(136) / 49, 8)
OUT["reduced_model_base"] = mp.nstr(mpf(4) ** (1 - mpf("0.99579401232") / mpf("2.97636724377")), 10)
OUT["sandwich_eta_ceiling"] = mp.nstr(mpf("0.99") * mpf("0.999") / 3, 6)

D0 = 512 * 10**18
N0 = 140 * 10**18
T = 8 * 10**11
K = 10


def binary_chem_envelope(K, M, u, T, extra_pure_terms=0):
    """K*E <= K[M(74+16u+Tu/21)+2+extra]2^-128 + 2KM 2^-64, valid for u = 128."""
    return (K * (M * (74 + 16 * u + F(T * u, 21)) + 2 + extra_pure_terms) * F(1, 2**128)
            + F(2 * K * M, 2**64))


# ------------------------------------------------ compiled witness (Theorem A)
M1, N1 = 10**13, 65536 * 10**18
u1 = F(N1, D0)
check("u = 128 for N = 6.5536e22", u1 == 128)
check("N >= N0", N1 >= N0)
transfer1 = F(80000, M1) * sum(R**j for j in range(K))
check("closed form of transfer sum", transfer1 == F(80000, M1) * (R**K - 1) / (R - 1))
chem1 = binary_chem_envelope(K, M1, 128, T)
service = F(2 * K, 10000)
fail1 = transfer1 + chem1 + service
check("compiled witness failure < 0.006", fail1 < F(6, 1000))
OUT["compiled"] = {"transfer": dec(transfer1), "chem": dec(chem1), "service": dec(service),
                   "total": dec(fail1), "confidence_replay": dec(1 - fail1, 13)}
# terminal composition
odds_lower = 2**11 * exp_neg_lower(F(19, 50)) * F(49, 51)**10
check("exp(10g - log 2) > 938.76", odds_lower > F(93876, 100))
check("high fraction > 0.998935", odds_lower / (1 + odds_lower) > F(998935, 10**6))
OUT["odds_10"] = dec(odds_lower, 10)
OUT["fraction_10"] = dec(odds_lower / (1 + odds_lower), 13)
floor1 = F(M1, 4) * RHO**10
cl1 = -(-floor1.numerator // floor1.denominator)
check("compiled minority floor 1598083", cl1 == 1598083)
OUT["compiled"]["minority_floor_real"] = dec(floor1, 12)

# ------------------------------------------------ refined witness (Theorem B)
M2, N2 = 4 * 10**9, 65536 * 10**18


def one_type_cheb(mu):
    return 1 / (EPS**2 * mu)


def one_type_exp_upper(mu):
    """Rigorous upper bound of exp(-eps^2 mu/2) + exp(-eps^2 mu/(2+eps))."""
    return exp_neg_upper(EPS**2 * mu / 2) + exp_neg_upper(EPS**2 * mu / (2 + EPS))


def one_type(mu):
    return min(one_type_cheb(mu), one_type_exp_upper(mu))


def tau_refined(M, j):
    """Low type at share floor rho_*^j/2, high type at share >= 1/2."""
    return one_type(F(3, 32) * M * RHOS**j) + one_type(F(3, 32) * M)


tau2 = [tau_refined(M2, j) for j in range(K)]
transfer2 = sum(tau2)
chem2 = binary_chem_envelope(K, M2, 128, T, extra_pure_terms=1)
fail2 = transfer2 + chem2 + service
check("refined witness failure < 0.003", fail2 < F(3, 1000))
check("refined witness transfer < 0.00098", transfer2 < F(98, 100000))
service_fine = F(2 * K, 10**6)
check("refined witness with finer quotas < 0.001", transfer2 + chem2 + service_fine < F(1, 1000))
OUT["refined"] = {"transfer": dec(transfer2), "chem": dec(chem2), "service": dec(service),
                  "total": dec(fail2), "confidence_replay": dec(1 - fail2, 10),
                  "total_fine_quotas": dec(transfer2 + chem2 + service_fine, 10),
                  "tau_last": dec(tau2[-1]), "tau_second_last": dec(tau2[-2], 6)}
floor2 = F(M2, 4) * RHOS**10
cl2 = -(-floor2.numerator // floor2.denominator)
OUT["refined"]["minority_floor_real"] = dec(floor2, 12)
OUT["refined"]["minority_floor_int"] = cl2
check("refined minority floor 36862", cl2 == 36862)
check("M ratio 2500", F(M1, M2) == 2500)
check("NM ratio 2500", F(M1 * N1, M2 * N2) == 2500)
# the second-moment form of Theorem B at the same M does not close
cheb_refined_M2 = F(80000, 3 * M2) * (RS**K - 1) / (RS - 1) + F(10000 * K, M2)
OUT["refined"]["second_moment_only_at_same_M"] = dec(cheb_refined_M2, 6)
check("second-moment form alone does not close M = 4e9", cheb_refined_M2 > F(1, 10))


# --------------------------------------------- required population, K = 10
def min_M(fun, delta, lo=2, hi=10**16):
    """Smallest even M with fun(M) <= delta, assuming fun decreasing (bisection on mpf)."""
    while hi - lo > 2:
        mid = (lo + hi) // 2
        if fun(mid) <= delta:
            hi = mid
        else:
            lo = mid
    return hi + (hi % 2)


def f_compiled(M):
    return mpf(80000) / M * sum((mpf(204) / 49) ** j for j in range(K))


def c_mp(mu, e=mpf(1) / 50):
    return min(1 / (e * e * mu), mexp(-e * e * mu / 2) + mexp(-e * e * mu / (2 + e)))


def f_exp_original_floors(M):
    return sum(2 * c_mp(mpf(M) / 16 * (mpf(49) / 204) ** j) for j in range(K))


def f_cheb_refined(M):
    return sum(mpf(80000) / (3 * M) * (mpf(136) / 49) ** j + mpf(10000) / M for j in range(K))


def f_refined(M):
    return sum(c_mp(mpf(3) / 32 * M * (mpf(49) / 136) ** j) + c_mp(mpf(3) / 32 * M) for j in range(K))


dt = mpf(4) / 1000
OUT["required_M_K10_delta_0.004"] = {
    "compiled_second_moment": mp.nstr(mpf(min_M(f_compiled, dt)), 5),
    "exponential_tail_original_floors": mp.nstr(mpf(min_M(f_exp_original_floors, dt)), 5),
    "minority_growth_second_moment": mp.nstr(mpf(min_M(f_cheb_refined, dt)), 5),
    "refined_theorem_B": mp.nstr(mpf(min_M(f_refined, dt)), 5),
    "necessary_1_plus_exp(10g)/2": mp.nstr(1 + mexp(10 * gm) / 2, 6),
}
# simple sufficient rule of Corollary: M >= (161600/3) R*^(K-1) log(4K/delta)
rule = mpf(161600) / 3 * (mpf(136) / 49) ** (K - 1) * mlog(4 * K / dt)
OUT["simple_rule_M_K10"] = mp.nstr(rule, 5)
check("simple rule is sufficient at K=10 (diagnostic)", f_refined(rule) <= dt)

# ----------------------------------------------------------- target gain table
for frac, kk in [(F(9, 10), 4), (F(95, 100), 5), (F(99, 100), 8), (F(999, 1000), 11)]:
    target = 2 * frac / (1 - frac)
    # need log(target) <= kk*g ; rigorous: target <= exp_lower(kk*g_lo)
    check(f"gain table {frac}", target <= exp_lower(kk * g_lo))
    check(f"gain table minimal {frac}", mlog(mpf(target.numerator) / target.denominator) > (kk - 1) * gm)

# ------------------------------------------------------------- reserve ceiling
# K g < log(2(M-r)/r): r = 1 gives the basic ceiling
OUT["ceiling_K_M4e9"] = mp.nstr(mlog(2 * (mpf(M2) - 1)) / gm, 6)
OUT["ceiling_K_M1e13"] = mp.nstr(mlog(2 * (mpf(M1) - 1)) / gm, 6)

# ---------------------------------------------------------------- rarity
loss = {c: F(comb(400 - c, 100), comb(400, 100)) for c in (1, 4, 20)}
check("loss c=1 is 3/4", loss[1] == F(3, 4))
check("loss c=4", loss[4] == F(13231647, 42029596))
OUT["loss"] = {str(c): dec(v, 9) for c, v in loss.items()}
for c, v in loss.items():
    up = mexp(-mpf(100 * c) / 400)
    lo = (1 - mpf(c) / (400 - 100 + 1)) ** 100
    check(f"loss bounds c={c} (diagnostic)", lo <= mpf(v.numerator) / v.denominator <= up)

# heterogeneity diagnostic: all 70 four-subsets of eight endpoint cells
hetero = {}
for label, sizes in {"equal": [F(1)] * 8,
                     "mixed": [F(1), F(1), F(19, 10), F(19, 10)] * 2}.items():
    weights = [[v / 2 if (i < 4) == b else F(0) for i, v in enumerate(sizes)] for b in (True, False)]
    subsets = list(combinations(range(8), 4))
    vals = [[sum((w[i] for i in s), F(0)) for s in subsets] for w in weights]
    means = [sum(v, F(0)) / len(subsets) for v in vals]
    n, m = 8, 4
    for w, v, mu in zip(weights, vals, means):
        var = sum(((x - mu) ** 2 for x in v), F(0)) / len(subsets)
        exact = (F(m * (n - m), n * (n - 1))
                 * (sum(x * x for x in w) - sum(w) ** 2 / n))
        check(f"exact variance identity {label}", var == exact)
        check(f"variance <= (n-m)/(n-1) mean {label}", var <= F(n - m, n - 1) * mu)
    hetero[label] = {}
    for e in (F(1, 50), F(1, 2)):
        fail = F(sum(any(abs(vals[t][a] - means[t]) > e * means[t] for t in range(2))
                     for a in range(len(subsets))), len(subsets))
        hetero[label][str(e)] = str(fail)
check("hetero equal 17/35", hetero["equal"]["1/50"] == "17/35")
check("hetero mixed 27/35", hetero["mixed"]["1/50"] == "27/35")
check("hetero equal 1/35", hetero["equal"]["1/2"] == "1/35")
check("hetero mixed 13/35", hetero["mixed"]["1/2"] == "13/35")
OUT["heterogeneity"] = hetero

# normalization refinement: reciprocal recurrence and 155/154 cap
q = F(1, 2)
for j in range(12):
    check(f"normalization closed form j={j}", 1 / q == F(308, 155) * R**j + F(2, 155))
    check(f"normalization cap j={j}", q / (F(1, 2) * RHO**j) <= F(155, 154))
    q = (1 - EPS) * q / (4 * (1 + EPS) - 2 * EPS * q)

# ------------------------------------------------------------ resource accounts
def accounts(K, N, M):
    NM = N * M
    return {"NM": NM, "operating_precursor": (8 * K - 4) * NM, "growth": (6 * K - 3) * NM,
            "residual": (2 * K - 1) * NM, "discard": (7 * K - 4) * NM, "terminal": 8 * NM,
            "total": (8 * K + 4) * NM, "duration": K * (T + 5376)}


acc1, acc2 = accounts(K, N1, M1), accounts(K, N2, M2)
check("compiled operating precursor", acc1["operating_precursor"] == 4980736 * 10**31)
check("compiled total precursor", acc1["total"] == 5505024 * 10**31)
check("duration", acc1["duration"] == 8000000053760)
OUT["accounts_compiled"] = {k: mp.nstr(mpf(v), 8) for k, v in acc1.items()}
OUT["accounts_refined"] = {k: mp.nstr(mpf(v), 8) for k, v in acc2.items()}
check("refined NM", acc2["NM"] == 262144 * 10**27)

# explicit clocks of the companion paper and quotas with allowances < 1e-4
for tag, (N, M) in {"compiled": (N1, M1), "refined": (N2, M2)}.items():
    qR, qB = 34000 * N, 280000 * N * M
    JB = 10**4 * T * qB + 1
    JR = 10**4 * M * 5376 * qR + 1
    check(f"quota allowances {tag}", F(T * qB, JB) < F(1, 10**4) and F(M * 5376 * qR, JR) < F(1, 10**4))
    OUT[f"quotas_{tag}"] = {"qR": mp.nstr(mpf(qR), 8), "qB": mp.nstr(mpf(qB), 8),
                            "JB": mp.nstr(mpf(JB), 8), "JR": mp.nstr(mpf(JR), 8),
                            "exchange_allowance": mp.nstr(mpf(K * (JB + M * JR)), 8)}

# units: N / N_A
NA = mpf("6.02214076e23")
OUT["N_over_NA_mol"] = mp.nstr(mpf(N1) / NA, 6)
OUT["N0_over_NA_mol"] = mp.nstr(mpf(N0) / NA, 6)
OUT["pL_at_mM_scale"] = mp.nstr(NA * mpf("1e-12") * mpf("1e-3"), 4)
OUT["fL_at_mM_scale"] = mp.nstr(NA * mpf("1e-15") * mpf("1e-3"), 4)

# molecular-scale rule of Proposition (chemical sizing), evaluated
CT = 142 + mpf(4 * T) / 21
for tag, M in (("compiled", M1), ("refined", M2)):
    OUT[f"sizing_rule_N_{tag}"] = mp.nstr(4 * D0 * mlog(CT * M * K / mpf("1e-5")), 6)

# ------------------------------------------ grid diagnostics (not proofs)
import random
random.seed(20260919)
worst = mpf("-inf")
for _ in range(4000):
    Nn = mpf(10) ** random.uniform(3, 23)
    H = Nn * mpf(10) ** random.uniform(0, 12)
    L = Nn * mpf(10) ** random.uniform(0, 12)
    aH = mpf(random.uniform(2.97, 3.0))
    aL = mpf(random.uniform(0.99, 1.01))
    vH = (Nn / 1000) * (mpf(8) / 25) * mlog(1 + 1 / (H + L))
    vL = (Nn / 1000) * (-mlog(1 + 1 / L) + (mpf(8) / 25) * mlog(1 + 1 / (H + L)))
    val = (aH * H * (mexp(vH) - 1) + aL * L * (mexp(vL) - 1)) / Nn
    worst = max(worst, val)
check("scalar minority barrier negative on random grid (diagnostic)", worst < 0)
OUT["scalar_barrier_worst_over_N"] = mp.nstr(worst, 6)
for i in range(1, 1000):
    e = mpf(i) / 1000
    check("Chernoff upper exponent (diagnostic)", (1 + e) * mlog(1 + e) - e >= e * e / (2 + e))
    check("Chernoff lower exponent (diagnostic)", (1 - e) * mlog(1 - e) + e >= e * e / 2)
# exact check of the exponential tail against the eight-cell enumeration
for label, sizes in {"equal": [F(1)] * 8, "mixed": [F(1), F(1), F(19, 10), F(19, 10)] * 2}.items():
    w = [v / 2 if i < 4 else F(0) for i, v in enumerate(sizes)]
    subsets = list(combinations(range(8), 4))
    vals = [sum((w[i] for i in s), F(0)) for s in subsets]
    mu = sum(vals, F(0)) / len(subsets)
    for e in (F(1, 4), F(1, 2), F(9, 10)):
        exact = F(sum(abs(x - mu) > e * mu for x in vals), len(subsets))
        y = e * e * mu
        ym, em = mpf(y.numerator) / y.denominator, mpf(e.numerator) / e.denominator
        bound = mexp(-ym / 2) + mexp(-ym / (2 + em))
        check(f"exponential tail dominates exact law {label} {e} (diagnostic)",
              mpf(exact.numerator) / exact.denominator <= bound)

OUT["checks_passed"] = len(CHECKS)
Path(__file__).with_name("check_paper_output.json").write_text(json.dumps(OUT, indent=2) + "\n")
print(json.dumps(OUT, indent=2))
print(f"{len(CHECKS)} checks passed")
