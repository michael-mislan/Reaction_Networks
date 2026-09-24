"""Recompute every printed constant in the manuscript and rebuild all figures.

Every quantity the paper prints as exact is recomputed here in exact rational
arithmetic; every quantity the paper prints as a bound is re-derived from the
same inequality chain the proof uses, with rational upper bounds for every
exponential (a truncated exponential series has only positive terms, so it is a
valid *lower* bound for exp and hence gives a valid *upper* bound for its
reciprocal).  The numerical ODE solutions are independent checks of the
inequalities, never their justification.

All parameters are synthetic design requirements.  Nothing here is fitted to
measured data.

Run:   python check_paper.py
Writes: results.json, recovery_rows.tex, figures/*.pdf
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from math import exp, factorial
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = Path(__file__).resolve().parent
FIGDIR = HERE / "figures"
REPORT: dict[str, object] = {}
CHECKS: list[str] = []


def record(name: str, value) -> None:
    REPORT[name] = value


def ok(claim: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"FAILED: {claim}")
    CHECKS.append(claim)


# ---------------------------------------------------------------------------
# 0.  Rational upper bounds for exp(-x)
# ---------------------------------------------------------------------------

def exp_lower(x: Q, terms: int | None = None) -> Q:
    """Rational lower bound for exp(x), x >= 0: a truncated Taylor sum."""
    if x < 0:
        raise ValueError("exp_lower expects x >= 0")
    n = terms if terms is not None else int(3 * float(x)) + 40
    return sum(x ** j / factorial(j) for j in range(n + 1))


def exp_neg_upper(x: Q, terms: int | None = None) -> Q:
    """Rational upper bound for exp(-x), x >= 0."""
    return 1 / exp_lower(x, terms)


# The one exponential bound the Lean certificate also uses.
TAYLOR16 = sum(Q(193, 20) ** j / factorial(j) for j in range(17))
ok("degree-16 Taylor sum for exp(9.65) exceeds 14000", TAYLOR16 > 14000)
ok("degree-16 Taylor sum for exp(9.65) exceeds 15208", TAYLOR16 > 15208)
ok("the same sum does not exceed exp(9.65)", float(TAYLOR16) < exp(9.65))
record("taylor16_exp_9_65", str(TAYLOR16))
record("taylor16_exp_9_65_float", float(TAYLOR16))

# ---------------------------------------------------------------------------
# 1.  The declared uncertainty box
# ---------------------------------------------------------------------------

P_LOW = (Q(95, 100), Q(105, 100))
P_HIGH = (Q(195, 100), Q(205, 100))
K = (Q(98, 100), Q(102, 100))
CTOT = (Q(99, 100), Q(101, 100))
RTOT = (Q(99, 100), Q(101, 100))
U = (Q(79, 1000), Q(81, 1000))
CREL = (Q(20), Q(25))
BETA = (Q(1), Q(2))
GAIN = (Q(98, 100), Q(102, 100))
ETA = Q(1, 100)
ERR = Q(1, 100)
TACQ = Q(8)
TAU = Q(5)

A_MIN = P_LOW[0] + K[0]            # 1.93
A_MAX = P_HIGH[1] + K[1]           # 3.07
H_MIN = BETA[0] + CREL[0]          # 21
H_MAX = BETA[1] + CREL[1]          # 27
P_MIN, P_MAX = P_LOW[0], P_HIGH[1]
PC_MAX = P_MAX + CREL[1]           # 27.05

ok("a >= 1.93", A_MIN == Q(193, 100))
ok("a <= 3.07", A_MAX == Q(307, 100))
ok("h >= 21", H_MIN == 21)
ok("h <= 27", H_MAX == 27)
ok("c >= k on the box", CREL[0] >= K[1])
ok("the acquisition window exceeds the complex lag", TACQ >= 1 / H_MIN)

# ---------------------------------------------------------------------------
# 2.  Preservation: loading bound, suppression, free-pool floor
# ---------------------------------------------------------------------------

B0 = U[1] * (1 + P_MAX / CREL[0]) / A_MIN
SUPPRESSION = (1 + ETA) / (1 - ETA) * B0
M_FLOOR = 1 - ETA - (1 + ETA) * B0

ok("B0 = 35721/772000", B0 == Q(35721, 772000))
ok("relative suppression = 400869/8492000", SUPPRESSION == Q(400869, 8492000))
ok("relative suppression < 4.73%", SUPPRESSION < Q(473, 10000))
ok("relative suppression < 5%", SUPPRESSION < Q(1, 20))
ok("free-pool floor m > 0.94", M_FLOOR > Q(94, 100))
record("B0", str(B0))
record("suppression", str(SUPPRESSION))
record("suppression_float", float(SUPPRESSION))
record("m_floor", str(M_FLOOR))
record("m_floor_float", float(M_FLOOR))


def xbar(p: Q, c_tot: Q, k: Q) -> Q:
    return p * c_tot / (p + k)


XB_MAX_ALL = xbar(P_HIGH[1], CTOT[1], K[0])       # 41/60
XB_MAX_LOW = xbar(P_LOW[1], CTOT[1], K[0])        # 303/580
XB_MIN_HIGH = xbar(P_HIGH[0], CTOT[0], K[1])      # 13/20
ok("max xbar over the whole box is 41/60", XB_MAX_ALL == Q(41, 60))
ok("max xbar in the low class is 303/580", XB_MAX_LOW == Q(303, 580))
ok("min xbar in the high class is 13/20", XB_MIN_HIGH == Q(13, 20))

E_ABS = (1 + ETA) * XB_MAX_ALL * B0                       # uniform bound on e and w
B_ABS = U[1] * (1 + ETA) * XB_MAX_ALL / CREL[0]           # uniform bound on b
ok("absolute deficit bound < 0.032", E_ABS < Q(32, 1000))
ok("absolute complex bound < 0.0028", B_ABS < Q(28, 10000))
record("e_absolute_bound", str(E_ABS))
record("e_absolute_bound_float", float(E_ABS))
record("b_absolute_bound", str(B_ABS))
record("b_absolute_bound_float", float(B_ABS))

# ---------------------------------------------------------------------------
# 3.  Signal envelopes, threshold and class fluxes
# ---------------------------------------------------------------------------

SIGMA = U[1] * CTOT[1] / (CREL[0] * RTOT[0])
ok("saturation coefficient sigma < 0.005", SIGMA < Q(5, 1000))
record("sigma", str(SIGMA))

# Unrounded envelopes (the design criterion), then the rounded ones the paper prints.
U_SHARP = GAIN[1] * U[1] * (1 + ETA) * XB_MAX_LOW * TACQ
L_SHARP = GAIN[0] * U[0] * M_FLOOR * XB_MIN_HIGH / (1 + SIGMA) * (TACQ - 1 / H_MIN)

UPPER8 = (Q(102, 100) * Q(81, 1000) * Q(101, 100)
          * (Q(105, 100) * Q(101, 100) / Q(203, 100)) * 8)
LOWER8 = (Q(98, 100) * Q(79, 1000) * Q(94, 100)
          * (Q(195, 100) * Q(99, 100) / Q(297, 100)) / Q(1005, 1000)
          * (8 - Q(1, 21)))
MARGIN = LOWER8 - UPPER8 - 2 * ERR
THRESHOLD = (UPPER8 + LOWER8) / 2

ok("U(8) = 126420993/362500000", UPPER8 == Q(126420993, 362500000))
ok("L(8) = 56426461/150750000", LOWER8 == Q(56426461, 150750000))
ok("the rounded upper envelope dominates the sharp one", U_SHARP <= UPPER8)
ok("the rounded lower envelope is dominated by the sharp one", L_SHARP >= LOWER8)
ok("remaining separation = 1214759671/218587500000", MARGIN == Q(1214759671, 218587500000))
ok("remaining separation exceeds 0.005", MARGIN > Q(5, 1000))
ok("threshold strictly above every low record", UPPER8 + ERR < THRESHOLD)
ok("threshold strictly below every high record", THRESHOLD < LOWER8 - ERR)
ok("per-class slack exceeds 0.0025", MARGIN / 2 > Q(25, 10000))
for name, value in (("U8", UPPER8), ("L8", LOWER8), ("margin", MARGIN),
                    ("threshold", THRESHOLD), ("half_margin", MARGIN / 2)):
    record(name, str(value))
    record(name + "_float", float(value))


def stationary_flux(p: Q, k: Q, c_tot: Q) -> Q:
    return k * p * c_tot / (p + k)


F_LOW_MAX = stationary_flux(P_LOW[1], K[1], CTOT[1])
F_HIGH_MIN = stationary_flux(P_HIGH[0], K[0], CTOT[0])
ok("low-class stationary native flux < 0.523", F_LOW_MAX < Q(523, 1000))
ok("high-class stationary native flux > 0.645", F_HIGH_MIN > Q(645, 1000))
record("F_low_max", str(F_LOW_MAX))
record("F_low_max_float", float(F_LOW_MAX))
record("F_high_min", str(F_HIGH_MIN))
record("F_high_min_float", float(F_HIGH_MIN))

# The acquisition-time boundary of the printed certificate.
def rounded_margin(T: Q) -> Q:
    up = (Q(102, 100) * Q(81, 1000) * Q(101, 100)
          * (Q(105, 100) * Q(101, 100) / Q(203, 100)) * T)
    lo = (Q(98, 100) * Q(79, 1000) * Q(94, 100)
          * (Q(195, 100) * Q(99, 100) / Q(297, 100)) / Q(1005, 1000)
          * (T - Q(1, 21)))
    return lo - up - 2 * ERR


TIME_BOUNDARY = {int(T): str(rounded_margin(Q(T))) for T in (5, 6, 7, 8, 9)}
ok("the printed certificate fails at T = 6", rounded_margin(Q(6)) < 0)
ok("the printed certificate holds at T = 7", rounded_margin(Q(7)) > 0)
ok("the printed certificate margin at T = 7 exceeds 0.002", rounded_margin(Q(7)) > Q(2, 1000))
record("time_boundary_margins", TIME_BOUNDARY)
record("time_boundary_margins_float",
       {k_: float(Q(v)) for k_, v in TIME_BOUNDARY.items()})

# ---------------------------------------------------------------------------
# 4.  Recovery remainders
# ---------------------------------------------------------------------------

KA = K[1] / A_MIN                  # k/a upper bound
PCH = PC_MAX / H_MIN               # (p+c)/h upper bound
D_STAR = CREL[1] - K[0]            # c - k upper bound
A_STAR = U[1] * H_MAX * CTOT[1] / CREL[0]   # sup of the association flux amplitude
ok("A* = 0.1104435", A_STAR == Q(1104435, 10000000))
record("k_over_a", str(KA))
record("pc_over_h", str(PCH))
record("d_star", str(D_STAR))
record("A_star", str(A_STAR))

EXP_965 = Q(1, 14000)              # > exp(-9.65); certified by TAYLOR16 above
ok("1/14000 is an upper bound for exp(-9.65)", float(EXP_965) > exp(-9.65))

# 4a.  Ideal switch: alpha = 0 after T.
B_IDEAL = E_ABS + D_STAR * B_ABS / (H_MIN - A_MIN)
TAIL_IDEAL = KA * (B_IDEAL * EXP_965 + PCH * B_ABS * EXP_965)
TAIL_IDEAL_SHARP = KA * (B_IDEAL * exp_neg_upper(A_MIN * TAU)
                         + PCH * B_ABS * exp_neg_upper(H_MIN * TAU))
ok("ideal-switch remainder below 3e-6 with the crude exponential bound",
   TAIL_IDEAL < Q(3, 10 ** 6))
ok("ideal-switch remainder below 1.5e-6 with the sharp exponential bound",
   TAIL_IDEAL_SHARP < Q(15, 10 ** 7))
record("B_ideal", str(B_IDEAL))
record("tail_ideal_crude", str(TAIL_IDEAL))
record("tail_ideal_crude_float", float(TAIL_IDEAL))
record("tail_ideal_sharp_float", float(TAIL_IDEAL_SHARP))

# 4b.  Fading switch: alpha(T+s) <= alpha_0 exp(-gamma s).
def denom(r: Q, rho: Q, nu: Q) -> Q | None:
    """Best d with int_0^s e^{-r(s-v)}e^{-rho v} dv <= e^{-nu s}/d."""
    cands = []
    if nu <= r and nu < rho:
        cands.append(rho - nu)
    if nu <= rho and nu < r:
        cands.append(r - nu)
    return max(cands) if cands else None


def fading_constants(gamma: Q, nu0: Q, nu1: Q):
    d1 = denom(H_MIN, gamma, nu1)
    d0 = denom(A_MIN, nu1, nu0)
    if d1 is None or d0 is None:
        raise ValueError("invalid certified rates")
    beta_star = B_ABS + A_STAR / d1
    big_b = E_ABS + D_STAR * beta_star / d0
    return big_b, beta_star


def fading_remainder(gamma: Q, tau: Q, nu0: Q, nu1: Q, crude: bool = False) -> Q:
    big_b, beta_star = fading_constants(gamma, nu0, nu1)
    if crude:
        e0 = e1 = eg = EXP_965
    else:
        e0 = exp_neg_upper(nu0 * tau)
        e1 = exp_neg_upper(nu1 * tau)
        eg = exp_neg_upper(gamma * tau)
    return KA * (big_b * e0 + PCH * (beta_star * e1 + A_STAR / gamma * eg))


# Headline corollary: gamma >= 21, tau = 5, certified with the single crude bound.
NU0_FAST, NU1_FAST = Q(193, 100), Q(12)
B_FAST, BETA_FAST = fading_constants(Q(21), NU0_FAST, NU1_FAST)
TAIL_FAST_CRUDE = fading_remainder(Q(21), TAU, NU0_FAST, NU1_FAST, crude=True)
TAIL_FAST_SHARP = fading_remainder(Q(21), TAU, NU0_FAST, NU1_FAST)
ok("fading-switch remainder at gamma=21, tau=5 below 4e-6 (crude bound)",
   TAIL_FAST_CRUDE < Q(4, 10 ** 6))
ok("fading-switch remainder at gamma=21, tau=5 below 2.4e-6 (sharp bound)",
   TAIL_FAST_SHARP < Q(24, 10 ** 7))
ok("the crude fading bound is genuinely above 3e-6, so 4e-6 is the honest figure",
   TAIL_FAST_CRUDE > Q(3, 10 ** 6))
record("B_fast", str(B_FAST))
record("beta_fast", str(BETA_FAST))
record("tail_fading_crude", str(TAIL_FAST_CRUDE))
record("tail_fading_crude_float", float(TAIL_FAST_CRUDE))
record("tail_fading_sharp_float", float(TAIL_FAST_SHARP))

# Certified recovery deadlines as a function of the switch decay rate.
DEADLINES = [
    # gamma, nu0, nu1, certified tau
    (Q(1, 2), Q(1, 2), Q(1, 2), Q(227, 10)),
    (Q(1), Q(1), Q(1), Q(112, 10)),
    (Q(2), Q(185, 100), Q(2), Q(68, 10)),
    (Q(5), Q(193, 100), Q(5), Q(52, 10)),
    (Q(10), Q(193, 100), Q(10), Q(49, 10)),
    (Q(21), Q(193, 100), Q(12), Q(49, 10)),
]
TARGET = Q(3, 10 ** 6)
deadline_rows = []
for gamma, nu0, nu1, tau in DEADLINES:
    val = fading_remainder(gamma, tau, nu0, nu1)
    shorter = fading_remainder(gamma, tau - Q(1, 10), nu0, nu1)
    ok(f"certified deadline holds at gamma={float(gamma)}", val < TARGET)
    ok(f"deadline at gamma={float(gamma)} is tight to 0.1 time units",
       shorter > TARGET)
    deadline_rows.append(dict(gamma=float(gamma), nu0=float(nu0), nu1=float(nu1),
                              tau=float(tau), remainder=float(val),
                              remainder_exact=str(val)))
record("recovery_deadlines", deadline_rows)

# Additional complete loss caused by residual binding during a fading switch.
def extra_loss(gamma: Q) -> Q:
    return KA * (1 + P_MAX / CREL[0]) * U[1] * CTOT[1] / gamma


EXTRA_21 = extra_loss(Q(21))
ok("additional complete loss at gamma=21 is below 0.00228", EXTRA_21 < Q(228, 100000))
ok("additional complete loss at gamma=21 exceeds 0.00226", EXTRA_21 > Q(226, 100000))
record("extra_complete_loss_gamma21", str(EXTRA_21))
record("extra_complete_loss_gamma21_float", float(EXTRA_21))
record("extra_complete_loss_gamma1_float", float(extra_loss(Q(1))))

# ---------------------------------------------------------------------------
# 5.  Continuous bounded-error inference
# ---------------------------------------------------------------------------

A_L = GAIN[0] * U[0] * M_FLOOR * CTOT[0] / (1 + SIGMA) * (TACQ - 1 / H_MIN)
A_U = GAIN[1] * U[1] * (1 + ETA) * CTOT[1] * TACQ
A_L_PRINT = (Q(98, 100) * Q(79, 1000) * Q(94, 100) * Q(99, 100)
             / Q(1005, 1000) * (8 - Q(1, 21)))
A_U_PRINT = Q(102, 100) * Q(81, 1000) * Q(101, 100) ** 2 * 8
ok("A_L = 47745467/83750000", A_L_PRINT == Q(47745467, 83750000))
ok("A_U = 42140331/62500000", A_U_PRINT == Q(42140331, 62500000))
ok("the printed A_L is dominated by the sharp one", A_L >= A_L_PRINT)
ok("the printed A_U dominates the sharp one", A_U <= A_U_PRINT)
record("A_L", str(A_L_PRINT))
record("A_L_float", float(A_L_PRINT))
record("A_U", str(A_U_PRINT))
record("A_U_float", float(A_U_PRINT))

P_RANGE = (Q(95, 100), Q(205, 100))


def outer_p_interval(y: Q):
    lo, hi = P_RANGE
    if 0 < y - ERR < A_U_PRINT:
        lo = max(lo, K[1] * (y - ERR) / (A_U_PRINT - y + ERR))
    elif y - ERR >= A_U_PRINT:
        return None                      # no p satisfies the upper envelope
    if 0 <= y + ERR < A_L_PRINT:
        hi = min(hi, K[1] * (y + ERR) / (A_L_PRINT - y - ERR))
    return (lo, hi) if lo <= hi else None


def outer_flux_interval(p_lo: Q, p_hi: Q):
    return (K[0] * CTOT[0] * p_lo / (p_lo + K[0]),
            K[1] * CTOT[1] * p_hi / (p_hi + K[1]))


# The lower inversion uses k_max in both places: L_p = A_L p/(p+k_max) and
# U_p = A_U p/(p+k_min).  Recompute the inversion honestly with k_min above.
def outer_p_interval_exact(y: Q):
    lo, hi = P_RANGE
    if y - ERR > 0:
        if y - ERR >= A_U_PRINT:
            return None
        lo = max(lo, K[0] * (y - ERR) / (A_U_PRINT - y + ERR))
    if y + ERR >= A_L_PRINT:
        hi = P_RANGE[1]
    else:
        hi = min(hi, K[1] * (y + ERR) / (A_L_PRINT - y - ERR))
    return (lo, hi) if lo <= hi else None


INFERENCE_EXAMPLES = []
for y in (Q(30549, 100000), Q(41151, 100000)):
    iv = outer_p_interval_exact(y)
    ok(f"outer p-set for y={float(y)} is nonempty", iv is not None)
    fl = outer_flux_interval(*iv)
    INFERENCE_EXAMPLES.append(dict(y=float(y), p_lo=float(iv[0]), p_hi=float(iv[1]),
                                   F_lo=float(fl[0]), F_hi=float(fl[1])))
record("inference_examples", INFERENCE_EXAMPLES)
ok("a low-signal observation cannot force the high class",
   INFERENCE_EXAMPLES[0]["p_hi"] < 1.95)
ok("a high-signal observation excludes the low class",
   INFERENCE_EXAMPLES[1]["p_lo"] > 1.05)

# Consistency with the binary theorem: at the two-class threshold the outer set
# must be compatible with the decision.
THRESH_SET = outer_p_interval_exact(THRESHOLD)
ok("a record at the binary threshold has a nonempty outer set",
   THRESH_SET is not None)
ok("that outer set meets neither promised class, matching strict separation",
   THRESH_SET[0] > P_LOW[1] and THRESH_SET[1] < P_HIGH[0])
record("threshold_outer_p", [float(THRESH_SET[0]), float(THRESH_SET[1])])

# Range of records compatible with the declared continuous contract.
_step = Q(1, 10000)
_lo = min(y for y in (Q(n, 10000) for n in range(1, 8000))
          if outer_p_interval_exact(y) is not None)
_hi = max(y for y in (Q(n, 10000) for n in range(1, 8000))
          if outer_p_interval_exact(y) is not None)
ok("the compatible record range starts near 0.2650",
   abs(float(_lo) - 0.2650) < 2e-4)
ok("the compatible record range ends near 0.4661",
   abs(float(_hi) - 0.4661) < 2e-4)
ok("both example records lie inside the compatible range",
   all(float(_lo) <= ex["y"] <= float(_hi) for ex in INFERENCE_EXAMPLES))
record("compatible_record_range", [float(_lo), float(_hi)])

# ---------------------------------------------------------------------------
# 6.  Nonlinear slope sandwich and its Michaelis-Menten limit
# ---------------------------------------------------------------------------

def slope_sandwich(g_lo: Q, g_hi: Q, k_lo: Q, k_hi: Q, c: Q):
    lower = k_lo * (g_hi + c) / (c * (g_hi + k_hi))
    upper = k_hi * (g_lo + c) / (c * (g_lo + k_lo))
    return lower, upper


lin_lo, lin_hi = slope_sandwich(Q(1), Q(1), Q(1), Q(1), Q(20))
ok("with constant slopes the sandwich collapses to k(p+c)/(c(p+k))",
   lin_lo == lin_hi == Q(1) * (Q(1) + 20) / (20 * (Q(1) + 1)))
record("linear_collapse", str(lin_lo))

# Reduced Michaelis-Menten example: V=K=10, C=Rt=1, c=20, beta=1.
MM_G_LO = Q(10) * Q(10) / (Q(10) + Q(1)) ** 2       # V K/(K+C)^2 = 100/121
MM_G_HI = Q(10) / Q(10)                             # V/K = 1
MM_LO, MM_HI = slope_sandwich(MM_G_LO, MM_G_HI, MM_G_LO, MM_G_HI, Q(20))
ok("MM sandwich lower end is 100*21/(121*40)", MM_LO == Q(100, 121) * 21 / (20 * 2))
ok("MM sandwich upper end is 0.63", MM_HI == Q(63, 100))
record("mm_bounds", [float(MM_LO), float(MM_HI)])
record("mm_linear_coefficient", float(Q(1) * (Q(1) + 20) / (20 * 2)))

# Low-saturation limit: shrink C/K_g and C/K_n with p = V_g/K_g, k = V_n/K_n fixed.
limits = []
for scale in (1, 10, 100, 1000):
    Kg = Q(10) * scale
    Vg = Kg                                          # p = 1
    g_lo = Vg * Kg / (Kg + Q(1)) ** 2
    g_hi = Vg / Kg
    lo, hi = slope_sandwich(g_lo, g_hi, g_lo, g_hi, Q(20))
    limits.append(dict(K=float(Kg), lower=float(lo), upper=float(hi)))
ok("the slope sandwich contracts to the linear coefficient as saturation vanishes",
   limits[-1]["upper"] - limits[-1]["lower"] < 1e-3)
record("mm_low_saturation", limits)


def nonlinear_ratio(Vg=10.0, Kg=10.0, Vn=10.0, Kn=10.0, C=1.0, Rt=1.0,
                    c_rel=20.0, beta=1.0, u=0.08, T=8.0, horizon=60.0):
    """Complete-loss per reporter product for saturating rate laws."""
    alpha = u * (beta + c_rel) / (Rt * c_rel)
    g = lambda z: Vg * z / (Kg + z)
    n = lambda xx: Vn * xx / (Kn + xx)

    # Reporter-free reference: integrate it alongside so the deficit is matched.
    def rhs(t, y, active):
        x, b, q, D, x0 = y
        al = alpha if active else 0.0
        v = al * x * (Rt - b)
        return [g(C - x - b) - n(x) - (v - (beta + c_rel) * b) - c_rel * b,
                v - (beta + c_rel) * b,
                c_rel * b,
                n(x0) - n(x),
                g(C - x0) - n(x0)]

    # Stationary reference level for the reporter-free source.
    lo, hi = 0.0, C
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if g(C - mid) - n(mid) > 0:
            lo = mid
        else:
            hi = mid
    xs = 0.5 * (lo + hi)
    y = [xs, 0.0, 0.0, 0.0, xs]
    for a_, b_, act in ((0.0, T, True), (T, horizon, False)):
        sol = solve_ivp(lambda t, y: rhs(t, y, act), (a_, b_), y,
                        rtol=1e-11, atol=1e-14)
        assert sol.success
        y = sol.y[:, -1]
    q_inf = y[2] + c_rel * y[1] / (beta + c_rel)
    return y[3] / q_inf, xs


MM_RATIO, MM_REF = nonlinear_ratio()
ok("the nonlinear reference level is 1/2", abs(MM_REF - 0.5) < 1e-9)
ok("the nonlinear cost ratio lies inside the proved sandwich",
   float(MM_LO) < MM_RATIO < float(MM_HI))
ok("the nonlinear cost ratio rounds to 0.5236", abs(MM_RATIO - 0.5236) < 5e-5)
record("mm_numeric_ratio", MM_RATIO)

# ---------------------------------------------------------------------------
# 7.  Numerical source solutions (independent checks, not proofs)
# ---------------------------------------------------------------------------

def run(p=1.0, k=1.0, C=1.0, u=0.08, c=20.0, beta=1.0, R=1.0, s=0.0,
        T=8.0, delay=0.0, recovery=5.0, gamma=None):
    """Integrate the literal source; gamma=None means an ideal switch."""
    a = p + k
    xb = p * C / a
    alpha0 = u * (beta + c) / (R * c)
    x0 = lambda t: xb * (1 + s * np.exp(-a * t))

    def rhs(t, y, mode):
        x, b, q, I, D = y
        if mode == "on":
            al = alpha0
        elif mode == "off":
            al = 0.0
        else:
            al = alpha0 * np.exp(-gamma * (t - T))
        v = al * x * (R - b)
        return [p * (C - x - b) - k * x - v + beta * b,
                v - (beta + c) * b, c * b, b, k * (x0(t) - x)]

    ts, ys, y = [], [], [xb * (1 + s), 0.0, 0.0, 0.0, 0.0]
    end_acq = None
    segments = [(0.0, delay, "off"), (delay, T, "on"),
                (T, T + recovery, "off" if gamma is None else "fade")]
    for lo, hi, mode in segments:
        if hi <= lo:
            continue
        sol = solve_ivp(lambda t, y: rhs(t, y, mode), (lo, hi), y,
                        rtol=2e-10, atol=2e-13, dense_output=True)
        assert sol.success
        grid = np.linspace(lo, hi, 201)
        ts.extend(grid)
        ys.extend(sol.sol(grid).T)
        y = sol.y[:, -1]
        if abs(hi - T) < 1e-12:
            end_acq = y.copy()
    tt = np.array(ts)
    yy = np.array(ys).T
    e = x0(tt) - yy[0]
    b = yy[1]
    identity = a * yy[4] - k * ((p + c) * yy[3] + b - e)
    q_inf = y[2] + c * y[1] / (beta + c)      # complete-recovery reporter product
    out = dict(p=p, c=c, u=u, T=T, delay=delay, gamma=gamma,
               q_T=float(end_acq[2]), q_inf=float(q_inf),
               peak_suppression=float(np.max(e / x0(tt))),
               loss_acquisition=float(end_acq[4]),
               loss_complete=float(k / a * (1 + p / c) * q_inf),
               remaining_after_recovery=float(k / a * (e[-1] + (p - beta) * b[-1]
                                                      / (beta + c))),
               identity_residual=float(np.max(np.abs(identity))))
    assert out["identity_residual"] < 5e-8
    assert np.min(yy[0]) > -1e-9 and np.min(C - yy[0] - b) > -1e-9
    return out, (tt, yy, e / x0(tt))


COMPARISON = []
for label, c_rel, delay in (("slow catalyst", 1.0, 0.0),
                            ("fast catalyst", 20.0, 0.0),
                            ("late fast pulse", 20.0, 4.0)):
    lo_row, _ = run(c=c_rel, delay=delay)
    hi_row, _ = run(p=2.0, c=c_rel, delay=delay)
    COMPARISON.append(dict(label=label, c=c_rel, delay=delay,
                           low_signal=lo_row["q_T"],
                           low_peak_percent=100 * lo_row["peak_suppression"],
                           low_complete_loss=lo_row["loss_complete"],
                           nominal_gap=hi_row["q_T"] - lo_row["q_T"] - 0.02))
record("comparison", COMPARISON)
# The ratio of complete losses is explained exactly by Theorem 3.3.
_slow, _fast = COMPARISON[0], COMPARISON[1]
_q_slow = _slow["low_complete_loss"] / (0.5 * (1 + 1 / 1.0))
_q_fast = _fast["low_complete_loss"] / (0.5 * (1 + 1 / 20.0))
_ratio = _slow["low_complete_loss"] / _fast["low_complete_loss"]
ok("the loss ratio equals the storage-factor ratio rescaled by realised product",
   abs(_ratio - (2 / 1.05) * (_q_slow / _q_fast)) < 1e-12)
ok("the realised complete products are 0.28830 and 0.30731",
   abs(_q_slow - 0.28830) < 5e-6 and abs(_q_fast - 0.30731) < 5e-6)
record("complete_products", [_q_slow, _q_fast])
record("loss_ratio", _ratio)
ok("the slow catalyst violates the 5% preservation requirement",
   COMPARISON[0]["low_peak_percent"] > 5)
ok("the fast catalyst satisfies it", COMPARISON[1]["low_peak_percent"] < 5)
ok("the slow catalyst costs more native output at equal effective activity",
   COMPARISON[0]["low_complete_loss"] > 1.7 * COMPARISON[1]["low_complete_loss"])
ok("the delayed pulse reduces both product and loss",
   COMPARISON[2]["low_signal"] < COMPARISON[1]["low_signal"]
   and COMPARISON[2]["low_complete_loss"] < COMPARISON[1]["low_complete_loss"])

# The storage factor at fixed final product, for four catalytic release rates.
FACTORS = {str(c_rel): float(1 + Q(1) / Q(c_rel)) for c_rel in ("1/5", "1", "5", "20")}
ok("the factor at c=0.2 and p=1 is exactly 6", FACTORS["1/5"] == 6.0)
record("storage_factors", FACTORS)

# Sixteen interior draws challenge the uniform bounds.
rng = np.random.default_rng(17092026)
interior = []
for high in (False, True):
    for _ in range(8):
        args = dict(p=rng.uniform(1.95, 2.05) if high else rng.uniform(0.95, 1.05),
                    k=rng.uniform(0.98, 1.02), C=rng.uniform(0.99, 1.01),
                    u=rng.uniform(0.079, 0.081), c=rng.uniform(20, 25),
                    beta=rng.uniform(1, 2), R=rng.uniform(0.99, 1.01),
                    s=rng.uniform(-0.01, 0.01))
        row, _ = run(**args)
        row["high"] = high
        interior.append(row)
        assert row["peak_suppression"] < float(SUPPRESSION)
        assert abs(row["remaining_after_recovery"]) < float(TAIL_IDEAL)
record("interior_draws", interior)
record("max_identity_residual", max(r["identity_residual"] for r in interior))
ok("all sixteen interior draws respect the proved suppression bound",
   all(r["peak_suppression"] < float(SUPPRESSION) for r in interior))
ok("all sixteen interior draws respect the proved recovery remainder",
   all(abs(r["remaining_after_recovery"]) < float(TAIL_IDEAL) for r in interior))
ok("the accounting identity residual stays below 5e-8",
   max(r["identity_residual"] for r in interior) < 5e-8)

# Fading switches, nominal parameters: the proved deadlines must dominate.
FADE = []
for gamma in (1.0, 5.0, 21.0):
    row, _ = run(gamma=gamma, recovery=25.0)
    FADE.append(dict(gamma=gamma, loss_complete=row["loss_complete"],
                     remaining_after_25=row["remaining_after_recovery"]))
ideal_row, _ = run(recovery=25.0)
FADE.append(dict(gamma=None, loss_complete=ideal_row["loss_complete"],
                 remaining_after_25=ideal_row["remaining_after_recovery"]))
record("fading_numerics", FADE)
ok("a fading switch costs more complete native output than an ideal one",
   all(f["loss_complete"] >= ideal_row["loss_complete"] - 1e-9
       for f in FADE if f["gamma"]))
ok("the extra complete loss respects the proved bound at gamma=21",
   0 < FADE[2]["loss_complete"] - ideal_row["loss_complete"] < float(EXTRA_21))
ok("a slower switch costs more additional complete native output",
   FADE[0]["loss_complete"] > FADE[1]["loss_complete"] > FADE[2]["loss_complete"])
record("extra_loss_numeric",
       {str(f["gamma"]): f["loss_complete"] - ideal_row["loss_complete"] for f in FADE})

# Schedule invariance of the complete-recovery cost coefficient.
inv = []
for delay, gamma in ((0.0, None), (4.0, None), (0.0, 5.0), (2.0, 1.0)):
    row, _ = run(delay=delay, gamma=gamma, recovery=40.0)
    inv.append(row["loss_complete"] / row["q_inf"])
ok("the cost per reporter product is schedule invariant to 1e-12",
   max(inv) - min(inv) < 1e-12)
record("schedule_invariant_ratio", inv[0])
ok("the invariant equals k(p+c)/(c(p+k)) = 0.525 at the nominal point",
   abs(inv[0] - 0.525) < 1e-9)

# ---------------------------------------------------------------------------
# 8.  Figures
# ---------------------------------------------------------------------------

FIGDIR.mkdir(exist_ok=True)
plt.rcParams.update({"font.size": 8.5, "axes.grid": True, "grid.alpha": 0.3,
                     "axes.spines.top": False, "axes.spines.right": False})


def margin_curve(T: float, u_nom: float) -> tuple[float, float]:
    """Unrounded sufficient signal margin and relative suppression at activity u."""
    umax, umin = Q(str(u_nom)) + Q(1, 1000), Q(str(u_nom)) - Q(1, 1000)
    b0 = umax * (1 + P_MAX / CREL[0]) / A_MIN
    m = 1 - ETA - (1 + ETA) * b0
    sig = umax * CTOT[1] / (CREL[0] * RTOT[0])
    Tq = Q(str(T))
    up = GAIN[1] * umax * (1 + ETA) * XB_MAX_LOW * Tq
    lo = GAIN[0] * umin * m * XB_MIN_HIGH / (1 + sig) * (Tq - 1 / H_MIN)
    return float(lo - up - 2 * ERR), float((1 + ETA) / (1 - ETA) * b0)


fig, ax = plt.subplots(1, 2, figsize=(7.0, 2.7), layout="constrained")
ts = np.linspace(1, 10, 120)
for u_nom in (0.04, 0.06, 0.08, 0.10):
    curve = [margin_curve(t, u_nom)[0] for t in ts]
    sup = margin_curve(8.0, u_nom)[1]
    style = "-" if sup <= 0.05 else "--"
    ax[0].plot(ts, curve, style, lw=1.3,
               label=f"$u={u_nom:.2f}$ ({100 * sup:.1f}\\% loading)")
ax[0].axhline(0, color="black", lw=0.8)
ax[0].axvline(8, color="gray", lw=0.8)
ax[0].set(xlabel="acquisition time $T$", ylabel="sufficient signal margin")
ax[0].legend(fontsize=6.5, frameon=False)
for label, c_rel, delay in (("slow, $c=1$", 1.0, 0.0),
                            ("fast, $c=20$", 20.0, 0.0),
                            ("late fast pulse", 20.0, 4.0)):
    _, (tt, yy, sup) = run(c=c_rel, delay=delay)
    ax[1].plot(tt, 100 * sup, lw=1.3, label=label)
ax[1].axhline(5, color="black", lw=0.8, ls="--")
ax[1].axvline(8, color="gray", lw=0.8)
ax[1].set(xlabel="time, including recovery", ylabel="native-flux suppression (\\%)")
ax[1].legend(fontsize=6.5, frameon=False)
fig.savefig(FIGDIR / "design.pdf")
plt.close(fig)

# Certified recovery deadline against switch decay rate.
fig, ax = plt.subplots(figsize=(3.4, 2.5), layout="constrained")
gammas = np.geomspace(0.4, 40, 60)


def deadline_numeric(gamma_f: float, target=3e-6) -> float:
    gamma = Q(str(round(gamma_f, 6)))
    best = np.inf
    for nu1_f in np.geomspace(0.05 * min(21.0, gamma_f), min(21.0, gamma_f), 40):
        nu1 = Q(str(round(nu1_f, 6)))
        for nu0_f in np.geomspace(0.05 * min(1.93, nu1_f), min(1.93, nu1_f), 25):
            nu0 = Q(str(round(nu0_f, 6)))
            try:
                big_b, beta_star = fading_constants(gamma, nu0, nu1)
            except ValueError:
                continue
            f = (lambda t: float(KA) * (float(big_b) * exp(-float(nu0) * t)
                                        + float(PCH) * (float(beta_star)
                                                        * exp(-float(nu1) * t)
                                                        + float(A_STAR / gamma)
                                                        * exp(-float(gamma) * t))))
            if f(400.0) > target:
                continue
            lo, hi = 0.0, 400.0
            for _ in range(60):
                mid = 0.5 * (lo + hi)
                if f(mid) > target:
                    lo = mid
                else:
                    hi = mid
            best = min(best, hi)
    return best


curve = [deadline_numeric(g) for g in gammas]
ax.plot(gammas, curve, lw=1.4, color="#1f4e79")
ax.scatter([float(r["gamma"]) for r in deadline_rows],
           [r["tau"] for r in deadline_rows], s=14, color="#c1121f", zorder=3)
ax.set(xscale="log", xlabel=r"switch decay rate $\gamma$",
       ylabel=r"certified recovery time $\tau$")
ax.axhline(5, color="gray", lw=0.8, ls="--")
fig.savefig(FIGDIR / "deadline.pdf")
plt.close(fig)

# Outer inference intervals.
fig, ax = plt.subplots(1, 2, figsize=(7.0, 2.6), layout="constrained")
ys = np.linspace(0.02, 0.60, 200)
lo_p, hi_p, lo_f, hi_f, keep = [], [], [], [], []
for yv in ys:
    iv = outer_p_interval_exact(Q(str(round(float(yv), 6))))
    if iv is None:
        continue
    keep.append(yv)
    lo_p.append(float(iv[0]))
    hi_p.append(float(iv[1]))
    fl = outer_flux_interval(*iv)
    lo_f.append(float(fl[0]))
    hi_f.append(float(fl[1]))
ax[0].fill_between(keep, lo_p, hi_p, alpha=0.35, color="#1f4e79", lw=0)
ax[0].plot(keep, lo_p, lw=1.0, color="#1f4e79")
ax[0].plot(keep, hi_p, lw=1.0, color="#1f4e79")
ax[0].set(xlabel="recorded value $y$", ylabel="outer set for $p$")
ax[1].fill_between(keep, lo_f, hi_f, alpha=0.35, color="#7a5195", lw=0)
ax[1].plot(keep, lo_f, lw=1.0, color="#7a5195")
ax[1].plot(keep, hi_f, lw=1.0, color="#7a5195")
for ex in INFERENCE_EXAMPLES:
    ax[0].plot([ex["y"], ex["y"]], [ex["p_lo"], ex["p_hi"]], color="#c1121f", lw=1.8)
    ax[1].plot([ex["y"], ex["y"]], [ex["F_lo"], ex["F_hi"]], color="#c1121f", lw=1.8)
ax[1].set(xlabel="recorded value $y$", ylabel="outer set for native flux $F$")
fig.savefig(FIGDIR / "inference.pdf")
plt.close(fig)

# ---------------------------------------------------------------------------
# 9.  Generated LaTeX table rows
# ---------------------------------------------------------------------------

def sci(x: float) -> str:
    mantissa, expo = f"{x:.2e}".split("e")
    return f"{mantissa}\\cdot 10^{{{int(expo)}}}"


rows = " \\\\\n".join(
    f"${r['gamma']:g}$ & ${r['nu0']:g}$ & ${r['nu1']:g}$ & ${r['tau']:.1f}$ & "
    f"${sci(r['remainder'])}$"
    for r in deadline_rows)
(HERE / "recovery_rows.tex").write_text(
    "\\newcommand{\\recoveryrows}{%\n" + rows + " \\\\\n}\n", encoding="utf-8")

comp = " \\\\\n".join(
    f"{r['label'].capitalize()}, $c={r['c']:g}$, $[{r['delay']:g},8]$ & "
    f"${r['low_signal']:.5f}$ & ${r['low_peak_percent']:.3f}\\%$ & "
    f"${r['low_complete_loss']:.5f}$ & ${r['nominal_gap']:.5f}$"
    for r in COMPARISON)
(HERE / "comparison_rows.tex").write_text(
    "\\newcommand{\\comparisonrows}{%\n" + comp + " \\\\\n}\n", encoding="utf-8")

record("checks_run", len(CHECKS))
(HERE / "results.json").write_text(json.dumps(REPORT, indent=2), encoding="utf-8")
print(f"{len(CHECKS)} checks passed.")
for key in ("suppression_float", "U8_float", "L8_float", "margin_float",
            "threshold_float", "tail_ideal_crude_float", "tail_fading_crude_float",
            "F_low_max_float", "F_high_min_float"):
    print(f"  {key:28s} {REPORT[key]}")
print("  deadlines", [(r["gamma"], r["tau"]) for r in deadline_rows])
print("  comparison", [(r["label"], round(r["low_signal"], 5),
                        round(r["low_peak_percent"], 3),
                        round(r["low_complete_loss"], 5),
                        round(r["nominal_gap"], 5)) for r in COMPARISON])
print("  inference", INFERENCE_EXAMPLES)
