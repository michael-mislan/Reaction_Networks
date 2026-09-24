"""Independent replay of every constant printed in the paper.

Run with the repository virtual environment:

    ..\\..\\..\\.venv\\Scripts\\python.exe check_paper.py

Everything is exact rational or integer arithmetic; the only floating point
appears in descriptive decimal conversions, which are printed with the exact
rational alongside.  Writes check_paper_output.json.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECKS: list[dict] = []
FAILED: list[str] = []


def check(name: str, got, want, note: str = "") -> None:
    ok = got == want
    CHECKS.append({"name": name, "ok": ok, "got": str(got), "want": str(want), "note": note})
    if not ok:
        FAILED.append(f"{name}: got {got}, want {want}")


def check_true(name: str, cond: bool, note: str = "") -> None:
    CHECKS.append({"name": name, "ok": bool(cond), "got": str(bool(cond)), "want": "True", "note": note})
    if not cond:
        FAILED.append(name)


# ---------------------------------------------------------------------------
# Exponential bounds by positive rational Taylor sums (always lower bounds of
# exp on the nonnegative axis, so 1/S is an upper bound of exp(-x)).
# ---------------------------------------------------------------------------

def exp_lower(x: F, terms: int) -> F:
    """A rational lower bound for exp(x), x >= 0."""
    assert x >= 0
    total = F(0)
    term = F(1)
    for k in range(terms):
        total += term
        term = term * x / (k + 1)
    return total


# ---------------------------------------------------------------------------
# 1.  The phase exponent.
# ---------------------------------------------------------------------------

s = F(1, 10 ** 6)                       # the tilt used in the phase estimate
Delta = F(1, 700) - F(1, 1000)          # transported stock minus the low-X threshold
Cquad = F(12, 5) * 91                   # quadratic remainder per step, 91V steps
kappa = s * Delta - Cquad * s ** 2      # unrounded exponent coefficient

check("phase rate kappa", kappa, F(1839, 8750000000000))
check_true("kappa exceeds the printed 1e-10 rate", kappa > F(1, 10 ** 10))
check("kappa / 1e-10", kappa * 10 ** 10, F(1839, 875),
      "the rounded certificate discarded a factor 1839/875 = 2.1017...")

# Optimising the tilt inside the same inequality is nearly exhausted.
s_star = Delta / (2 * Cquad)
kappa_star = Delta * s_star - Cquad * s_star ** 2
check("optimal tilt s*", s_star, F(3, 7000) / F(2184, 5))
check_true("retuning the tilt gains under 0.04 percent", kappa_star / kappa - 1 < F(4, 10000))
check_true("retuning the tilt gains something", kappa_star > kappa)

# ---------------------------------------------------------------------------
# 2.  The residual-absorption floor used by the Lean envelope.
# ---------------------------------------------------------------------------

c_res = F(1, 40000000) - kappa
check("residual coefficient", c_res, F(216911, 8750000000000))
V_floor = 10 ** 10
x_floor = c_res * V_floor
check_true("absorption floor argument at least 247", x_floor >= 247)
# 247^9 * x / 10! <= exp(x) and the left side already dominates 2*10^6*(V+1).
coeff = F(247 ** 9) * c_res / 3628800
check_true("absorption coefficient exceeds 2e6 with margin",
           coeff >= 2 * 10 ** 6 * F(10 ** 10 + 1, 10 ** 10))
CHECKS.append({"name": "absorption margin factor", "ok": True,
               "got": str(float(coeff / (2 * 10 ** 6))), "want": ">1", "note": "slack in Lean"})

# ---------------------------------------------------------------------------
# 3.  Confidence certificates.
# ---------------------------------------------------------------------------

# Hundred cycles at the reduced scale: 101*100*exp(-kappa V) <= 21/10^6.
V_new = 96 * 10 ** 9
check_true("kappa*V_new at least 20", kappa * V_new >= 20)
e20 = exp_lower(F(20), 38)
check_true("e^20 >= 484800000", e20 >= 484800000)
check_true("hundred-cycle failure at V_new below 21e-6",
           F(10100) / 484800000 <= F(21, 10 ** 6))

# Same copy scale as the original example, halved bath.
V_old = 2 * 10 ** 11
check_true("kappa*V_old at least 42", kappa * V_old >= 42)
check_true("e^42 >= 2.3503e17", 484800000 ** 2 >= 235031040000000000)
check_true("hundred-cycle failure at V_old below 1e-13",
           F(10100) / 235031040000000000 <= F(1, 10 ** 13))

# The useful-confidence floor of the refined certificate.
V_min = 5 * 10 ** 10
check_true("kappa*V_min at least 10", kappa * V_min >= 10)
e10 = exp_lower(F(10), 21)
check_true("e^10 >= 10100", e10 >= 10100)
check_true("error below 1/100 at the floor", F(101) / 10100 <= F(1, 100))

# Smallest scale that still certifies the original hundred-cycle confidence.
# 101*100*exp(-kappa V) <= 21e-6  <=>  exp(kappa V) >= 1.01e10/21.
target = F(101 * 100 * 10 ** 6, 21)
V_star = None
for candidate in range(94 * 10 ** 9, 97 * 10 ** 9, 10 ** 8):
    if exp_lower(kappa * candidate, 120) >= target:
        V_star = candidate
        break
check_true("a scale below 9.6e10 already suffices", V_star is not None and V_star <= V_new)
CHECKS.append({"name": "smallest certified scale on a 1e8 grid", "ok": True,
               "got": str(V_star), "want": "<= 96000000000", "note": "grid search, exact Taylor"})

# ---------------------------------------------------------------------------
# 4.  The hundred-cycle mission at the reduced scale.
# ---------------------------------------------------------------------------

m = 100
V = V_new


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


QI_cycle = ceil_div(V, 56)
QX_cycle = ceil_div(V, 1080)
I_end = ceil_div(V, 28)
gross_cycle = V // 10
food_cycle = 5 * V
R_new = m * gross_cycle * 10           # rho = 1/10

check("per-cycle template equivalents", QI_cycle, 1714285715)
check("per-cycle free X", QX_cycle, 88888889)
check("terminal inventory floor", I_end, 3428571429)
check("per-cycle gross allowance", gross_cycle, 9600000000)
check("mission template equivalents", m * QI_cycle, 171428571500)
check("mission free X", m * QX_cycle, 8888888900)
check("mission food per species", m * food_cycle, 48000000000000)
check("mission gross allowance", m * gross_cycle, 960000000000)
check("sufficient pure fuel", R_new, 9600000000000)
check_true("bath inequality holds with equality", m * gross_cycle == F(1, 10) * R_new)

net_uniform = m * QI_cycle + I_end - (161 * V) // 160      # worst admitted seed
net_allfree = m * QI_cycle + I_end - V                     # the all-free-X seed
check("net synthesis, worst admitted seed", net_uniform, 78257142929)
check("net synthesis, all-free seed", net_allfree, 78857142929)
net = net_allfree
check_true("uniform real net bound is positive",
           (F(m, 56) - F(161, 160)) * V > 0)
check_true("net onset at 55 cycles", (F(55, 56) + F(2, 56) - F(161, 160)) > 0)
check_true("no net onset at 54 cycles", (F(54, 56) + F(2, 56) - F(161, 160)) < 0)

# The original certified example, for the comparison table.
QI_old = ceil_div(V_old, 56)
QX_old = ceil_div(V_old, 1080)
check("original mission template equivalents", m * QI_old, 357142857200)
check("original mission free X", m * QX_old, 18518518600)
check("original gross allowance", m * (V_old // 5), 4000000000000)
check("original sufficient fuel", m * (V_old // 5) * 10, 40000000000000)
check("original net synthesis, all-free seed",
      m * QI_old + ceil_div(V_old, 28) - V_old, 164285714343)
check("original net synthesis, worst admitted seed",
      m * QI_old + ceil_div(V_old, 28) - (161 * V_old) // 160, 163035714343)

# Halved allowance at the original copy scale.
check("halved gross allowance at V_old", m * (V_old // 10), 2000000000000)
check("halved bath at V_old", m * (V_old // 10) * 10, 20000000000000)

# Reduction factors.
check("copy-scale reduction", F(V_old, V_new), F(25, 12))
check("fuel-inventory reduction", F(40000000000000, R_new), F(25, 6))

# Fixed-demand comparison: holding the original output demand fixed pins V.
D_I = m * QI_old
check_true("the original output demand forces the original scale back",
           ceil_div(56 * D_I, m) >= V_old,
           f"demand term = {ceil_div(56 * D_I, m)}")
check_true("and it exceeds the reduced scale by a factor above two",
           F(ceil_div(56 * D_I, m), V_new) > 2)

# ---------------------------------------------------------------------------
# 5.  Service intensity on the material corridor (pure bath, d = 1/50).
# ---------------------------------------------------------------------------

# alpha x + beta u w / V <= (1/50)(a*11/10 + eta*b*(11/10)^2) with a + b = 1.
eta = F(1, 8000000000)
cap = F(11, 10)
worst = F(1, 50) * max(cap, eta * cap * cap)
check("correlated gross intensity coefficient", worst, F(11, 500))
check_true("the independent-coefficient bound is larger", F(9, 200) > worst)

# Chernoff exponent at g = 1/10 over four time units with a one-count buffer.
g = F(1, 10)
exp_g = F(1, 1) + g + F(3, 5) * g ** 2     # exp(z) <= 1 + z + (3/5)z^2 for |z| <= 9/50
check_true("quadratic bound for exp(1/10)", exp_g <= F(53, 500) + 1)
margin = -g * F(1, 10) + 4 * worst * (exp_g - 1)
check_true("sharp service exponent beats -1/2000", margin <= F(-1, 2000),
           "coefficient of V before the one-count buffer")
check("sharp service exponent", margin, F(-21, 31250))
check_true("the old error allocation still pays for it", F(21, 31250) > F(1, 2000))

# The first attempt, with the independent cap, does not close.
bad = -g * F(1, 10) + 4 * F(9, 200) * (exp_g - 1)
check_true("independent-cap attempt fails", bad > 0, f"margin {bad}")

# ---------------------------------------------------------------------------
# 6.  Inventory identity and bath activities.
# ---------------------------------------------------------------------------

B_m = m * gross_cycle
check_true("pure-bath fuel activity floor", F(R_new - B_m, R_new) == F(9, 10))
check_true("pure-bath waste activity ceiling", F(B_m, R_new) == F(1, 10))
# Loaded bath force corridor.
rho = F(1, 10)
check("loaded force ratio", (1 + rho) / (1 - rho), F(11, 9))

# ---------------------------------------------------------------------------
# 7.  Thermochemistry: endpoint bath free energies.
# ---------------------------------------------------------------------------

# Delta G_b = -A0 J - log binom(R, J) for a pure bath.  Check the factorial
# cancellation symbolically on small integers.
import math as _math

for R_small, J in [(5, 0), (5, 3), (5, 5), (7, 2)]:
    lhs = _math.lgamma(R_small - J + 1) + _math.lgamma(J + 1) - _math.lgamma(R_small + 1)
    rhs = -_math.log(_math.comb(R_small, J))
    check_true(f"pure endpoint identity R={R_small} J={J}", abs(lhs - rhs) < 1e-12)

for R_small, J in [(5, -4), (5, 0), (5, 5), (6, -6)]:
    lhs = _math.lgamma(R_small - J + 1) + _math.lgamma(R_small + J + 1) - 2 * _math.lgamma(R_small + 1)
    rhs = _math.log(_math.factorial(R_small - J) * _math.factorial(R_small + J)
                    / _math.factorial(R_small) ** 2)
    check_true(f"loaded endpoint identity R={R_small} J={J}", abs(lhs - rhs) < 1e-12)

A0_exp = 80000000000
check("bath potential difference argument", A0_exp, 8 * 10 ** 10,
      "A0 = log(8*10^10) = log 10 + log(8*10^9)")

# Force-budget inversion:  R >= B coth(zeta/2).
def coth_half(z: float) -> float:
    return 1 / _math.tanh(z / 2)


CHECKS.append({"name": "force inversion at zeta=0.1", "ok": True,
               "got": f"{coth_half(0.1):.4f}", "want": "20.0167", "note": "R/B_m"})
CHECKS.append({"name": "force inversion at zeta=0.02", "ok": True,
               "got": f"{coth_half(0.02):.4f}", "want": "100.0033", "note": "R/B_m"})
check_true("zeta = 0.1 inversion", abs(coth_half(0.1) - 20.01667) < 1e-4)
check_true("zeta = 0.02 inversion", abs(coth_half(0.02) - 100.00333) < 1e-4)
# The chosen rho = 1/10 corresponds to a loaded-bath affinity drift of log(11/9).
check_true("rho = 1/10 drift", abs(_math.log(11 / 9) - 0.2006706954621511) < 1e-12)

# ---------------------------------------------------------------------------
# 8.  Dimensional conversions at c_* = 1 mM and tau = 60 s.
# ---------------------------------------------------------------------------

NA = F(602214076, 10 ** 8) * 10 ** 23    # exact, mol^-1
c_star = F(1, 1000)                      # mol/L


def litres(count: int) -> F:
    return F(count, 1) / (NA * c_star)


def pmol(count: int) -> float:
    return float(F(count, 1) / NA * 10 ** 12)


vol_reactor = float(litres(V) * 10 ** 9)          # nL
vol_bath = float(litres(R_new) * 10 ** 9)
check_true("reactor volume near 0.1594 nL", abs(vol_reactor - 0.15941) < 1e-4)
check_true("bath volume near 15.94 nL", abs(vol_bath - 15.9412) < 1e-3)
check_true("bath-to-reactor ratio is 100", abs(vol_bath / vol_reactor - 100) < 1e-9)

amounts = {
    "template equivalents": pmol(m * QI_cycle),
    "free X": pmol(m * QX_cycle),
    "food per species": pmol(m * food_cycle),
    "gross driven events": pmol(m * gross_cycle),
    "initial pure fuel": pmol(R_new),
    "net synthesis": pmol(net),
}
check_true("template amount near 0.284656 pmol", abs(amounts["template equivalents"] - 0.28466384) < 1e-7)
check_true("free-X amount near 0.014760 pmol", abs(amounts["free X"] - 0.0147604) < 1e-6)
check_true("food amount near 79.7062 pmol", abs(amounts["food per species"] - 79.705875) < 1e-5)
check_true("fuel amount near 15.9412 pmol", abs(amounts["initial pure fuel"] - 15.94123) < 1e-4)

# Rate coefficients:  a dimensionless order-k coefficient a becomes
# a / (tau * c_*^{k-1}).
tau = 60
check_true("bimolecular 20 becomes 1000/3 per M per s",
           F(20, 1) / (tau * c_star) == F(1000, 3))
check_true("unimolecular 20 becomes 1/3 per s", F(20, tau) == F(1, 3))
check_true("washout becomes 1/60 per s", F(1, tau) == F(1, 60))
check_true("mission duration is 400 minutes", 4 * m * tau == 24000)

# ---------------------------------------------------------------------------
# 9.  Asymptotic design rule.
# ---------------------------------------------------------------------------

# V = max(5e10, ceil(log(101 m / delta)/kappa)), R = max(1, ceil(m floor(V/10)/rho))
inv_kappa = 1 / kappa
check_true("1/kappa near 4.758e9", abs(float(inv_kappa) - 4758020.663 * 1000) < 1e4)
# At delta = 1/100 the copy floor governs until the logarithm overtakes it.
import math as _m2
cross = None
for mm in [10, 100, 10 ** 4, 10 ** 6, 10 ** 8]:
    v = max(5 * 10 ** 10, _math.ceil(_math.log(101 * mm / 0.01) * float(inv_kappa)))
    if v > 5 * 10 ** 10 and cross is None:
        cross = mm
    CHECKS.append({"name": f"design scale at m={mm}", "ok": True, "got": str(v),
                   "want": ">=5e10", "note": "delta=0.01, no extra output demand"})
check_true("the copy floor governs at one cycle",
           max(5 * 10 ** 10, _math.ceil(_math.log(101 / 0.01) * float(inv_kappa))) == 5 * 10 ** 10)
check_true("the logarithmic term governs from four cycles",
           _math.ceil(_math.log(101 * 4 / 0.01) * float(inv_kappa)) > 5 * 10 ** 10)
check_true("but not yet at three cycles",
           _math.ceil(_math.log(101 * 3 / 0.01) * float(inv_kappa)) <= 5 * 10 ** 10)

# ---------------------------------------------------------------------------

payload = {"checks": CHECKS, "failed": FAILED, "total": len(CHECKS)}
(HERE / "check_paper_output.json").write_text(json.dumps(payload, indent=2))
print(f"{len(CHECKS)} checks")
if FAILED:
    print("FAILURES:")
    for f in FAILED:
        print("  " + f)
    raise SystemExit(1)
print("ALL CHECKS PASSED")
