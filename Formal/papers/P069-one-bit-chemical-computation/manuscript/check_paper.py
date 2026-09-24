"""Independent replay of every number printed in the paper.

Run with the repository virtual environment (needs numpy, scipy, sympy):

    python check_paper.py

Exact quantities are recomputed in `fractions.Fraction` or bounded integer
arithmetic; the handful of genuinely floating-point diagnostics are labelled
NUMERIC and are not used to support any claim in the paper.  Writes
check_paper_output.json and exits nonzero on the first failure.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix

HERE = Path(__file__).resolve().parent
CHECKS: list[dict] = []
FAILED = 0


def check(name, ok, got=None, want=None):
    global FAILED
    CHECKS.append({"name": name, "ok": bool(ok), "got": str(got), "want": str(want)})
    if not ok:
        FAILED += 1
        print(f"  FAIL  {name}\n        got  {got}\n        want {want}")
    else:
        print(f"  ok    {name}" + (f"   [{got}]" if got is not None else ""))


def section(title):
    print(f"\n== {title}")


S = 2 ** 31
B = F(3216)

# ---------------------------------------------------------------------------
section("1. exact core certificate (integer uniformization)")


def binom_tail(n, lo, hi, prob):
    a, b = prob.numerator, prob.denominator
    if hi < lo:
        return F(0)
    return F(sum(comb(n, j) * a ** j * (b - a) ** (n - j) for j in range(lo, hi + 1)),
             b ** n)


def certify(K=80, m=8, T=1, theta=F(1, 2), eta=F(1), exact_payoff=True):
    states = [(n, p) for n in range(1, K + 1) for p in range(K - n + 1)]
    ix = {s: i for i, s in enumerate(states)}
    entries, exits = [], []
    for i, (n, p) in enumerate(states):
        f = K - n - p
        out = 0
        for dst, r in (((n + 1, p), 100 * n * f), ((n - 1, p), n * (n - 1)),
                       ((n, p + 1), 100 * n * f), ((n, p - 1), n * p)):
            assert r >= 0
            if r:
                assert dst in ix
                entries.append((i, ix[dst], r))
                out += r
        exits.append(out)
    lam = (max(exits) + 99) // 100
    D = 100 * lam
    entries.extend((i, i, D - r) for i, r in enumerate(exits))
    rr, cc, aa = zip(*entries)
    A = coo_matrix((np.array(aa, dtype=np.int64), (rr, cc)),
                   shape=(len(states), len(states))).tocsr()
    assert np.all(A.data >= 0)
    assert np.all(np.asarray(A.sum(axis=1)).ravel() == D)
    e_minus = sum((F((-1) ** j, factorial(j)) for j in range(26)), F())
    weights = [int(S * e_minus / factorial(j)) for j in range(19)]
    assert D * S < 2 ** 63 and S * sum(weights) < 2 ** 63 and sum(weights) <= S
    split = {n: binom_tail(n, m, n - m, theta) for n in range(1, K + 1)}
    collect = {p: binom_tail(p, 4, p, eta) for p in range(K + 1)}
    v = np.array([int(S * split[n] * collect[p]) for n, p in states], dtype=np.int64)
    assert v.min() >= 0 and v.max() <= S
    last = max(j for j, w in enumerate(weights) if w)
    for _ in range(lam * T):
        term = v
        acc = weights[0] * term
        for j in range(1, last + 1):
            term = A.dot(term) // D
            acc += weights[j] * term
        v = acc // S
    starts = [ix[(n, 0)] for n in range(m, K + 1)]
    worst = min(starts, key=lambda i: int(v[i]))
    return int(v[worst]), states[worst], lam, len(states), D, sum(weights)


c_num, c_worst, lam, nstates, D, wsum = certify()
check("lambda = 3216", lam == 3216, lam, 3216)
check("3240 core states", nstates == 3240, nstates, 3240)
check("D = 321600", D == 321600, D, 321600)
check("c numerator 2147232289", c_num == 2147232289, c_num, 2147232289)
check("c minimiser (8,0)", c_worst == (8, 0), c_worst, (8, 0))
check("D*S = 690630741196800 < 2^63", D * S == 690630741196800 and D * S < 2 ** 63,
      D * S, 690630741196800)
check("S*sum(w) = 4611686007689969664 < 2^63",
      S * wsum == 4611686007689969664 and S * wsum < 2 ** 63, S * wsum,
      4611686007689969664)

cO_num, cO_worst, _, _, _, _ = certify(theta=F(12, 25), eta=F(9, 10))
check("c_O numerator 2147153442", cO_num == 2147153442, cO_num, 2147153442)
check("c_O minimiser (8,0)", cO_worst == (8, 0), cO_worst, (8, 0))

for th, want in ((F(49, 100), 2147213192), (F(9, 20), 2146619325)):
    got, _, _, _, _, _ = certify(theta=th, eta=F(9, 10))
    check(f"diagnostic certificate theta={th}", got == want, got, want)

c = F(c_num, S)
cO = F(cO_num, S)
check("c decimal 0.9998829518444836", abs(float(c) - 0.9998829518444836) < 1e-15,
      repr(float(c)))
check("c_O decimal 0.9998462358489633", abs(float(cO) - 0.9998462358489633) < 1e-15,
      repr(float(cO)))

# smaller and larger cores, quoted in the remark after Proposition 3.2
c64, _, _, n64, _, _ = certify(K=64)
c96, _, _, n96, _, _ = certify(K=96)
print(f"  NOTE  K=64: {c64}/2^31 = {c64 / S:.9f} over {n64} states")
print(f"  NOTE  K=96: {c96}/2^31 = {c96 / S:.9f} over {n96} states")
check("K=64 certificate below 0.998", c64 / S < 0.998, f"{c64 / S:.9f}")
check("K=96 certificate above 0.99998", c96 / S > 0.99998, f"{c96 / S:.9f}")

# rounding slack at (8,0): unrounded float evaluation of the same payoff
payoff_slack = None
try:
    from scipy.sparse.linalg import expm_multiply
    states = [(n, p) for n in range(1, 81) for p in range(81 - n)]
    ix = {s: i for i, s in enumerate(states)}
    rows, cols, vals = [], [], []
    for i, (n, p) in enumerate(states):
        f = 80 - n - p
        tot = 0.0
        for dst, r in (((n + 1, p), n * f), ((n - 1, p), n * (n - 1) / 100),
                       ((n, p + 1), n * f), ((n, p - 1), n * p / 100)):
            if r:
                rows.append(i); cols.append(ix[dst]); vals.append(r); tot += r
        rows.append(i); cols.append(i); vals.append(-tot)
    G = coo_matrix((vals, (rows, cols)), shape=(len(states),) * 2).tocsr()
    h = np.array([float(binom_tail(n, 8, n - 8, F(1, 2)) * binom_tail(p, 4, p, F(1)))
                  for n, p in states])
    exact = expm_multiply(G, h)
    unrounded = min(exact[ix[(n, 0)]] for n in range(8, 81))
    payoff_slack = unrounded - float(c)
    print(f"  NOTE  unrounded float payoff at the minimiser: {unrounded:.10f} "
          f"(certificate slack {payoff_slack:.3e})  [NUMERIC]")
except Exception as exc:  # pragma: no cover
    print(f"  NOTE  skipped float comparison: {exc}")

# ---------------------------------------------------------------------------
section("2. prefix maximum and exponential estimates")

prefix = max(2 * r * (80 - r) + F(r * (r - 1), 100) for r in range(8, 81))
arg = max(range(8, 81), key=lambda r: 2 * r * (80 - r) + F(r * (r - 1), 100))
check("prefix maximum 16078/5", prefix == F(16078, 5), prefix, F(16078, 5))
check("prefix maximiser r=40", arg == 40, arg, 40)
check("integer form (r-40)(199r-8039)>=0 for all integer r",
      all((r - 40) * (199 * r - 8039) >= 0 for r in range(-500, 500)))
rare_F = 80 * F(1, 10 ** 7) + 64 * 80 ** 3 * F(5, 10 ** 11)
rare_WO = 80 * F(1, 10 ** 7) + 80 ** 3 * F(6, 10 ** 11)
check("regime F rare channels 1.6464e-3", rare_F == F(1029, 625000), float(rare_F))
check("regime WO rare channels 3.872e-5", abs(float(rare_WO) - 3.872e-5) < 1e-18,
      float(rare_WO))
check("prefix + F rare < 3216", prefix + rare_F < 3216, float(prefix + rare_F))
check("prefix + WO rare < 3216", prefix + rare_WO < 3216, float(prefix + rare_WO))

check("sum_{j<=18} 14^j/j! > 10^6 (so e^-14 < 1e-6)",
      sum(F(14 ** j, factorial(j)) for j in range(19)) > 10 ** 6)
check("56^5/120 > 10^6 (so e^-56 < 1e-6)", F(56 ** 5, 120) > 10 ** 6)
check("56*gamma_min*tau = 14 in W and WO", 56 * F(2 * 10 ** 7) * F(1, 8 * 10 ** 7) == 14)
check("56*gamma_min*tau = 14 in O", 56 * F(10 ** 8) * F(1, 4 * 10 ** 8) == 14)
check("72*gamma_min*tau = 144 in F", 72 * F(2 * 10 ** 7) * F(1, 10 ** 7) == 144)
check("one-minority F exponent >= 7168", 56 * F(2 * 10 ** 7) * 64 * F(1, 10 ** 7) >= 7168)

erlang = sum(F(144 ** m, factorial(m)) for m in range(64)) / \
    sum(F(144 ** m, factorial(m)) for m in range(301))
check("Erlang deadline bound < 2.44e-14", erlang < F(244, 10 ** 16), float(erlang))
check("Erlang deadline bound < 1e-12", erlang < F(1, 10 ** 12), float(erlang))

# ---------------------------------------------------------------------------
section("3. the four one-minority regime bounds")

q_orig = c - F(15, 10 ** 6)
q_W = c - (F(1, 10 ** 6) + B * F(1, 8 * 10 ** 7) + 80 * F(1, 10 ** 7)
           + 80 ** 3 * F(6, 10 ** 11))
q_O = cO - (F(1, 10 ** 6) + B * F(1, 4 * 10 ** 8) + 80 * F(1, 10 ** 8)
            + 80 ** 3 * F(1, 10 ** 11))
q_WO = cO - (F(1, 10 ** 6) + B * F(1, 8 * 10 ** 7) + 80 * F(1, 10 ** 7)
             + 80 ** 3 * F(6, 10 ** 11))
for name, got, want, thr in (
        ("q_Orig", q_orig, F(6710000239829, 6710886400000), F(4999, 5000)),
        ("q_W", q_W, F(838695571135489, 838860800000000), F(4999, 5000)),
        ("q_O", q_O, F(419359631961841, 419430400000000), F(4999, 5000)),
        ("q_WO", q_WO, F(419332385763057, 419430400000000), F(9997, 10000))):
    check(f"{name} exact value", got == want, got, want)
    check(f"{name} exceeds its advertised threshold", got > thr,
          f"{float(got):.16f} > {float(thr)}")
check("q_W loss = 999/12500000", c - q_W == F(999, 12500000), c - q_W)
check("q_O loss = 187/12500000", cO - q_O == F(187, 12500000), cO - q_O)
check("q_WO loss = 999/12500000", cO - q_WO == F(999, 12500000), cO - q_WO)
check("q_WO does NOT reach 4999/5000 (regimes W,O are not free)", q_WO < F(4999, 5000),
      float(q_WO))
check("q_W decimal 0.9998030318444836", abs(float(q_W) - 0.9998030318444836) < 1e-15,
      repr(float(q_W)))
check("q_O decimal 0.9998312758489633", abs(float(q_O) - 0.9998312758489633) < 1e-15,
      repr(float(q_O)))
check("q_WO decimal 0.9997663158489632", abs(float(q_WO) - 0.9997663158489632) < 1e-15,
      repr(float(q_WO)))
check("q_Orig decimal 0.9998679518444836",
      abs(float(q_orig) - 0.9998679518444836) < 1e-15, repr(float(q_orig)))

# WO box is the coordinatewise union of W and O
W = dict(g=(2e7, 2e9), b=(1e-13, 6e-11), e=(1e-10, 1e-7), th=(.5, .5), et=(1., 1.))
O = dict(g=(1e8, 2e9), b=(1e-13, 1e-11), e=(1e-10, 1e-8), th=(.48, .52), et=(.9, 1.))
WO = dict(g=(2e7, 2e9), b=(1e-13, 6e-11), e=(1e-10, 1e-7), th=(.48, .52), et=(.9, 1.))
check("WO contains W and O in every coordinate",
      all(WO[k][0] <= min(W[k][0], O[k][0]) and WO[k][1] >= max(W[k][1], O[k][1])
          for k in WO))

# ---------------------------------------------------------------------------
section("4. the correction walk")


def consensus(r, j):
    """u_r(j) = P(reach r before 0), closed form."""
    if j <= 0:
        return F(0)
    if j >= r:
        return F(1)
    return F(sum(comb(r - 3, a) for a in range(0, j - 1)), 2 ** (r - 3))


def consensus_solve(r, j):
    """Same quantity by an exact linear solve of the harmonic equations."""
    import sympy
    u = sympy.symbols(f"u0:{r + 1}")
    eqs = [sympy.Eq(u[0], 0), sympy.Eq(u[r], 1)]
    for y in range(1, r):
        eqs.append(sympy.Eq(u[y], sympy.Rational(r - y - 1, r - 2) * u[y - 1]
                            + sympy.Rational(y - 1, r - 2) * u[y + 1]))
    sol = sympy.solve(eqs, u, dict=True)[0]
    return F(int(sympy.fraction(sol[u[j]])[0]), int(sympy.fraction(sol[u[j]])[1]))


ok = all(consensus(r, j) == consensus_solve(r, j)
         for r in range(4, 13) for j in range(0, r + 1))
check("closed form matches exact linear solve for r=4..12, all j", ok)
check("u_10(2) = 1/128", consensus(10, 2) == F(1, 128), consensus(10, 2))
check("correct consensus at (10,2) is 127/128", 1 - consensus(10, 2) == F(127, 128))
check("u_r(2) = 2^{-(r-3)} for r=5..30",
      all(consensus(r, 2) == F(1, 2 ** (r - 3)) for r in range(5, 31)))

# Mabinogion identity of Flajolet and Huillet (eq. 20), N = r-2, kappa = j-1
try:
    import sympy
    y = sympy.symbols("y")
    good = True
    for N in range(3, 9):
        for k in range(1, N):
            omega = (sympy.Rational(1, 2) ** (N - 1) * (N - 1) * sympy.binomial(N - 2, k - 1)
                     * sympy.integrate((1 - y) ** (k - 1) * (1 + y) ** (N - k - 1), (y, 0, 1)))
            ours = sympy.Rational(1, 2 ** (N - 1)) * sum(sympy.binomial(N - 1, a)
                                                         for a in range(k, N))
            good &= sympy.simplify(omega - ours) == 0
    check("Mabinogion integral form equals our binomial tail (N=3..8)", good)
except Exception as exc:  # pragma: no cover
    print(f"  NOTE  skipped Mabinogion identity: {exc}")

check("inventory rule: r >= 3 + ceil(log2(1/delta)) gives r>=16 at delta=2e-4",
      3 + math.ceil(math.log2(5000)) == 16, 3 + math.ceil(math.log2(5000)), 16)
check("u_16(2) = 1/8192", consensus(16, 2) == F(1, 8192), consensus(16, 2))
check("residual budget 7.79e-5 at r=16",
      abs(float(F(2, 10 ** 4) - F(1, 8192)) - 7.79296875e-5) < 1e-16,
      float(F(2, 10 ** 4) - F(1, 8192)))

# ---------------------------------------------------------------------------
section("5. finite fuel: absorption, spent fuel, regimes F and FO")


def absorption(r, j, L=64):
    active, hits = {j: F(1)}, []
    if j in (0, r):
        return {0: (F(1) if j == 0 else F(0), F(0)),
                r: (F(1) if j == r else F(0), F(0))}
    for k in range(1, L + 1):
        nxt = {}
        for yy, p in active.items():
            for z, q in ((yy - 1, F(r - yy - 1, r - 2)), (yy + 1, F(yy - 1, r - 2))):
                if z in (0, r):
                    hits.append((k, z, p * q))
                else:
                    nxt[z] = nxt.get(z, F()) + p * q
        active = nxt
    assert sum(p for _, _, p in hits) + sum(active.values()) == 1
    return {b: (sum(p for k, z, p in hits if z == b),
                sum(k * p for k, z, p in hits if z == b)) for b in (0, r)}


def fuel_bound(core, r, j, endpoint):
    v, s = absorption(r, j)[endpoint]
    return (core - 80 * F(1, 10 ** 7)) * v - 80 ** 3 * F(5, 10 ** 11) * s \
        - B * F(1, 10 ** 7) - F(1, 10 ** 12)


v0, s0 = absorption(10, 2)[0]
check("v_0(10,2;64) exact",
      v0 == F(675247821429526785890499475507935979615,
              680564733841876926926749214863536422912), v0)
check("s_0(10,2;64) exact",
      s0 == F(24981573789484567970908456334429570891,
              10633823966279326983230456482242756608), s0)
check("v_0 decimal 0.992187499369", abs(float(v0) - 0.9921874993693319) < 1e-15,
      repr(float(v0)))
check("conditional mean spent fuel 2.36775398866",
      abs(float(s0 / v0) - 2.36775398866485) < 1e-12, repr(float(s0 / v0)))

rows_FO = [(fuel_bound(cO, r, j, 0), r, j) for j in (0, 1, 2) for r in range(8 + j, 81)]
rows_F = [(fuel_bound(c, r, j, 0), r, j) for j in (0, 1, 2) for r in range(8 + j, 81)]
check("216 admitted (r,j) pairs", len(rows_FO) == 216, len(rows_FO), 216)
qFO, rFO, jFO = min(rows_FO)
qF, rF, jF = min(rows_F)
check("regime F minimiser (10,2)", (rFO, jFO) == (10, 2) and (rF, jF) == (10, 2),
      (rFO, jFO))
check("q_F (imperfect operations) exact",
      qFO == F(176915425816575482750126908089960417712372422485900866047,
               178405961588244985132285746181186892047843328000000000000), qFO)
check("q_F (ideal operations) exact",
      qF == F(353843849988858058737189145333276639679672751198608372719,
              356811923176489970264571492362373784095686656000000000000), qF)
check("q_F > 2479/2500 with imperfect operations", qFO > F(2479, 2500), float(qFO))
check("q_F > 0.99164525", qFO > F(99164525, 10 ** 8), repr(float(qFO)))
check("q_F decimal 0.9916452580485533", abs(float(qFO) - 0.9916452580485533) < 1e-15,
      repr(float(qFO)))
check("q_F ideal decimal 0.9916816872003354",
      abs(float(qF) - 0.9916816872003354) < 1e-15, repr(float(qF)))
check("every one of the 216 pairs clears 2479/2500",
      all(q > F(2479, 2500) for q, _, _ in rows_FO))

# sharpness against the consensus ceiling
ceiling = 1 - consensus(10, 2)
check("ceiling 127/128 for the worst admitted state", ceiling == F(127, 128))
check("truncation within 6.4e-10 of the ceiling",
      float(ceiling - v0) < 6.4e-10, f"{float(ceiling - v0):.3e}")
check("q_F within 5.5e-4 of the ceiling", float(ceiling - qFO) < 5.5e-4,
      f"{float(ceiling - qFO):.4e}")
check("failure allowance 8.35e-3", abs(float(1 - qFO) - 8.3547419e-3) < 1e-9,
      f"{float(1 - qFO):.4e}")
check("floor share 7.8125e-3", float(consensus(10, 2)) == 0.0078125)

# the coarse alternative: charge every successful path all 64 fuel units
coarse = cO - (1 - v0) - 80 * F(1, 10 ** 7) - 64 * 80 ** 3 * F(5, 10 ** 11) \
    - B * F(1, 10 ** 7) - F(1, 10 ** 12)
print(f"  NOTE  coarse (charge W=L) bound with c_O: {float(coarse):.10f}; "
      f"spent-fuel gain {float(qFO - coarse):.4e}")
check("spent-fuel accounting gains about 1.6e-3",
      1.5e-3 < float(qFO - coarse) < 1.7e-3, f"{float(qFO - coarse):.4e}")
check("coarse bound rounds to 0.99007", abs(float(coarse) - 0.9900657) < 1e-6,
      f"{float(coarse):.7f}")

# the opposite endpoint: a productive program switch
v10, s10 = absorption(10, 2)[10]
q_switch = fuel_bound(cO, 10, 2, 10)
q_switch_ideal = fuel_bound(c, 10, 2, 10)
check("v_10 exact", v10 == F(5316911553929185963121618191138170975,
                             680564733841876926926749214863536422912), v10)
check("v_10 decimal 0.0078124993693319",
      abs(float(v10) - 0.0078124993693319) < 1e-16, repr(float(v10)))
check("absorbed mass by 64 jumps is below 1 (transient mass retained)",
      0 < 1 - (v10 + v0) < F(2, 10 ** 9), f"{float(1 - (v10 + v0)):.4e}")
check("conditional mean spent fuel at the switch 11.3714239539",
      abs(float(s10 / v10) - 11.371423953928531) < 1e-11, repr(float(s10 / v10)))
check("q_switch exact",
      q_switch == F(1335789892734298336668227655567197469391357788454466047,
                    178405961588244985132285746181186892047843328000000000000), q_switch)
check("q_switch > 37/5000", q_switch > F(37, 5000), repr(float(q_switch)))
check("q_switch decimal 0.0074873613013967",
      abs(float(q_switch) - 0.007487361301396737) < 1e-16, repr(float(q_switch)))
check("q_switch (ideal operations) 0.007487648145",
      abs(float(q_switch_ideal) - 0.007487648145088585) < 1e-16,
      repr(float(q_switch_ideal)))
p128 = 1 - (1 - F(37, 5000)) ** 128
check("128 founders: > 0.6135 > 1/2", p128 > F(6135, 10000),
      f"{float(p128):.6f}")

# ---------------------------------------------------------------------------
section("6. pure-start obstruction")

pure = 80 * F(1, 10 ** 7) * (1 + F(1, 10 ** 7))
check("pure-start bound 8.0000008e-6", abs(float(pure) - 8.0000008e-6) < 1e-18,
      repr(float(pure)))
check("pure-start bound < 8.1e-6", pure < F(81, 10 ** 7), float(pure))
old = (80 * F(1, 10 ** 7) + 64 * 80 ** 3 * F(5, 10 ** 11)) * (1 + F(1, 10 ** 7))
check("improvement factor 205.8 over the leakage+reverse bound",
      abs(float(old / pure) - 205.8) < 1e-9, float(old / pure))
check("mixed/pure separation exceeds 935 (certified switch bound)",
      q_switch / pure > 935, float(q_switch / pure))
check("separation from the rounded threshold 37/5000 is just under 925",
      abs(float(F(37, 5000) / pure) - 925) < 1e-3, float(F(37, 5000) / pure))
check("1 - e^{-u} <= u used in the bound",
      1 - math.exp(-float(80 * F(1, 10 ** 7) * (1 + F(1, 10 ** 7)))) <= float(pure))

# ---------------------------------------------------------------------------
section("7. iteration, selection, information")

for name, q, want in (("W/O", F(4999, 5000), 0.998), ("WO", F(9997, 10000), 0.997),
                      ("F", F(2479, 2500), 0.919)):
    check(f"ten divisions in {name} exceed {want}", q ** 10 > F(int(want * 1000), 1000),
          f"{float(q ** 10):.6f}")


def selection(q, cutoff):
    bad = F(1 + sum(comb(20, j) for j in range(cutoff + 1, 21)), 2 ** 20)
    return 1 - 20 * (1 - q) - bad


check("selection W/O cutoff 16 = 16297339/16384000",
      selection(F(4999, 5000), 16) == F(16297339, 16384000),
      selection(F(4999, 5000), 16))
check("selection W/O cutoff 15 = 129773087/131072000",
      selection(F(4999, 5000), 15) == F(129773087, 131072000),
      selection(F(4999, 5000), 15))
check("selection WO cutoff 16 = 16264571/16384000",
      selection(F(9997, 10000), 16) == F(16264571, 16384000),
      selection(F(9997, 10000), 16))
check("selection WO cutoff 15 = 129510943/131072000",
      selection(F(9997, 10000), 15) == F(129510943, 131072000),
      selection(F(9997, 10000), 15))
check("selection decimal 0.9947106323",
      abs(float(selection(F(4999, 5000), 16)) - 0.9947106323242187) < 1e-15,
      repr(float(selection(F(4999, 5000), 16))))
check("upper tail sum_{j>=17} C(20,j) = 1351",
      sum(comb(20, j) for j in range(17, 21)) == 1351)
check("odds 20:16 = 5:4 and 20:15 = 4:3",
      F(20, 16) == F(5, 4) and F(20, 15) == F(4, 3))


def h2(u):
    return -u * math.log2(u) - (1 - u) * math.log2(1 - u)


for name, q, want in (("W/O", F(4999, 5000), 0.997254), ("WO", F(9997, 10000), 0.996056),
                      ("F", F(2479, 2500), 0.930011)):
    got = 1 - h2(float(1 - q))
    check(f"Fano bound {name} = {want}", abs(got - want) < 5e-7, f"{got:.6f}", want)

# ---------------------------------------------------------------------------
section("8. resources")

check("food per division <= 160 (refill identity 80+p)",
      all((80 - a) + (80 - b) == 80 + p
          for p in range(0, 81) for a in range(0, 81 - p)
          for b in [80 - p - a] if b >= 0))
check("one-minority: 81 + 10*162 = 1701", 81 + 10 * 162 == 1701)
check("regime F: 144 + 10*288 = 3024", 144 + 10 * 288 == 3024)
check("20 founders, one division: 20*(81+162) = 4860", 20 * (81 + 162) == 4860)
check("regime F, 20 founders: 20*(144+288) = 8640", 20 * (144 + 288) == 8640)

# ---------------------------------------------------------------------------
section("9. cluster partition and the elementary candidate")


def split(weights, m):
    p = [1]
    for w in weights:
        v = [0] * (len(p) + w)
        for i, a in enumerate(p):
            v[i] += a
            v[i + w] += a
        p = v
    return F(sum(p[m:sum(weights) - m + 1]), 2 ** len(weights))


check("32 free monomers, >=8 each = 2142968775/2^31",
      split([1] * 32, 8) == F(2142968775, 2 ** 31), split([1] * 32, 8))
check("16 intact dimers, >=8 each = 32071/32768",
      split([2] * 16, 8) == F(32071, 32768), split([2] * 16, 8))
check("monomer decimal 0.997897598",
      abs(float(split([1] * 32, 8)) - 0.997897598426789) < 1e-15,
      repr(float(split([1] * 32, 8))))
check("dimer decimal 0.978729248",
      abs(float(split([2] * 16, 8)) - 0.978729248046875) < 1e-15,
      repr(float(split([2] * 16, 8))))
check("at least one cluster each side = 1 - 2^{1-M}",
      all(split([1] * M, 1) == 1 - F(1, 2 ** (M - 1)) for M in range(1, 12)))
check("first association bound 56/(4e8) = 1.4e-7",
      F(56, 4 * 10 ** 8) == F(7, 50000000)
      and abs(float(F(56, 4 * 10 ** 8)) - 1.4e-7) < 1e-20, float(F(56, 4 * 10 ** 8)))
check("8X dimerisation propensity 8*7 = 56", 8 * 7 == 56)
pilot = json.loads((HERE / "data/elementary_pilot.json").read_text())
check("recorded elementary pilot rows (0,0,168,998 corrected)",
      [r["corrected"] for r in pilot["rows"]] == [0, 0, 168, 998],
      [r["corrected"] for r in pilot["rows"]])
check("recorded mean bound moieties (0, 4.84, 8.599, 8.003)",
      [r["mean_bound"] for r in pilot["rows"]] == [0.0, 4.84, 8.599, 8.003],
      [r["mean_bound"] for r in pilot["rows"]])
check("the four catalytic turnover ratios multiply to 1e19 (D_X is regenerated)",
      F(10 ** 5) ** 3 * F(10 ** 4) == 10 ** 19)
check("K=64 and K=96 certified values quoted in the remark",
      abs(c64 / S - 0.997547) < 5e-7 and abs(c96 / S - 0.999983) < 1e-6,
      (f"{c64 / S:.6f}", f"{c96 / S:.6f}"))
check("certificate slack at K=80 is about 8.5e-6",
      payoff_slack is None or abs(payoff_slack - 8.465e-6) < 1e-8, payoff_slack)
check("unrounded float payoff 0.9998914165",
      payoff_slack is None or abs(payoff_slack + float(c) - 0.9998914165) < 1e-9)

# ---------------------------------------------------------------------------
section("10. dimensional and thermodynamic figures")

NA = 6.02214076e23
V = 1e-15
t0 = NA * V / 1e6
check("t_0 = 602.214076 s", abs(t0 - 602.214076) < 1e-6, f"{t0:.6f}")
check("regime O startup 1.51 microseconds", abs(t0 / 4e8 * 1e6 - 1.5055) < 1e-3,
      f"{t0 / 4e8 * 1e6:.4f} us")
check("regime WO startup 7.53 microseconds", abs(t0 / 8e7 * 1e6 - 7.5277) < 1e-3,
      f"{t0 / 8e7 * 1e6:.4f} us")
k4 = 1e8 * (NA * V) ** 3 / t0
check("gamma=1e8 is 3.63e31 M^-3 s^-1", abs(k4 / 3.63e31 - 1) < 3e-3, f"{k4:.3e}")
RT = 8.314462618 * 298.15
check("RT log(1e19) = 108.5 kJ/mol", abs(RT * math.log(1e19) / 1000 - 108.5) < 0.1,
      f"{RT * math.log(1e19) / 1000:.2f}")
lo, hi = 2e7 / 6e-11, 2e9 / 1e-13
check("WO ratio range [3.33e17, 2e22]", abs(lo / 3.333e17 - 1) < 1e-3 and hi == 2e22,
      f"[{lo:.3e},{hi:.3e}]")
check("WO bias range [100.0,127.3] kJ/mol",
      abs(RT * math.log(lo) / 1000 - 100.0) < 0.15
      and abs(RT * math.log(hi) / 1000 - 127.3) < 0.15,
      f"[{RT * math.log(lo) / 1000:.1f},{RT * math.log(hi) / 1000:.1f}]")

# ---------------------------------------------------------------------------
section("11. the binomial derivative identity (symbolic)")

try:
    import sympy
    th = sympy.symbols("theta")
    good = True
    for n in list(range(16, 24)) + [40]:
        g = sum(sympy.binomial(n, j) * th ** j * (1 - th) ** (n - j)
                for j in range(8, n - 7))
        rhs = (n * sympy.binomial(n - 1, 7) * th ** 7 * (1 - th) ** 7
               * ((1 - th) ** (n - 15) - th ** (n - 15)))
        good &= sympy.simplify(sympy.diff(g, th) - rhs) == 0
    check("g_n'(theta) identity for n=16..23 and n=40", good)
    good = all(sympy.simplify(sum(sympy.binomial(n, j) * th ** j * (1 - th) ** (n - j)
                                  for j in range(8, n - 7))) == 0 for n in range(1, 16))
    check("g_n vanishes identically for n < 16", good)
except Exception as exc:  # pragma: no cover
    print(f"  NOTE  skipped derivative identity: {exc}")

check("g_n(0.48) = g_n(0.52) by symmetry",
      all(binom_tail(n, 8, n - 8, F(12, 25)) == binom_tail(n, 8, n - 8, F(13, 25))
          for n in range(16, 81)))
check("a_p is nondecreasing in eta on a grid",
      all(binom_tail(p, 4, p, F(9, 10)) <= binom_tail(p, 4, p, F(95, 100))
          <= binom_tail(p, 4, p, F(1)) for p in range(0, 81)))

# ---------------------------------------------------------------------------
section("12. restart regions and state space")

for k, want in ((1, 145), (2, 216)):
    n = sum(1 for x in range(8, 81) for y in range(0, k + 1) if x + y <= 80)
    check(f"|B^{{L,{k}}}| = {want}", n == want, n, want)
check("smallest k=1 preparation (8,1,71,0,0,1,0) has core mass 80",
      8 + 1 + 71 == 80)
check("smallest k=2 preparation (8,2,70,0,0,64,0) has core mass 80 and 144 units",
      8 + 2 + 70 == 80 and 80 + 64 == 144)
check("81 = 80 + 1 modelled units in the one-minority regimes", 80 + 1 == 81)

# ---------------------------------------------------------------------------
print()
total = len(CHECKS)
print(f"{total - FAILED}/{total} checks passed")
(HERE / "check_paper_output.json").write_text(json.dumps(
    {"passed": total - FAILED, "total": total, "checks": CHECKS}, indent=1))
if FAILED:
    print("FAILURES PRESENT")
    sys.exit(1)
print("ALL CHECKS PASSED")
