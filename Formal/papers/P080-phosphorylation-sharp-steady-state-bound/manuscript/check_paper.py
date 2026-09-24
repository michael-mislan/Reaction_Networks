"""Exact replay of every computational statement in the paper.

Usage:  python check_paper.py [--full]
Standard library only (fractions).  Exits nonzero on the first failed check.
--full extends the exact Routh stability census from n <= 6 to n <= 10
(about 25 minutes); everything else runs in well under a minute.
These are finite checks of exposition and implementation.  The theorems of the
paper are proved for all n in the text and do not depend on this file.
"""
import json
import os
import random
import sys
import time
from fractions import Fraction as Q

from phos_sharp import (add, build, chart, charpoly, convert, deriv, det, mul, pair,
                        ratio, rates_from, reduced_jacobian, routh_rhp, scale, state_from,
                        totals, trim, val, vector_field)

CHECKS = 0
REPORT = {}


def ok(cond, msg):
    global CHECKS
    if not cond:
        print("FAILED:", msg)
        sys.exit(1)
    CHECKS += 1


def canonical(n):
    xs = [Q(j + 2) for j in range(2 * n - 1)]
    r = Q((4 * n * n - 1) // 8 + 1)
    return xs, r


# ---------------------------------------------------------------- Sturm tools
def prem(a, b):
    a = trim(a)
    while a != [0] and len(a) >= len(b):
        k = len(a) - len(b)
        c = a[-1] / b[-1]
        for j in range(len(b)):
            a[j + k] -= c * b[j]
        a = trim(a)
    return a


def sturm(p):
    seq = [trim(p), deriv(p)]
    while seq[-1] != [0]:
        rem = scale(-1, prem(list(seq[-2]), seq[-1]))
        if rem == [0]:
            break
        seq.append(rem)
    return seq


def variations(seq, x):
    if x == "+inf":
        v = [p[-1] for p in seq]
    elif x == "-inf":
        v = [p[-1] * (-1) ** (len(p) - 1) for p in seq]
    else:
        v = [val(p, x) for p in seq]
    s = [1 if t > 0 else -1 for t in v if t != 0]
    return sum(a != b for a, b in zip(s, s[1:]))


def real_roots(p, a, b):
    seq = sturm(p)
    return variations(seq, a) - variations(seq, b)


def poly_in_x(p):
    """p(u(x)) as a polynomial in x, u=(x^2-1)/8."""
    out = [Q(0)]
    ux = [Q(-1, 8), Q(0), Q(1, 8)]
    pw = [Q(1)]
    for c in p:
        out = add(out, scale(c, pw))
        pw = mul(pw, ux)
    return out


# ------------------------------------------------ 1. construction, n = 1..8
t0 = time.time()
states_checked = 0
for n in range(1, 9):
    xs, r = canonical(n)
    rec = build(xs, r)
    ok(rec["positive"], "positivity n=%d" % n)
    N, J, A, B, D = rec["N"], rec["J"], rec["A"], rec["B"], rec["D"]
    ok(len(N) == n and len(J) == n and min(N) > 0 and min(J) > 0, "Lemma 3.1 positivity")
    # identity (x-1)N(u(x)) - 2J(u(x)) = Pi(x) as polynomials in x
    Pi = [Q(1)]
    for x in xs:
        Pi = mul(Pi, [-x, Q(1)])
    lhs = add(mul([Q(-1), Q(1)], poly_in_x(N)), scale(-2, poly_in_x(J)))
    ok(lhs == Pi, "product identity n=%d" % n)
    # leading coefficients
    ok(N[-1] == 8 ** (n - 1) and J[-1] == 8 ** (n - 1) * (sum(xs) - 1) / 2, "leading coefficients")
    ok(J[0] * 2 == __import__("math").prod([x - 1 for x in xs]), "J(0)")
    # conversion identity (cx+e)Pi
    nr, jr = val(N, r), val(J, r)
    c, e = jr, 4 * r * nr - jr
    Lraw = add(rec["Braw"], scale(-r, rec["Draw"]))
    lhs = add(mul([Q(-1), Q(1)], poly_in_x(Lraw)),
              scale(2, mul(add(poly_in_x([Q(0), Q(1)]), [-r]), poly_in_x(rec["Draw"]))))
    ok(lhs == mul([e, c], Pi), "conversion identity n=%d" % n)
    for st in rec["states"]:
        x, u, z = st["x"], st["u"], st["z"]
        ok(min(z) > 0, "positive state")
        ok(all(v == 0 for v in vector_field(rec["rates"], z)), "literal equilibrium")
        ok(totals(z) == (2 * r, Q(2), 2 * (r + 1)), "common totals")
        ok(z[n + 1] == (x - 1) / 2 and z[n + 2] == 4 / (x + 1), "free enzymes")
        ok(sum(z[:n + 1]) == z[n + 1] + z[n + 2], "free substrate = free enzymes")
        H, dH, s, f, Lv, Mv = chart(A, B, D, r, Q(2), u)
        ok(Lv > 0 and Mv > 0 and s == st["s"] and f == st["f"] and H == 2 * (r + 1), "regular chart")
        dPi = Q(1)
        for y in xs:
            if y != x:
                dPi *= x - y
        slope = -16 * (1 + u) * (c * x + e) * dPi / ((r - u) * (x + 1) ** 2 * val(rec["Draw"], u))
        ok(dH == slope and dH != 0, "slope formula")
        states_checked += 1
    signs = [chart(A, B, D, r, Q(2), st["u"])[1] > 0 for st in rec["states"]]
    ok(signs == [j % 2 == 1 for j in range(2 * n - 1)], "alternating slopes")
REPORT["construction_states_checked"] = states_checked

# ------------------------------------------------ 2. interlacing (Lemma 4.1)
random.seed(11)
inter = 0
for trial in range(60):
    m = random.randint(1, 5)
    xs = sorted({1 + Q(random.randint(1, 4000), random.choice([7, 100, 1000])) for _ in range(2 * m + 1)})
    if len(xs) < 2 * m + 1:
        continue
    random.shuffle(xs)
    N, J = pair(xs)
    ok(real_roots(N, "-inf", Q(-1, 8)) == m, "N real-rooted below -1/8")
    ok(real_roots(J, "-inf", Q(0)) == m, "J real-rooted, negative")
    W = add(mul(deriv(N), J), scale(-1, mul(N, deriv(J))))
    ok(real_roots(W, "-inf", "+inf") == 0 and val(W, Q(0)) < 0, "N'J-NJ' < 0 on the real line")
    inter += 1
REPORT["interlacing_instances"] = inter

# ------------------------------------------------ 3. threshold theorem (Theorem 4.2)
def second_condition(r, sx):
    t = sx - 4 * r
    return t <= 0 or t * t <= 1 + 8 * r


thr = 0
for trial in range(400):
    m = random.randint(0, 6)
    mode = random.random()
    if mode < 0.35:
        xs = [Q(random.randint(1001, 1100), 1000) for _ in range(2 * m + 1)]
    elif mode < 0.7:
        xs = [Q(random.randint(101, 100000), 100) for _ in range(2 * m + 1)]
    else:
        xs = [1 + Q(random.randint(1, 10 ** 6), 10 ** random.randint(1, 6)) for _ in range(2 * m + 1)]
    if len(set(xs)) < len(xs):
        continue
    umax, sx = max(ratio(x) for x in xs), sum(xs)
    lo, hi = Q(0), sx
    for _ in range(40):
        mid = (lo + hi) / 2
        lo, hi = (lo, mid) if second_condition(mid, sx) else (mid, hi)
    r = max(hi, umax * (1 + Q(1, 10 ** 6)) + Q(1, 10 ** 9))
    ok(r > umax and second_condition(r, sx), "threshold hypotheses")
    rec = build(xs, r)
    ok(rec["positive"], "threshold theorem instance")
    ok(all(v == 0 for st in rec["states"] for v in vector_field(rec["rates"], st["z"])), "equilibria")
    for rr in (Q(1, 1000), umax / 3, umax * 7):
        ok(min(convert(rec["N"], rec["J"], rr)[0]) > 0, "D_raw positive for every r>0")
    thr += 1
for n in range(1, 13):                       # Corollary 4.3: every r > (4n^2-1)/8
    xs = [Q(j + 2) for j in range(2 * n - 1)]
    for eps in (Q(1, 10 ** 6), Q(1, 2), Q(40)):
        ok(build(xs, Q(4 * n * n - 1, 8) + eps)["positive"], "arithmetic family n=%d" % n)
REPORT["threshold_instances"] = thr
# the threshold is not vacuous: B_raw fails just above max u_j for clustered roots
bad = [Q(1059, 1000), Q(1098, 1000), Q(1003, 1000), Q(1029, 1000), Q(1038, 1000)]
ok(not build(bad, max(ratio(x) for x in bad) + Q(1, 10 ** 6))["positive"], "necessity example")
Nb, Jb = pair(bad)
ok(convert(Nb, Jb, Q(64, 100))[1][-1] < 0 < convert(Nb, Jb, Q(66, 100))[1][-1], "sign change of lead(B_raw)")
ok(not second_condition(Q(674, 1000), sum(bad)) and second_condition(Q(675, 1000), sum(bad)), "0.675")
for rr in (Q(3, 10), Q(64, 100), Q(66, 100), Q(3)):     # positivity <=> leading coefficient
    Bb = convert(Nb, Jb, rr)[1]
    ok((min(Bb) > 0) == (Bb[-1] > 0), "B_raw positive iff leading coefficient positive")

# ------------------------------------------------ 4. determinant formula (Prop. 6.2)
for n in range(1, 5):
    xs, r = canonical(n)
    rec = build(xs, r)
    for st in rec["states"]:
        H, dH, s, f, Lv, Mv = chart(rec["A"], rec["B"], rec["D"], r, Q(2), st["u"])
        P = Q(1)
        for (a, b, c, al, be, ga) in rec["rates"]:
            P *= (b + c) * (be + ga) * ga * al / (be + ga)
        pred = (-1) ** (n + 1) * P * f ** n * st["u"] * Mv * dH
        ok(det(reduced_jacobian(rec["rates"], st["z"])) == pred, "determinant formula n=%d" % n)
# also at generic (non-constructed) rates: perturb, locate nothing; formula is an identity in the
# chart, so test it at a random positive equilibrium of random rates.
for trial in range(20):
    n = random.randint(1, 3)
    rates = [tuple(Q(random.randint(1, 30), random.randint(1, 30)) for _ in range(6)) for _ in range(n)]
    t = [Q(1)]
    Bc, Dc = [], []
    for (a, b, c, al, be, ga) in rates:
        p, q = a / (b + c), al / (be + ga)
        Bc.append(p * t[-1])
        t.append(t[-1] * c * p / (ga * q))
        Dc.append(q * t[-1])
    u, s, f = (Q(random.randint(1, 40), 7) for _ in range(3))
    z = state_from(t, Bc, Dc, u, s, f)
    ok(all(v == 0 for v in vector_field(rates, z)), "parametrisation of all equilibria")
    ET, FT, ST = totals(z)
    r = ET / FT
    if r == u:
        continue
    H, dH, s2, f2, Lv, Mv = chart(t, Bc, Dc, r, FT, u)
    ok(s2 == s and f2 == f and H == ST, "chart recovers the state")
    P = Q(1)
    for (a, b, c, al, be, ga) in rates:
        P *= (b + c) * (be + ga) * ga * al / (be + ga)
    ok(det(reduced_jacobian(rates, z)) == (-1) ** (n + 1) * P * f ** n * u * Mv * dH,
       "determinant formula, generic rates")

# ------------------------------------------------ 5. exact Routh census
nmax = 10 if "--full" in sys.argv else 6
census = {}
for n in range(1, nmax + 1):
    xs, r = canonical(n)
    rec = build(xs, r)
    pattern = [routh_rhp(charpoly(reduced_jacobian(rec["rates"], st["z"])))[0] for st in rec["states"]]
    ok(pattern == [j % 2 for j in range(2 * n - 1)], "stable/saddle pattern n=%d" % n)
    census[n] = pattern
REPORT["routh_census_nmax"] = nmax

# ------------------------------------------------ 6. the three-site example
xs, r = canonical(3)
ok(r == 5, "example r")
rec = build(xs, r)
A, B, D = rec["A"], rec["B"], rec["D"]
ok(rec["N"] == [1200, 1256, 64] and rec["J"] == [60, 1852, 608], "N, J")
ok(D == [1, Q(69002, 3405), Q(9808, 3405)], "D")
ok(B == [Q(34797, 454), Q(308833, 2270), Q(5236, 1135)], "B")
ok(rec["rates"] == [(2, Q(454, 34797), Q(454, 34797), Q(6810, 72407), 1, 1),
                    (Q(138004, 72407), Q(138004, 926499), Q(138004, 926499), Q(69002, 39405), 1, 1),
                    (Q(9808, 39405), Q(2452, 3927), Q(2452, 3927), 2, 1, 1)], "rate table")
ok(rec["totals"] == (10, 2, 12), "totals")
L = add(B, scale(-r, D))
ok(L[2] < 0 and val(L, Q(0)) > 0 and val(L, Q(5)) > 0, "L concave and positive on [0,5]")
delta = Q(1, 500)
probes = [Q(1, 20), Q(69, 128), Q(4327, 3200), Q(7917, 3200), Q(6373, 1600), Q(399, 80)]
resid = [chart(A, B, D, r, Q(2), u)[0] - 12 for u in probes]
ok(all((-1) ** k * v > delta for k, v in enumerate(resid)), "S_T window: alternating probes beyond 1/500")
us = [st["u"] for st in rec["states"]]
ok(all(probes[k] < us[k] < probes[k + 1] for k in range(5)), "probes separate the five roots")
table = []
for st in rec["states"]:
    z = st["z"]
    dH = chart(A, B, D, r, Q(2), st["u"])[1]
    table.append(dict(u=str(st["u"]), E=str(z[4]), F=str(z[5]), S3=float(z[3]),
                      S3_plus_Y3=float(z[3] + z[-1]), Hprime=float(dH),
                      kinase_bound=str(1 - z[4] / 10), phosphatase_bound=str(1 - z[5] / 2),
                      flux=str(sum(z[9:]))))
REPORT["example_n3"] = table
# general sufficient bound (A.1) of the appendix for this example
N, J = rec["N"], rec["J"]
bound = max(4 * sum(N) * sum(J) / (N[-1] * min(J)), 2 * sum(J) * (sum(N) + sum(J)) / (N[-1] * min(J)))
ok(bound == 6615, "appendix bound equals 6615 for the example")

# ------------------------------------------------ 7. readouts, flux, loading (Prop. 7.1)
for n in range(1, 8):
    xs, r = canonical(n)
    rec = build(xs, r)
    last = [st["z"][n] for st in rec["states"]]
    tot = [st["z"][n] + st["z"][-1] for st in rec["states"]]
    ok(all(a < b for a, b in zip(last, last[1:])) and all(a < b for a, b in zip(tot, tot[1:])),
       "ordered readouts")
    for st in rec["states"]:
        x, z = st["x"], st["z"]
        flux = sum(c * z[n + 3 + i] for i, (a, b, c, al, be, ga) in enumerate(rec["rates"]))
        ok(flux == 2 * (x - 1) / (x + 1), "total phosphorylation flux")
        ok(sum(z[n + 3:2 * n + 3]) / (2 * r) == 1 - (x - 1) / (4 * r), "kinase loading")
        ok(sum(z[2 * n + 3:]) / 2 == 1 - 2 / (x + 1), "phosphatase loading")

# ------------------------------------------------ 8. kinetic freedom (Prop. 2.1)
xs, r = canonical(3)
rec = build(xs, r)
A, B, D = rec["A"], rec["B"], rec["D"]
for trial in range(10):
    rates = []
    for i in range(3):
        lam, b, be = (Q(random.randint(1, 50), random.randint(1, 50)) for _ in range(3))
        p, q = B[i] / A[i], D[i] / A[i + 1]
        c = lam * D[i] / B[i]
        rates.append(((b + c) * p, b, c, (be + lam) * q, be, lam))
    ok(all(v == 0 for st in rec["states"] for v in vector_field(rates, st["z"])),
       "equilibria preserved under kinetic retuning")

# ------------------------------------------------ 9. fixed-root large-r limits (Remark 7.3)
xs = [Q(j) for j in range(2, 7)]
N, J = pair(xs)
big = Q(10 ** 12)
recb = build(xs, big)
for i in range(3):
    ok(abs(float(recb["D"][i] - J[i] / J[0])) < 1e-9 * float(J[i] / J[0]) + 1e-9, "D -> J/d0")
    ok(abs(float(recb["B"][i] / big - (J[i] + N[i]) / J[0])) < 1e-8 * float((J[i] + N[i]) / J[0]), "B/r -> (J+N)/d0")

REPORT["checks_passed"] = CHECKS
REPORT["seconds"] = round(time.time() - t0, 1)
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check_paper_report.json")
with open(out, "w") as fh:
    json.dump(REPORT, fh, indent=1)
print("all %d checks passed in %.1f s (Routh census through n=%d)" % (CHECKS, time.time() - t0, nmax))
