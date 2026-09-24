"""Exact rational N=16 smooth-readout certificate on a partition of a slope interval.

For each subinterval [s0, s1] the hazard of every state is enclosed by the
statewise envelope of its two endpoint values (the hazard is monotone in s at
each fixed state), with rational exponential bounds.  Upper risks are exact
supersolutions under the UPPER hazard envelope; lower risks are downward-rounded
monotone iterates from zero under the LOWER envelope.  Pointwise death coupling
makes extinction monotone in the hazard vector, so the boxes hold for every
slope in the subinterval.  All asserted comparisons are exact rationals; numpy
is used only to propose the supersolution, which is then checked exactly.

usage: python slope_certificate.py 7 9 20      (20 equal subintervals)
       python slope_certificate.py 7.999 8.001 1
"""
import sys, json, time
from fractions import Fraction as F
from math import comb
from pathlib import Path
import numpy as np
from model import source, pair

N = 16; S = 10 ** 14; B = F(1, 10)
OUT = Path(__file__).resolve().parents[1] / "data"


def exp_bounds(x):
    if x < 0:
        l, u = exp_bounds(-x); return 1 / u, 1 / l
    terms = [F(1)]
    for j in range(1, 121):
        terms.append(terms[-1] * x / j)
    l = sum(terms); u = l + terms[-1] * x / 121 / (1 - x / 122)
    return l, u


def hazards(s0, s1, states):
    dl, du = [], []
    for a, r in states:
        lo, hi = [], []
        for s in (s0, s1):
            el, eu = exp_bounds(s * F(a - r, N))
            lo.append(F(1, 100) + F(29, 100) / (1 + eu)); hi.append(F(1, 100) + F(29, 100) / (1 + el))
        dl.append(F(int(min(lo) * S), S))                       # floor
        du.append(F(-((-max(hi) * S).__floor__()), S))          # ceiling
    return dl, du


def certificate(s0, s1):
    states, ix, Qf, Df, pairsf = source(N)
    n = len(states)
    dl, du = hazards(s0, s1, states)
    qoff, exitr, ps = [], [], []
    for a, r in states:
        u = N - a - r; row = []
        for st, v in (((a + 1, r), u * (F(1, 100) + F(a, N))), ((a, r + 1), u * (F(1, 100) + F(r, N))),
                      ((a - 1, r), a * (F(1, 100) + F(r, 2 * N))), ((a, r - 1), r * (F(1, 100) + F(a, 2 * N)))):
            if v:
                row.append((ix[st], v))
        qoff.append(row); exitr.append(sum(v for _, v in row))
        ps.append([(ix[i, j], ix[a - i, r - j], F(comb(a, i) * comb(r, j), 2 ** (a + r)))
                   for i in range(a + 1) for j in range(r + 1)])
    res = {}
    duf = np.array([float(x) for x in du])
    Rf = np.linalg.inv(np.diag(duf + .1) - Qf)
    for ind in (False, True):
        # --- floating proposal under the upper hazard
        z = np.zeros(n)
        for _ in range(100000):
            zn = Rf @ (duf + .1 * ((Df @ z) ** 2 if ind else pair(pairsf, z, z, n)))
            if np.max(np.abs(zn - z)) < 1e-14:
                break
            z = zn
        if ind:
            J = .2 * np.diag(Df @ z) @ Df
        else:
            J = np.zeros((n, n)); ii, jj, kk, pp = pairsf
            np.add.at(J, (ii, jj), .1 * pp * z[kk]); np.add.at(J, (ii, kk), .1 * pp * z[jj])
        J += Qf - np.diag(duf + .1)
        wv = np.linalg.solve(-J, np.ones(n)); assert wv.min() > 0
        upper = [F(int(np.ceil((z[i] + 1e-8 * wv[i]) * S)), S) for i in range(n)]
        assert max(upper) < 1
        # --- exact supersolution residuals
        minres = None
        for i, row in enumerate(ps):
            if ind:
                dz = sum(p * upper[j] for j, k, p in row); pr = dz * dz
            else:
                pr = sum(p * upper[j] * upper[k] for j, k, p in row)
            resid = (exitr[i] + du[i] + B) * upper[i] - sum(v * upper[j] for j, v in qoff[i]) - du[i] - pr / 10
            assert resid > 0
            minres = resid if minres is None or resid < minres else minres
        # --- exact downward iteration under the lower hazard (integer arithmetic, units 1/S)
        cr, ar, br, dr, d1 = [], [], [], [], []
        for i, row in enumerate(ps):
            den = exitr[i] + dl[i] + B
            cr.append(int(S * dl[i] / den)); ar.append([(j, int(S * v / den)) for j, v in qoff[i]])
            br.append([(j, k, int(S * p / (10 * den))) for j, k, p in row])
            dr.append(int(S / (10 * den))); d1.append([(j, int(p * S)) for j, k, p in row])
        zi = [0] * n
        for it in range(20000):
            zn = []
            for i in range(n):
                val = cr[i] * S + sum(c * zi[j] for j, c in ar[i])
                if ind:
                    dz = sum(c * zi[j] for j, c in d1[i]) // S
                    val += dr[i] * dz * dz // S
                else:
                    val += sum(c * zi[j] * zi[k] for j, k, c in br[i]) // S
                zn.append(val // S)
            assert min(zn[i] - zi[i] for i in range(n)) >= 0
            done = max(zn[i] - zi[i] for i in range(n)) <= 2
            zi = zn
            if done:
                break
        lower = [F(v, S) for v in zi]
        assert all(lower[i] <= upper[i] for i in range(n))
        res["I" if ind else "J"] = dict(lower=lower, upper=upper, iterations=it + 1, minres=minres)
    return states, ix, dl, du, res


def main():
    s_lo, s_hi, m = F(sys.argv[1]), F(sys.argv[2]), int(sys.argv[3])
    t0 = time.time(); rows = []
    for c in range(m):
        s0 = s_lo + (s_hi - s_lo) * c / m; s1 = s_lo + (s_hi - s_lo) * (c + 1) / m
        states, ix, dl, du, res = certificate(s0, s1)
        k97, kA = ix[9, 7], ix[16, 0]
        J, I = res["J"], res["I"]
        gaps = [I["lower"][i] - J["upper"][i] for i in range(len(states))]
        row = dict(s0=str(s0), s1=str(s1),
                   qJ97=[str(J["lower"][k97]), str(J["upper"][k97])],
                   qI97=[str(I["lower"][k97]), str(I["upper"][k97])],
                   gap97_lower=str(gaps[k97]), gap97_upper=str(I["upper"][k97] - J["lower"][k97]),
                   gapA_upper=str(I["upper"][kA] - J["lower"][kA]),
                   qImax_upper=str(max(I["upper"])), qJmax_upper=str(max(J["upper"])),
                   iterations=[J["iterations"], I["iterations"]],
                   min_residual=[str(J["minres"]), str(I["minres"])],
                   max_width=float(max(max(X["upper"][i] - X["lower"][i] for i in range(len(states))) for X in (J, I))))
        if m == 1:
            row["death_lower"] = [str(x) for x in dl]; row["death_upper"] = [str(x) for x in du]
            row["states"] = states
            for lab, X in (("joint", J), ("independent", I)):
                row[lab + "_lower"] = [str(x) for x in X["lower"]]; row[lab + "_upper"] = [str(x) for x in X["upper"]]
        rows.append(row)
        print(f"[{float(s0):.4f},{float(s1):.4f}] gap97>{float(gaps[k97]):.6f} qJ97<{float(J['upper'][k97]):.6f} "
              f"qI97>{float(I['lower'][k97]):.6f} qImax<{float(max(I['upper'])):.6f} it={row['iterations']} "
              f"t={time.time() - t0:.0f}s", flush=True)
    summary = dict(N=N, interval=[str(s_lo), str(s_hi)], pieces=m,
                   gap97_lower=str(min(F(r["gap97_lower"]) for r in rows)),
                   gap97_lower_decimal=float(min(F(r["gap97_lower"]) for r in rows)),
                   gapA_upper_decimal=float(max(F(r["gapA_upper"]) for r in rows)),
                   qJ97_upper_decimal=float(max(F(r["qJ97"][1]) for r in rows)),
                   qI97_lower_decimal=float(min(F(r["qI97"][0]) for r in rows)),
                   qImax_upper_decimal=float(max(F(r["qImax_upper"]) for r in rows)),
                   seconds=time.time() - t0, rows=rows)
    name = f"slope_certificate_{sys.argv[1]}_{sys.argv[2]}_{m}.json".replace("/", "-")
    OUT.mkdir(exist_ok=True); (OUT / name).write_text(json.dumps(summary, indent=1))
    print({k: v for k, v in summary.items() if k != "rows"})


if __name__ == "__main__":
    main()
