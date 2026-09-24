"""Sharp constants, biased allocation, rate spread and scaling for the
cooperative-gate proportion-memory class.

All numbers printed here are exact rationals unless a float is explicitly
requested for display.
"""
from __future__ import annotations

import json
import time
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, lgamma, log, log10

LN10 = log(10)


def log10_fact(n: int) -> float:
    return lgamma(n + 1) / LN10


def log10_k(lx, ly, fc, a=20):
    return log10(a) - log10_fact(lx) - log10_fact(ly) - log10_fact(fc)
from pathlib import Path

from frontier_proportion import Psi, coordinate_value, frontier, prefix

OUT = Path(__file__).resolve().parent.parent / 'data'


# ---------------------------------------------------------------- clock ----
def clock_lower(A: F, D: F, T: F = F(1), terms: int = 40) -> F:
    """Exact rational lower bound for r(a,d) = a/(a+d)(1-e^{-(a+d)T}) valid for
    every a >= A and d <= D, using a positive truncated Taylor sum for e^{AT}."""
    s = sum((F(A * T) ** j / factorial(j) for j in range(terms)), F(0))
    return (A / (A + D)) * (1 - 1 / s)


# ------------------------------------------------------- biased allocation --
@lru_cache(maxsize=None)
def psi_theta(n: int, l: int, u: int, theta: F) -> F:
    """P(l <= I <= u and l <= n-I <= u), I ~ Bin(n, theta). Exact."""
    lo, hi = max(l, n - u), min(u, n - l)
    if lo > hi:
        return F(0)
    return sum((F(comb(n, i)) * theta ** i * (1 - theta) ** (n - i)
                for i in range(lo, hi + 1)), F(0))


def coordinate_theta(l: int, u: int, g: int, theta: F) -> F:
    """Uniform two-daughter return for one coordinate at allocation bias theta.
    Parent-count endpoints suffice for every fixed theta (monotone coupling)."""
    return min(psi_theta(l + g, l, u, theta), psi_theta(u + g, l, u, theta))


def joint_theta(w, theta: F) -> F:
    return (coordinate_theta(w['lx'], w['ux'], w['gx'], theta)
            * coordinate_theta(w['ly'], w['uy'], w['gy'], theta))


# ------------------------------------------------------------ rate spread --
def log10_propensity(x, y, lx, ly, fc, core):
    """log10 of (x)_{lx} (y)_{ly} (f)_{fc} with f = core-x-y, falling factorials."""
    f = core - x - y
    s = 0.0
    for n, r in ((x, lx), (y, ly), (f, fc)):
        if n < r:
            return None
        for j in range(r):
            s += log10(n - j)
    return s


def spread(w, core, k_log10):
    lx, ux, ly, uy = w['lx'], w['ux'], w['ly'], w['uy']
    fc = w['gx'] + w['gy'] + w['q']
    vals = []
    for x in range(lx, ux + 1):
        for y in range(ly, uy + 1):
            v = log10_propensity(x, y, lx, ly, fc, core)
            if v is not None:
                vals.append((v, x, y))
    lo = min(vals)
    hi = max(vals)
    # concavity: the minimum of a concave function on a rectangle is at a vertex
    verts = [log10_propensity(x, y, lx, ly, fc, core)
             for x in (lx, ux) for y in (ly, uy)]
    return dict(min_log10=lo[0] + k_log10, min_at=[lo[1], lo[2]],
                max_log10=hi[0] + k_log10, max_at=[hi[1], hi[2]],
                span_log10=hi[0] - lo[0],
                vertex_min_is_global=abs(min(v for v in verts if v is not None) - lo[0]) < 1e-9)


def main():
    res = {}
    t0 = time.monotonic()

    PUB = dict(lx=65, ux=195, gx=121, ly=8, uy=64, gy=30, q=4, core=414)

    # 1. sharp clock ---------------------------------------------------------
    A, D = F(20), F(1, 100000)
    r_star = clock_lower(A, D)
    taylor25 = sum((F(20) ** j / factorial(j) for j in range(25)), F(0))
    res['clock'] = dict(A=str(A), D=str(D), r_star=str(r_star),
                        r_star_display=float(r_star),
                        union_bound_old='49999/50000',
                        taylor25_exceeds_4e8=bool(taylor25 > 400_000_000))
    print('clock lower r* =', float(r_star), flush=True)
    assert r_star > F(49999, 50000)

    # 2. sharp joint constant for the published source ----------------------
    fx = coordinate_value(65, 121, 316)
    fy = coordinate_value(8, 30, 94)
    phi = fx * fy
    joint = r_star * phi
    res['published_sharp'] = dict(
        partition=str(phi), partition_display=float(phi),
        joint=str(joint), joint_display=float(joint),
        headline='9997/10000', ten_cycle=float(F(9997, 10000) ** 10),
        old_headline='1999/2000', old_joint_display=float(F(49999, 50000) * F(99957, 100000)))
    print('published sharp joint =', float(joint), flush=True)
    assert joint > F(9997, 10000)
    assert F(9997, 10000) ** 10 > F(997, 1000)

    # 3. biased allocation tolerance ----------------------------------------
    def critical_theta(w, target: F, grid):
        rows = []
        for th in grid:
            v = joint_theta(w, th)
            rows.append(dict(theta=str(th), partition=str(v),
                             partition_display=float(v), ok=bool(v > target)))
        return rows

    grid = [F(1, 2), F(49, 100), F(12, 25), F(47, 100), F(23, 50), F(9, 20), F(11, 25)]
    res['published_bias'] = critical_theta(PUB, F(9996, 10000), grid)
    for row in res['published_bias']:
        print('published theta', row['theta'], row['partition_display'], row['ok'], flush=True)

    # 4. exact frontier witnesses, molecularity and rate spread -------------
    wits = {}
    for tag, rho, lymin in [('target_1999_2000_ly1', F(1999, 2000), 1),
                            ('target_1999_2000_ly8', F(1999, 2000), 8),
                            ('target_999_1000_ly1', F(999, 1000), 1)]:
        w = frontier(rho, q=4, ly_min=lymin)
        w = {k: (str(v) if isinstance(v, F) else v) for k, v in w.items()}
        w['molecularity'] = w['lx'] + w['ly'] + w['gx'] + w['gy'] + w['q'] + 1
        w['core'] = w['N']
        w['initial_supply'] = w['N'] + 1
        wits[tag] = w
        print(tag, 'N =', w['N'], 'molecularity =', w['molecularity'], flush=True)
    res['frontier_witnesses'] = wits

    res['spread_published'] = spread(PUB, 414, log10_k(65, 8, 155))
    w0 = wits['target_1999_2000_ly1']
    res['spread_frontier'] = spread(w0, w0['core'],
                                    log10_k(w0['lx'], w0['ly'],
                                            w0['gx'] + w0['gy'] + w0['q']))
    print('published span 10^%.2f ; frontier span 10^%.2f'
          % (res['spread_published']['span_log10'], res['spread_frontier']['span_log10']),
          flush=True)

    # 5. reliability scaling of the frontier --------------------------------
    scal = []
    for dexp in range(2, 8):
        rho = 1 - F(1, 10 ** dexp)
        w = frontier(rho, q=4, ly_min=1)
        import math as _m
        scal.append(dict(delta=f'1e-{dexp}', N=w['N'], L=round(_m.log(10 ** dexp), 4),
                         ratio=round(w['N'] / _m.log(10 ** dexp), 3),
                         corridors='X[%d,%d]+%d Y[%d,%d]+%d'
                                   % (w['lx'], w['ux'], w['gx'], w['ly'], w['uy'], w['gy'])))
        print('scaling', scal[-1], flush=True)
    res['scaling'] = scal

    res['seconds'] = round(time.monotonic() - t0, 2)
    OUT.mkdir(exist_ok=True)
    (OUT / 'proportion_extras.json').write_text(json.dumps(res, indent=2))


if __name__ == '__main__':
    main()
