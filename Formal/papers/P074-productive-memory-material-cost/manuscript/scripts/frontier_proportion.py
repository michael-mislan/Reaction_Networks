"""Exact material frontier for cooperative-gate proportion memory.

Architecture class G(q) -- one reversible cooperative pair per program,

    l_X X + l_Y Y + (g_X+g_Y+q) F + H  <->  (l_X+g_X) X + (l_Y+g_Y) Y + q P_X + W

and its X/Y mirror, with newborn corridors  X in [l_X,u_X],  Y in [l_Y,u_Y],
l_X > u_Y (so the mirror reaction is disabled and the ratio decoder is exact),
conserved core  N = x+y+f+p_X+p_Y,  one fuel token, deadline T, harvest of all
product, one complementary fair allocation of every intact molecule, and refill
of both daughters to core N.  No post-division repair or daughter selection.

Two facts make the frontier exactly computable.

(i)  Closure.  At a newborn only the selected forward channel is enabled; after
     it fires H is gone and only its own reverse is enabled.  The reachable
     class is the two-state pair, so the terminal law is exact and the clock
     factor r(a,d) = a/(a+d) (1-e^{-(a+d)}) can be pushed to 1 by the choice of
     the (free, positive, rational) rate constants.  Hence the frontier is set
     by the partition stage alone.

(ii) Endpoint reduction.  psi(n;l,u) = P(l <= I <= u, l <= n-I <= u), I~Bin(n,1/2),
     is nondecreasing for n <= l+u and nonincreasing for n >= l+u, so its minimum
     over the parent range [l+g, u+g] is at an endpoint, and

         psi(l+g;l,u) = Psi(l+g, g-l),     psi(u+g;l,u) = Psi(c, u-g),  c = u+g,

     where Psi(n,w) = P(|Bin(n,1/2) - n/2| <= w/2).  Both are central.  A
     positive uniform bound forces l <= g <= u.

Minimal core mass is  N = c_X + c_Y + q  with  c = u+g  per coordinate, because
the worst newborn must still hold g_X+g_Y+q food units.

The search below is exact (Fraction arithmetic) and exhaustive: for each
admissible minority corridor it scans majority cost upward from zero and stops
at the first success, and it stops enumerating minority cost once that cost
alone exceeds the incumbent total.
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / 'data'

_PREFIX: dict[int, list[int]] = {}


def prefix(n: int) -> list[int]:
    """prefix(n)[k] = sum_{i<k} C(n,i)."""
    p = _PREFIX.get(n)
    if p is None:
        s, c = [0], 1
        for i in range(n + 1):
            s.append(s[-1] + c)
            c = c * (n - i) // (i + 1)
        _PREFIX[n] = p = s
    return p


@lru_cache(maxsize=None)
def Psi(n: int, w: int) -> F:
    """P(|Bin(n,1/2) - n/2| <= w/2), exact."""
    if w < 0:
        return F(0)
    lo = max(0, -(-(n - w) // 2))          # ceil((n-w)/2)
    hi = min(n, (n + w) // 2)
    if lo > hi:
        return F(0)
    p = prefix(n)
    return F(p[hi + 1] - p[lo], 1 << n)


def coordinate_value(l: int, g: int, c: int) -> F:
    """Uniform two-daughter return probability for one coordinate."""
    u = c - g
    if not (1 <= l <= g <= u):
        return F(0)
    return min(Psi(l + g, g - l), Psi(c, u - g))


@lru_cache(maxsize=None)
def best_major(c: int, l: int) -> tuple[F, int]:
    """max over g of coordinate_value(l,g,c); the min of an increasing and a
    decreasing function of g, so a plain scan is used (ranges are short)."""
    best, arg = F(0), -1
    for g in range(l, c // 2 + 1):
        v = coordinate_value(l, g, c)
        if v > best:
            best, arg = v, g
    return best, arg


def frontier(rho: F, q: int = 4, ly_min: int = 1, cap: int = 4000):
    """Exact minimum core mass N = c_X + c_Y + q over the class."""
    began = time.monotonic()
    best_total, best_wit = None, None
    cy = 2 * ly_min
    while True:
        if best_total is not None and cy + q >= best_total:
            break
        if cy > cap:
            raise RuntimeError('cap reached')
        for gy in range(ly_min, cy // 2 + 1):
            fy = coordinate_value(ly_min, gy, cy)
            if fy <= rho:                      # F_X <= 1 forces F_Y > rho
                continue
            uy = cy - gy
            need = rho / fy
            limit = cap if best_total is None else best_total - cy - q
            for cx in range(2 * (uy + 1), limit):
                fx, gx = best_major(cx, uy + 1)
                if fx >= need:
                    total = cx + cy + q
                    if best_total is None or total < best_total:
                        best_total = total
                        best_wit = dict(N=total, cx=cx, cy=cy, gx=gx, gy=gy,
                                        lx=uy + 1, ux=cx - gx, ly=ly_min, uy=uy,
                                        q=q, FX=fx, FY=fy, joint=fx * fy)
                    break
        cy += 1
    w = dict(best_wit)
    w['FX'] = str(w['FX'])
    w['FY'] = str(w['FY'])
    w['joint_display'] = float(w['joint'])
    w['joint'] = str(w['joint'])
    w['rho'] = str(rho)
    w['ly_min'] = ly_min
    w['seconds'] = round(time.monotonic() - began, 2)
    return w


def verify_endpoint_lemma(cases):
    """Direct check that the parent-range minimum sits at an endpoint."""
    bad = 0
    for (l, u, g) in cases:
        vals = []
        for n in range(l + g, u + g + 1):
            lo, hi = max(l, n - u), min(u, n - l)
            p = prefix(n)
            vals.append(F(p[hi + 1] - p[lo], 1 << n) if lo <= hi else F(0))
        if min(vals) != min(vals[0], vals[-1]):
            bad += 1
        assert vals[0] == Psi(l + g, g - l), (l, u, g)
        assert vals[-1] == Psi(u + g, u - g), (l, u, g)
    return bad


def main():
    res = {}

    # 0. endpoint lemma, direct verification on a grid ----------------------
    cases = [(l, u, g) for l in range(1, 14) for u in range(l, 60, 3)
             for g in range(l, u + 1, 2)]
    res['endpoint_lemma'] = dict(cases=len(cases), violations=verify_endpoint_lemma(cases))
    print('endpoint lemma: %d cases, %d violations' % (len(cases), res['endpoint_lemma']['violations']),
          flush=True)

    # 1. the published 415-unit construction -------------------------------
    fx = coordinate_value(65, 121, 316)
    fy = coordinate_value(8, 30, 94)
    res['published_point'] = dict(
        lx=65, ux=195, gx=121, ly=8, uy=64, gy=30, q=4, core=316 + 94 + 4,
        FX=str(fx), FY=str(fy), joint=str(fx * fy), joint_display=float(fx * fy),
        psi_selected_low=str(Psi(186, 121 - 65)), psi_selected_high=str(Psi(316, 195 - 121)),
        psi_minority_low=str(Psi(38, 30 - 8)), psi_minority_high=str(Psi(94, 64 - 30)))
    print('published 415 point: joint partition =', float(fx * fy), flush=True)
    assert 316 + 94 + 4 == 414

    # 2. exact frontiers ----------------------------------------------------
    rows = []
    for rho_s, ly_min in [('1999/2000', 1), ('1999/2000', 8), ('999/1000', 1),
                          ('999/1000', 8), ('9999/10000', 1), ('99999/100000', 1)]:
        w = frontier(F(rho_s), q=4, ly_min=ly_min)
        rows.append(w)
        print('frontier rho=%-14s ly_min=%d  ->  core N = %d  (%s)  %.2fs'
              % (rho_s, ly_min, w['N'],
                 'X[%d,%d]+%d  Y[%d,%d]+%d' % (w['lx'], w['ux'], w['gx'],
                                               w['ly'], w['uy'], w['gy']),
                 w['seconds']), flush=True)
    res['frontiers'] = rows

    OUT.mkdir(exist_ok=True)
    (OUT / 'frontier_proportion.json').write_text(json.dumps(res, indent=2))


if __name__ == '__main__':
    sys.exit(main())
