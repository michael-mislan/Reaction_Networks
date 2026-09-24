"""Exact one-sided integer certificates for the elementary support-memory source.

The source, on a selected face, has counts (n, c, p) and food f = K-n-2c-p.
Six channels, with combinatorial factors g_r(z) and rate constants k_r:

    0  S+F -> 2S      (+1, 0, 0)   g = n f        k0 = 1
    1  2S  -> S+F     (-1, 0, 0)   g = n(n-1)     k1 = 1/100
    2  S+F -> C       (-1,+1, 0)   g = n f        k2 = 2
    3  C   -> S+F     (+1,-1, 0)   g = c          k3 = kappa
    4  C   -> S+P     (+1,-1,+1)   g = c          k4 = kappa
    5  S+P -> C       (-1,+1,-1)   g = n p        k5 = 1/50

A *parameter family* is a list of groups.  Each group is a set of channels
driven by one shared parameter ranging over a rational interval [lo, hi]; the
constant of channel r in the group is  mult_r * parameter.  The generator is
jointly affine in the group parameters, so the family is the convex hull of
its vertex generators, and the rowwise minimum of the one-step kernel over the
whole box is attained groupwise at an endpoint:

    min_k (P_k v)(z) = v(z) + (1/lam) sum_groups  min(lo*s_g, hi*s_g),
    s_g(z) = sum_{r in g} mult_r g_r(z) [v(z+nu_r) - v(z)].

All arithmetic below is integer arithmetic with downward rounding, so every
intermediate vector is a lower bound (after division by SCALE) on the true
finite-time payoff of EVERY fixed generator in the family.  An upper bound on
a payoff h is obtained from a lower bound on 1-h, because the full stochastic
semigroup preserves constants.

No floating-point operation enters a certificate.
"""
from __future__ import annotations

import math
import time
from fractions import Fraction as F

import numpy as np

SCALE = 2 ** 31
INCR = [(1, 0, 0), (-1, 0, 0), (-1, 1, 0), (1, -1, 0), (1, -1, 1), (-1, 1, -1)]


def states_of(K):
    return [(n, c, p) for c in range(K // 2 + 1) for n in range(K - 2 * c + 1)
            if n + c >= 1 for p in range(K - n - 2 * c + 1)]


def factor(r, n, c, p, f):
    return (n * f, n * (n - 1), n * f, c, c, n * p)[r]


def nominal_groups(kappa_lo=10, kappa_hi=10, tied=True, eps=F(0)):
    """Parameter family.  eps is a relative half-width applied to the four
    kappa-free constants (and multiplicatively to the kappa band ends)."""
    lo, hi = 1 - eps, 1 + eps
    base = [([0], [F(1)], F(1) * lo, F(1) * hi),
            ([1], [F(1)], F(1, 100) * lo, F(1, 100) * hi),
            ([2], [F(1)], F(2) * lo, F(2) * hi),
            ([5], [F(1)], F(1, 50) * lo, F(1, 50) * hi)]
    klo, khi = F(kappa_lo) * lo, F(kappa_hi) * hi
    if tied:
        base.append(([3, 4], [F(1), F(1)], klo, khi))
    else:
        base.append(([3], [F(1)], klo, khi))
        base.append(([4], [F(1)], klo, khi))
    return base


def payoff_fair(R):
    return 1 - F(1, 2 ** (R - 1))


def payoff_biased(theta):
    theta = F(theta)
    return lambda R: 1 - theta ** R - (1 - theta) ** R


def certify(K, groups, T=5, quota=4, split=payoff_fair):
    """Return exact lower/upper numerators (denominator SCALE) for
    inf over the family and min over the restart set of the joint payoff."""
    began = time.monotonic()
    states = states_of(K)
    ix = {z: i for i, z in enumerate(states)}
    N = len(states)
    # common denominator of all interval ends times multipliers
    Q = 1
    for chans, mults, lo, hi in groups:
        for m in mults:
            for x in (m * lo, m * hi):
                Q = Q * x.denominator // math.gcd(Q, x.denominator)
    dst = np.zeros((6, N), dtype=np.int64)
    g = np.zeros((6, N), dtype=np.int64)
    for i, (n, c, p) in enumerate(states):
        f = K - n - 2 * c - p
        for r in range(6):
            a = factor(r, n, c, p, f)
            if a:
                z2 = (n + INCR[r][0], c + INCR[r][1], p + INCR[r][2])
                assert z2 in ix, (states[i], r)
                dst[r, i] = ix[z2]
                g[r, i] = a
            else:
                dst[r, i] = i
    # integer group data
    G = []
    exit_hi = np.zeros(N, dtype=object)
    for chans, mults, lo, hi in groups:
        assert 0 < lo <= hi
        ilo, ihi = int(lo * Q), int(hi * Q)
        assert F(ilo, Q) == lo and F(ihi, Q) == hi
        imult = []
        for m in mults:
            assert m.denominator == 1
            imult.append(int(m))
        G.append((chans, imult, ilo, ihi))
        for r, m in zip(chans, imult):
            exit_hi = exit_hi + np.array([int(x) for x in g[r]], dtype=object) * (m * ihi)
    max_exit = max(int(x) for x in exit_hi)            # in units 1/Q
    lam = -(-max_exit // Q)                             # integer clock >= every exit rate
    D = Q * lam
    assert 4 * D * SCALE < 2 ** 63, 'int64 safety'
    e_minus = sum((F((-1) ** j, math.factorial(j)) for j in range(26)), F(0))
    assert 0 < e_minus
    weights = [int(SCALE * e_minus / math.factorial(j)) for j in range(19)]
    assert sum(weights) <= SCALE and SCALE * sum(weights) < 2 ** 63
    last = max(j for j, w in enumerate(weights) if w)
    h = [split(n + c) if p >= quota else F(0) for n, c, p in states]
    assert all(0 <= x <= 1 for x in h)
    v = np.array([[int(SCALE * x), int(SCALE * (1 - x))] for x in h], dtype=np.int64)
    assert 0 <= v.min() and v.max() <= SCALE

    # Sparse integer operators: A0 collects D*I and every degenerate group;
    # each nondegenerate group g has B_g with (B_g u)(z) = s_g(z).
    from scipy.sparse import coo_matrix, identity

    def diff_operator(chans, imult):
        rows, cols, vals = [], [], []
        for r, m in zip(chans, imult):
            nz = np.nonzero(g[r])[0]
            rows += [nz, nz]
            cols += [dst[r, nz], nz]
            vals += [m * g[r, nz], -m * g[r, nz]]
        return coo_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))),
                          shape=(N, N), dtype=np.int64).tocsr()

    A0 = (D * identity(N, dtype=np.int64, format='csr'))
    moving = []
    for chans, imult, ilo, ihi in G:
        B = diff_operator(chans, imult)
        if ilo == ihi:
            A0 = A0 + ilo * B
        else:
            moving.append((B, ilo, ihi))
    A0 = A0.tocsr()

    def lower_step(u):
        out = A0.dot(u)
        for B, ilo, ihi in moving:
            s = B.dot(u)
            out += np.where(s >= 0, ilo * s, ihi * s)
        assert out.min() >= 0
        return out // D

    blocks = lam * T
    assert isinstance(blocks, int)
    for _ in range(blocks):
        term = v
        acc = weights[0] * term
        for j in range(1, last + 1):
            term = lower_step(term)
            acc += weights[j] * term
        v = acc // SCALE
    assert 0 <= v.min() and v.max() <= SCALE
    starts = [i for i, (n, c, p) in enumerate(states) if p == 0 and 1 <= n + c <= K - 1]
    lo_i = min(starts, key=lambda i: int(v[i, 0]))
    up_i = max(starts, key=lambda i: int(v[i, 1]))
    return dict(K=K, T=T, quota=quota, states=N, starts=len(starts), clock=lam, Q=Q,
                blocks=blocks, last_weight=last, denominator=SCALE,
                lower=int(v[lo_i, 0]), lower_state=list(states[lo_i]),
                upper=SCALE - int(v[up_i, 1]), upper_state=list(states[up_i]),
                lower_by_start={str(states[i]): int(v[i, 0]) for i in starts
                                if states[i] in ((K - 1, 0, 0), (1, 0, 0), (0, 1, 0))},
                seconds=round(time.monotonic() - began, 2))


if __name__ == '__main__':
    r = certify(32, nominal_groups(10, 20))
    print(r)
    assert r['lower'] == 2145514420 and r['states'] == 3384 and r['clock'] == 771
