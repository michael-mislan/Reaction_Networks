"""Shared floating-point model builder for the reader-writer source.

States (a, r) with a + r <= N.  Returns the molecular generator Q, the
daughter marginal D1, and the complementary pair law as index arrays
(parent, daughter1, daughter2, probability).  Diagnostics only: every
certified number in the paper comes from the exact rational scripts.
Dense matrices for N <= 32, scipy CSR above that.
"""
import os
for _k in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_k, "1")
import numpy as np
from scipy.stats import binom
from scipy.sparse import coo_matrix


def source(N, e=.01, w=.01, k=1., h=.5, dense=None):
    states = [(a, r) for a in range(N + 1) for r in range(N + 1 - a)]
    ix = {x: i for i, x in enumerate(states)}
    n = len(states)
    lut = -np.ones((N + 1, N + 1), dtype=np.int64)
    for (a, r), i in ix.items():
        lut[a, r] = i
    qi, qj, qv = [], [], []
    ii, jj, kk, pp = [], [], [], []
    for i, (a, r) in enumerate(states):
        u = N - a - r; tot = 0.
        for dest, rate in (((a + 1, r), u * (w + k * a / N)), ((a, r + 1), u * (w + k * r / N)),
                           ((a - 1, r), a * (e + h * r / N)), ((a, r - 1), r * (e + h * a / N))):
            if rate:
                qi.append(i); qj.append(ix[dest]); qv.append(rate); tot += rate
        qi.append(i); qj.append(i); qv.append(-tot)
        x = np.arange(a + 1)[:, None]; y = np.arange(r + 1)[None, :]
        p = binom.pmf(x, a, .5) * binom.pmf(y, r, .5)
        ii.append(np.full(p.size, i)); jj.append(lut[x, y].ravel())
        kk.append(np.broadcast_to(lut[a - x, r - y], p.shape).ravel()); pp.append(p.ravel())
    ii, jj, kk, pp = map(np.concatenate, (ii, jj, kk, pp))
    Q = coo_matrix((qv, (qi, qj)), shape=(n, n)).tocsr()
    D = coo_matrix((pp, (ii, jj)), shape=(n, n)).tocsr()
    if dense is None:
        dense = N <= 32
    if dense:
        Q, D = Q.toarray(), D.toarray()
        assert np.max(np.abs(Q.sum(1))) < 1e-12 and np.max(np.abs(D.sum(1) - 1)) < 1e-12
    return states, ix, Q, D, (ii, jj, kk, pp)


def pair(pairs, f, g, n):
    ii, jj, kk, pp = pairs
    return np.bincount(ii, weights=pp * f[jj] * g[kk], minlength=n)


def step_hazard(states):
    return np.array([.01 if a > r else .3 for a, r in states])


def smooth_hazard(states, N, s=8.):
    return np.array([.01 + .29 / (1 + np.exp(s * (a - r) / N)) for a, r in states])


def extinction(Q, D, pairs, d, b, tol=2e-14, itmax=200000):
    """Least fixed points (joint, independent); dense Q, D; b may be a vector."""
    n = len(d)
    b = np.full(n, b) if np.isscalar(b) else np.asarray(b, float)
    R = np.linalg.inv(np.diag(b + d) - Q)
    Rd, T = R @ d, R * b[None, :]
    out = []
    for ind in (False, True):
        z = np.zeros(n)
        for _ in range(itmax):
            zn = Rd + T @ ((D @ z) ** 2 if ind else pair(pairs, z, z, n))
            if np.max(np.abs(zn - z)) < tol:
                break
            z = zn
        else:
            raise RuntimeError("iteration budget")
        out.append(zn)
    return out
