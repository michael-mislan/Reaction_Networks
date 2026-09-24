"""Why the certificate is non-monotone in the product-release rate.

Channels 3 (C -> S+F, rate kappa_d c) and 4 (C -> S+P, rate kappa_r c) leave the
complex at the same speed but dispose of the food-derived moiety differently:
channel 3 returns it to the food pool, channel 4 exports it as product.  Food is
the substrate of the replication channel S+F -> 2S, which is the only way the
carrier count R = n+c grows, and the partition payoff 1-2^{1-R} is governed by R.

This script solves the backward equations in floating point (diagnostic evidence
only; no certificate depends on it) and reports, for several (kappa_d, kappa_r):

  * the exact disjoint failure decomposition
        1 - p_z = P_z(p_T < q) + E_z[1{p_T>=q} 2^{1-R_T}] ,
  * terminal means of the carrier count R, the food stock and the product stock.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix, identity
from scipy.stats import poisson

OUT = Path(__file__).resolve().parent.parent / 'data'
INCR = [(1, 0, 0), (-1, 0, 0), (-1, 1, 0), (1, -1, 0), (1, -1, 1), (-1, 1, -1)]


def generator(K, kd, kr):
    states = [(n, c, p) for c in range(K // 2 + 1) for n in range(K - 2 * c + 1)
              if n + c >= 1 for p in range(K - n - 2 * c + 1)]
    ix = {z: i for i, z in enumerate(states)}
    rows, cols, vals = [], [], []
    for i, (n, c, p) in enumerate(states):
        f = K - n - 2 * c - p
        rate = [n * f, n * (n - 1) / 100.0, 2.0 * n * f, kd * c, kr * c, n * p / 50.0]
        tot = 0.0
        for r, a in enumerate(rate):
            if a > 0:
                j = ix[(n + INCR[r][0], c + INCR[r][1], p + INCR[r][2])]
                rows.append(i); cols.append(j); vals.append(a); tot += a
        rows.append(i); cols.append(i); vals.append(-tot)
    G = coo_matrix((vals, (rows, cols)), shape=(len(states),) * 2).tocsr()
    return states, ix, G


def evolve(G, payoffs, T=5.0):
    """Uniformization in floating point: e^{TG} h = sum_j Pois(lam T; j) P^j h."""
    lam = float(abs(G.diagonal()).max()) * 1.000001
    P = identity(G.shape[0], format='csr') + G / lam
    mu = lam * T
    hi = int(mu + 10.0 * np.sqrt(mu) + 50)
    w = poisson.pmf(np.arange(hi + 1), mu)
    Y = np.array(payoffs, dtype=float).T
    acc = w[0] * Y
    for j in range(1, hi + 1):
        Y = P.dot(Y)
        acc += w[j] * Y
    assert abs(w.sum() - 1.0) < 1e-10, w.sum()
    return acc.T


def run(K=32, T=5.0, q=4):
    rows = []
    states, ix, _ = generator(K, 10, 10)
    quota = np.array([1.0 if p >= q else 0.0 for _, _, p in states])
    split = np.array([1.0 - 2.0 ** (1 - (n + c)) if p >= q else 0.0 for n, c, p in states])
    Rf = np.array([float(n + c) for n, c, _ in states])
    Ff = np.array([float(K - n - 2 * c - p) for n, c, p in states])
    Pf = np.array([float(p) for _, _, p in states])
    for kd, kr in [(10, 10), (20, 10), (10, 20), (20, 20), (40, 40)]:
        st, ixx, G = generator(K, kd, kr)
        assert st == states
        out = evolve(G, [quota, split, Rf, Ff, Pf], T)
        for start in [(K - 1, 0, 0), (1, 0, 0), (0, 1, 0)]:
            i = ix[start]
            rows.append(dict(kappa_d=kd, kappa_r=kr, start=list(start),
                             quota_met=out[0, i], success=out[1, i],
                             quota_failure=1 - out[0, i],
                             partition_failure=out[0, i] - out[1, i],
                             mean_R=out[2, i], mean_food=out[3, i], mean_product=out[4, i]))
            print('kd=%2d kr=%2d start=%-10s success=%.9f  quota_fail=%.3e '
                  'part_fail=%.3e  E[R]=%.4f E[F]=%.4f E[P]=%.4f'
                  % (kd, kr, str(start), rows[-1]['success'], rows[-1]['quota_failure'],
                     rows[-1]['partition_failure'], rows[-1]['mean_R'],
                     rows[-1]['mean_food'], rows[-1]['mean_product']), flush=True)
    OUT.mkdir(exist_ok=True)
    (OUT / 'branching_mechanism.json').write_text(json.dumps(
        dict(K=K, T=T, quota=q, evidence='floating-point diagnostic (N); no certificate uses it',
             rows=rows), indent=2))


if __name__ == '__main__':
    run()
