"""Hill-climb for an extinction reversal with monotone b (up) and d (down)."""
import numpy as np, json, sys
from model import source, extinction

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)

def build(N, theta, states):
    nb = N + 1
    binc = np.cumsum(np.exp(theta[:nb]))            # b as increasing function of a
    dinc = np.cumsum(np.exp(theta[nb:2 * nb]))[::-1]  # d decreasing in a
    b = np.array([binc[a] for a, r in states]); d = np.array([dinc[a] for a, r in states])
    return b, d

def score(N, theta, cache):
    states, ix, Q0, D, pairs = cache
    e, w, k, h = np.exp(theta[-4:])
    states, ix, Q, D, pairs = source(N, e, w, k, h) if theta[-1] > -50 else cache
    b, d = build(N, theta, states)
    try:
        qj, qi = extinction(Q, D, pairs, d, b, tol=1e-13, itmax=5000)
    except RuntimeError:
        return -1, None
    return float(np.max(qj - qi)), (b, d, qj, qi)

for N in (3, 4, 5):
    cache = source(N, 0, 0, 0, 0)
    bestall = -1
    for restart in range(6):
        theta = np.concatenate([rng.normal(-1, 2, 2 * (N + 1)), rng.normal(-4, 2, 4)])
        val, _ = score(N, theta, cache)
        step = 1.0
        for it in range(400):
            cand = theta + step * rng.normal(0, 1, theta.size) * (rng.random(theta.size) < .3)
            v, info = score(N, cand, cache)
            if v > val:
                val, theta, keep = v, cand, info
            elif it % 50 == 49:
                step *= .7
        print(N, restart, val, flush=True)
        if val > bestall:
            bestall, btheta, binfo = val, theta, keep
    print("BEST", N, bestall, np.exp(btheta[-4:]))
    if bestall > 1e-6:
        b, d, qj, qi = binfo
        print(json.dumps(dict(b=b.tolist(), d=d.tolist(), qj=qj.tolist(), qi=qi.tolist())))
