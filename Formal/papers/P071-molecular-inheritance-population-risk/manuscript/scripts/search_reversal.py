"""Diagnostic search: can state-dependent division reverse the extinction order?

d is nonincreasing and b nondecreasing in the state order (better cells
divide faster and die more slowly).  We look for q_J(x) > q_I(x).
"""
import numpy as np, itertools, json
from model import source, extinction

rng = np.random.default_rng(7)
best = (0, None)
for N in (2, 3, 4):
    for trial in range(400):
        e = 10 ** rng.uniform(-3, 0); w = 10 ** rng.uniform(-3, 0)
        k = 10 ** rng.uniform(-2, 1); h = 10 ** rng.uniform(-2, 1)
        if trial % 4 == 0:
            e = w = k = h = 0.0
        states, ix, Q, D, pairs = source(N, e, w, k, h)
        # monotone b (up) and d (down) as functions of a only / of a-r
        kind = rng.integers(2)
        key = (lambda s: s[0]) if kind == 0 else (lambda s: s[0] - s[1])
        levels = sorted({key(s) for s in states})
        binc = np.cumsum(10 ** rng.uniform(-2, 1, len(levels)))
        dinc = np.cumsum(10 ** rng.uniform(-2, 0.5, len(levels)))[::-1]
        if rng.integers(2):
            dinc = np.full(len(levels), dinc.mean())
        b = np.array([binc[levels.index(key(s))] for s in states])
        d = np.array([dinc[levels.index(key(s))] for s in states])
        try:
            qj, qi = extinction(Q, D, pairs, d, b, tol=1e-13, itmax=20000)
        except RuntimeError:
            continue
        rev = float(np.max(qj - qi))
        if rev > best[0]:
            best = (rev, dict(N=N, e=e, w=w, k=k, h=h, kind=int(kind), b=b.tolist(), d=d.tolist(),
                              state=states[int(np.argmax(qj - qi))], qj=qj.tolist(), qi=qi.tolist()))
            print(N, trial, rev, flush=True)
print(json.dumps(best, indent=1))
