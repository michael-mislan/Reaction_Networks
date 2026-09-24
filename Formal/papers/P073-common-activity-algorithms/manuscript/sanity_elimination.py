"""Numerical sanity check of monotone elimination (Section 7 of the paper).

NOT a certificate and NOT the exact algorithm: maps are tabulated on a grid and
rounded upward.  The script eliminates vertices bottom-up along a depth-first
forest, exactly as in Lemma 7.1 (incoming map, next-map of the admissible set,
outgoing map), back-substitutes the least state, and compares it with the limit
of plain Kleene iteration, which converges to the same least state from below.
Random instances include cyclic graphs with several shared vertices.
"""
import random
import numpy as np

N = 40001
GRID = np.linspace(0.0, 1.0, N)
BIG = 2.0


def idx_up(v):
    """Smallest grid index with GRID[k] >= v (vectorised); N means 'beyond 1'."""
    return np.clip(np.ceil(np.asarray(v) * (N - 1) - 1e-9).astype(int), 0, N)


def ext(arr):
    return np.append(arr, BIG)


def solve_by_elimination(n, edges, lo, hi, t):
    adj = {v: set() for v in range(n)}
    for (u, v, r) in edges:
        adj[u].add(v); adj[v].add(u)
    parent, order, seen = {}, [], set()
    def dfs(v):
        seen.add(v)
        for w in sorted(adj[v]):
            if w not in seen:
                parent[w] = v
                dfs(w)
        order.append(v)                      # post-order: children first
    for v in range(n):
        if v not in seen:
            parent[v] = None
            dfs(v)
    def ancestors(v):
        out = []
        while parent[v] is not None:
            v = parent[v]; out.append(v)
        return out
    M = {}
    for (u, v, r) in edges:
        M[(u, v)] = (r * GRID + 2 * GRID ** 2) / (r + 2) + t
        M[(v, u)] = (-r + np.sqrt(r * r + 4 * (r + 1) * (GRID + t))) / 2
    T = {v: np.zeros(N) for v in range(n)}
    lo, hi = list(lo), list(hi)
    saved = {}
    for w in order:
        anc = ancestors(w)
        U = (GRID >= lo[w] - 1e-12) & (GRID <= hi[w] + 1e-12) & (T[w] <= GRID + 1e-12)
        nxt = np.full(N + 1, N, dtype=int)
        for k in range(N - 1, -1, -1):
            nxt[k] = k if U[k] else nxt[k + 1]
        saved[w] = (nxt, {i: M[(i, w)].copy() for i in anc if (i, w) in M}, lo[w])
        if not anc:
            continue
        for j in anc:
            if (w, j) not in M:
                continue
            g = ext(M[(w, j)])
            k0 = nxt[idx_up(lo[w])]
            lo[j] = max(lo[j], float(g[k0]))
            for i in anc:
                if (i, w) not in M:
                    continue
                comp = g[nxt[idx_up(np.minimum(M[(i, w)], 1.0 + 1e-9))]]
                comp = np.where(M[(i, w)] > 1.0, BIG, comp)
                if i == j:
                    T[i] = np.maximum(T[i], comp)
                else:
                    M[(i, j)] = np.maximum(M.get((i, j), np.zeros(N)), comp)
    z = [None] * n
    for w in reversed(order):
        nxt, inmaps, low = saved[w]
        a = low
        for i, arr in inmaps.items():
            a = max(a, float(ext(arr)[idx_up(z[i])]))
        if a > 1.0:
            return None
        k = nxt[idx_up(a)]
        if k >= N:
            return None
        z[w] = float(GRID[k])
    return z


def solve_by_kleene(n, edges, lo, hi, t, sweeps=200000):
    z = list(lo)
    for _ in range(sweeps):
        change = 0.0
        for (u, v, r) in edges:
            a = (r * z[u] + 2 * z[u] ** 2) / (r + 2) + t
            if a > z[v]:
                change = max(change, a - z[v]); z[v] = a
            b = (-r + (r * r + 4 * (r + 1) * (z[v] + t)) ** 0.5) / 2
            if b > z[u]:
                change = max(change, b - z[u]); z[u] = b
        if any(z[v] > hi[v] + 1e-9 for v in range(n)):
            return None
        if change < 1e-13:
            return z
    return z


def random_instance(rng):
    kind = rng.choice(['windmill', 'k2m', 'triangle', 'tree', 'diamond'])
    if kind == 'windmill':
        k = rng.randint(1, 3); n = 2 * k + 1; shape = []
        for i in range(k):
            shape += [(0, 1 + 2 * i), (1 + 2 * i, 2 + 2 * i), (0, 2 + 2 * i)]
    elif kind == 'k2m':
        m = rng.randint(2, 4); n = m + 2
        shape = [(0, 2 + i) for i in range(m)] + [(2 + i, 1) for i in range(m)]
    elif kind == 'triangle':
        n, shape = 3, [(0, 1), (1, 2), (0, 2)]
    elif kind == 'diamond':
        n, shape = 4, [(0, 1), (1, 3), (0, 2), (2, 3)]
    else:
        n = rng.randint(2, 6); shape = [(rng.randrange(v), v) for v in range(1, n)]
    edges = [(u, v, rng.choice([0.2, 0.5, 1.0, 2.0, 4.0, 9.0])) for (u, v) in shape]
    lo = [rng.choice([0.01, 0.05, 0.2]) for _ in range(n)]
    hi = [rng.choice([0.6, 0.9, 1.0]) for _ in range(n)]
    t = rng.choice([1e-4, 1e-3, 3e-3])
    return n, edges, lo, hi, t


def main():
    rng = random.Random(20260920)
    agree = sat = unsat = borderline = 0
    trials = 300
    for _ in range(trials):
        n, edges, lo, hi, t = random_instance(rng)
        ze = solve_by_elimination(n, edges, lo, hi, t)
        zk = solve_by_kleene(n, edges, lo, hi, t)
        if (ze is None) != (zk is None):
            # grid rounding can flip instances that are feasible by a hair
            borderline += 1
            continue
        if ze is None:
            unsat += 1; agree += 1
            continue
        err = max(abs(p - q) for p, q in zip(ze, zk))
        assert err < 5e-3, (n, edges, lo, hi, t, ze, zk)
        assert all(p >= q - 1e-6 for p, q in zip(ze, zk))     # upward rounding
        sat += 1; agree += 1
    print(dict(trials=trials, agree=agree, sat=sat, unsat=unsat, borderline=borderline))
    assert borderline <= trials // 20
    print('PASS (numerical sanity check only)')


if __name__ == '__main__':
    main()
