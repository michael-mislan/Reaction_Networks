"""General-N exact reconstruction of the inherited-mark branching source."""
from fractions import Fraction as F
from math import comb


def states_of(N):
    return [(a, r) for a in range(N + 1) for r in range(N - a + 1)]


def chem_generator(N, e):
    """Conservative generator Q_e (row = source state)."""
    st = states_of(N)
    idx = {s: i for i, s in enumerate(st)}
    n = len(st)
    Q = [[F(0)] * n for _ in range(n)]
    for i, (a, r) in enumerate(st):
        s = N - a - r
        ch = [((a + 1, r), s * (F(1, 100) + F(a, N))),
              ((a, r + 1), s * (F(1, 100) + F(r, N))),
              ((a - 1, r), a * (e + F(r, 2 * N))),
              ((a, r - 1), r * (e + F(a, 2 * N)))]
        for tgt, rate in ch:
            if rate:
                assert rate > 0 and tgt in idx, (tgt, rate)
                Q[i][idx[tgt]] += rate
                Q[i][i] -= rate
    return st, idx, Q


def daughter_marginal(N):
    """L[i][j] = P(one ordered daughter of a type-i mother has type j)."""
    st = states_of(N)
    idx = {s: i for i, s in enumerate(st)}
    n = len(st)
    L = [[F(0)] * n for _ in range(n)]
    for i, (a, r) in enumerate(st):
        for aa in range(a + 1):
            for rr in range(r + 1):
                L[i][idx[(aa, rr)]] += F(comb(a, aa) * comb(r, rr), 2 ** (a + r))
    return L


def pair_law(N):
    """pairs[i] = list of (j, k, prob) for the ordered daughter pair."""
    st = states_of(N)
    idx = {s: i for i, s in enumerate(st)}
    out = []
    for (a, r) in st:
        terms = {}
        for aa in range(a + 1):
            for rr in range(r + 1):
                p = F(comb(a, aa) * comb(r, rr), 2 ** (a + r))
                key = (idx[(aa, rr)], idx[(a - aa, r - rr)])
                terms[key] = terms.get(key, F(0)) + p
        out.append([(j, k, p) for (j, k), p in sorted(terms.items())])
    return out


def death_vector(N, prot=F(1, 100), unprot=F(3, 10)):
    return [prot if a > r else unprot for (a, r) in states_of(N)]


def mean_matrix(N, e, b=F(1, 10), bP=None, kappa=F(0)):
    """A = Q_e + diag(b)(2L - I) - diag(d + kappa*1_{protected}).

    bP overrides the division rate on protected states (a > r).
    kappa is an additional death rate applied on protected states.
    """
    st, idx, Q = chem_generator(N, e)
    L = daughter_marginal(N)
    d = death_vector(N)
    n = len(st)
    A = [row[:] for row in Q]
    for i, (a, r) in enumerate(st):
        bi = bP if (bP is not None and a > r) else b
        for j in range(n):
            A[i][j] += bi * 2 * L[i][j]
        A[i][i] -= bi
        A[i][i] -= d[i]
        if a > r:
            A[i][i] -= kappa
    return st, A


def phi(N, e, x, b=F(1, 10), bP=None, kappa=F(0)):
    """Phi(x) = Q_e x + (d+kappa) o (1-x) + b o (D(x,x) - x)."""
    st, idx, Q = chem_generator(N, e)
    pairs = pair_law(N)
    d = death_vector(N)
    n = len(st)
    out = []
    for i in range(n):
        a, r = st[i]
        bi = bP if (bP is not None and a > r) else b
        di = d[i] + (kappa if a > r else F(0))
        qx = sum(Q[i][j] * x[j] for j in range(n))
        dx = sum(p * x[j] * x[k] for j, k, p in pairs[i])
        out.append(qx + di * (1 - x[i]) + bi * (dx - x[i]))
    return out


def mv(M, w):
    return [sum(a * y for a, y in zip(row, w)) for row in M]


def leading_minors_positive(M):
    """Exact fraction-free-ish Gaussian elimination; returns True iff all
    leading principal minors of M are strictly positive."""
    n = len(M)
    A = [row[:] for row in M]
    det = F(1)
    for i in range(n):
        if A[i][i] == 0:
            return False
        det *= A[i][i]
        if det <= 0:
            return False
        piv = A[i][i]
        for k in range(i + 1, n):
            if A[k][i]:
                f = A[k][i] / piv
                for j in range(i, n):
                    A[k][j] -= f * A[i][j]
    return True


def subcritical(N, e, **kw):
    """Exact test s(A) < 0 via the nonsingular-M-matrix criterion on -A."""
    _, A = mean_matrix(N, e, **kw)
    M = [[-A[i][j] for j in range(len(A))] for i in range(len(A))]
    return leading_minors_positive(M)
