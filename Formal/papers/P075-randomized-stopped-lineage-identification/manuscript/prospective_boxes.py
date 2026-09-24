"""Prospective certified decision over a declared source class.

Every source in the class is enclosed by exact rational interval arithmetic:
the two-state inverse, the emission map and the reported confidence sets are
composed without any grid search or numerical optimiser.
"""
from fractions import Fraction as Q
from certkit import I, iv, sqrt_up, kl_interval, kl_ball_hat, evaluate

LF, LC = Q(25, 4), Q(6)
E_S, E_T = Q(1, 10), Q(17, 20)


def enlarge_kl(x, n, L):
    """All Chernoff sets reportable when the true probability lies in x."""
    lo = kl_interval(kl_ball_hat(x.a, n, L).a, n, L).a
    hi = kl_interval(kl_ball_hat(x.b, n, L).b, n, L).b
    return I(max(Q(0), lo), min(Q(1), hi))


def enlarge_hoeffding(x, n, L):
    r = 2 * sqrt_up(Q(L, 2 * n))
    return I(max(Q(0), x.a - r), min(Q(1), x.b + r))


def law(lam, qST):
    """Exact interval enclosure of the observed deadline block over the class."""
    p = I('.345', '.355'); a = iv(qST); r = I('.068', '.072')
    bs = I('.218', '.222'); bt = I('.158', '.162')
    ds = I('.118', '.122'); dt = I('.038', '.042')
    z = I(lam)
    al = z + a + bs + ds; be = z + r + bt + dt
    det = al * be - a * r
    A = [[z * be / det, z * a / det], [z * r / det, z * al / det]]
    M = [[(1 - p) * A[0][0], (1 - p) * A[0][1]], [p * A[1][0], p * A[1][1]]]
    E = [[I('.9'), I('.15')], [I('.1'), I('.85')]]
    EM = [[sum((E[i][k] * M[k][j] for k in (0, 1)), I(0)) for j in (0, 1)] for i in (0, 1)]
    J = [[sum((EM[i][k] * E[j][k] for k in (0, 1)), I(0)) for j in (0, 1)] for i in (0, 1)]
    mu = I('.1') * (1 - p) + I('.85') * p
    return J, mu


def arm(lam, qST, n, ncal, scheme, method):
    J, mu = law(lam, qST)
    en = enlarge_kl if scheme == 'kl' else enlarge_hoeffding
    Jw = [[en(J[i][j], n, LF) for j in (0, 1)] for i in (0, 1)]
    return evaluate(Jw, en(mu, n, LF), en(I(E_S), ncal, LC), en(I(E_T), ncal, LC),
                    I(lam), method)


def decide(lam, n, ncal, scheme='kl', method='cancelled', thr=Q(2, 5)):
    """Null: both arms have q_ST in [.049,.051].  Alternative: treated in [.849,.851]."""
    lo = arm(lam, Q('.049'), n, ncal, scheme, method)
    hi = arm(lam, Q('.051'), n, ncal, scheme, method)
    if lo is None or hi is None:
        return None
    ctrl = I(min(lo.a, hi.a), max(lo.b, hi.b))
    alt = arm(lam, I('.849', '.851'), n, ncal, scheme, method)
    if alt is None:
        return None
    return dict(null=ctrl - ctrl, alt=alt - ctrl, ok=bool((ctrl - ctrl).b < thr < (alt - ctrl).a))


if __name__ == '__main__':
    for scheme, method in (('hoeffding', 'matrix'), ('hoeffding', 'cancelled'), ('kl', 'cancelled')):
        for n in (140000, 150000, 200000, 1000000):
            d = decide(Q(1), n, n, scheme, method)
            print('%-10s %-10s n=%-8d %s' % (scheme, method, n,
                  'unresolved' if d is None else 'null=%s alt=%s certified=%s' % (d['null'], d['alt'], d['ok'])))
