"""Exact phase-wise exponential integrals for the branching reserves.

A function on one phase is  sum_{(m,k)} coef * w^m * e^{-k w},  w in [0,h],
with x = e^{-h} a fixed rational.  Coefficients are Fractions.  Definite
integration over [0,h] returns a polynomial in h with rational coefficients
(dict m -> Fraction), because the antiderivative of a constant contributes w.

Schedules are listed in BACKWARD time order: phase 0 is the LAST chronological
phase, because the extinction (backward) equation is propagated from the deadline.
"""
from fractions import Fraction as F

__all__ = ['EF', 'ONE', 'SCHED', 'reserves', 'poly_add', 'poly_eval_interval',
           'log_enclosure', 'upper']


class EF(dict):
    """dict (m, k) -> Fraction, meaning sum coef * w^m * e^{-k w}."""

    def __add__(self, other):
        out = EF(self)
        for key, v in other.items():
            out[key] = out.get(key, F(0)) + v
            if out[key] == 0:
                del out[key]
        return out

    def __sub__(self, other):
        return self + other.scale(-1)

    def scale(self, c):
        c = F(c)
        return EF({k: v * c for k, v in self.items() if v * c != 0})

    def __mul__(self, other):
        out = {}
        for (m1, k1), v1 in self.items():
            for (m2, k2), v2 in other.items():
                key = (m1 + m2, k1 + k2)
                out[key] = out.get(key, F(0)) + v1 * v2
        return EF({k: v for k, v in out.items() if v != 0})

    def at_h(self, x):
        """Value at w = h as a polynomial in h: dict m -> Fraction."""
        out = {}
        for (m, k), v in self.items():
            out[m] = out.get(m, F(0)) + v * F(x) ** k
        return {m: v for m, v in out.items() if v != 0}

    def antiderivative(self):
        """G(w) with G(0) = 0."""
        out = EF()
        for (m, k), v in self.items():
            if k == 0:
                out = out + EF({(m + 1, 0): v / (m + 1)})
            elif m == 0:
                out = out + EF({(0, 0): v / k, (0, k): -v / k})
            elif m == 1:
                out = out + EF({(0, 0): v / k**2, (0, k): -v / k**2, (1, k): -v / k})
            elif m == 2:
                out = out + EF({(0, 0): 2 * v / k**3, (0, k): -2 * v / k**3,
                                (1, k): -2 * v / k**2, (2, k): -v / k})
            else:
                raise NotImplementedError(m)
        return out

    def integral_0_h(self, x):
        return self.antiderivative().at_h(x)


ONE = EF({(0, 0): F(1)})

SCHED = {
    'AB': [(3, 3), (2, 4)],   # chronologically A = (2,4) then B = (3,3)
    'BA': [(2, 4), (3, 3)],
    'A': [(2, 4)],
    'B': [(3, 3)],
}


def poly_add(a, b):
    out = dict(a)
    for m, v in b.items():
        out[m] = out.get(m, F(0)) + v
    return {m: v for m, v in out.items() if v != 0}


def poly_eval_interval(p, hlo, hhi):
    """Rigorous enclosure of a polynomial in h for h in [hlo, hhi], h > 0."""
    lo = hi = F(0)
    for m, v in p.items():
        t1, t2 = v * hlo**m, v * hhi**m
        lo += min(t1, t2)
        hi += max(t1, t2)
    return lo, hi


def upper(p, hlo, hhi):
    return poly_eval_interval(p, hlo, hhi)[1]


def log_enclosure(num, den, terms=60):
    """[lo, hi] rational enclosure of log(num/den) for num > den > 0,
    from the alternating series for log(1+y), y = (num-den)/den < 1."""
    assert num > den > 0 and F(num - den, den) < 1
    y = F(num - den, den)
    s = F(0)
    lo = hi = None
    for n in range(1, terms + 1):
        s += (-1) ** (n + 1) * y**n / n
        if n % 2 == 1:
            hi = s
        else:
            lo = s
    return lo, hi


def reserves(name, x, sharp=True):
    """Return the reserve W_a as a polynomial in h (dict m -> Fraction).

    sharp=True  : W_a = int_0^{nh} e^{-(nh-u)} t0(u) (sigma_S+sigma_T)(u) du
                  with sigma_i(u) = int_0^u e^{-(R_i(u)-R_i(tau))} s0_i(tau) dtau.
    sharp=False : the published occupation reserve
                  V_a = int_0^{nh} e^{-(nh-u)} (L_S+L_T)(u) du,
                  L_i(u) = int_0^u e^{-(R_i(u)-R_i(tau))} dtau.
    """
    sched = SCHED[name]
    n = len(sched)
    x = F(x)
    offS, offT = [0] * n, [0] * n
    for k in range(1, n):
        offS[k] = offS[k - 1] + sched[k - 1][0]
        offT[k] = offT[k - 1] + sched[k - 1][1]
    dS_list = [p[0] for p in sched]
    dT_list = [p[1] for p in sched]

    def pieces(k, d, dlist, offlist):
        """Return (L, sigma_main, sigma_h) on phase k as EFs; sigma = sigma_main + h*sigma_h."""
        const = F(0)
        for j in range(k):
            dj = dlist[j]
            const += x ** (-offlist[j]) * (x ** (-dj) - 1) / dj
        inner = EF({(0, 0): const}) + EF({(0, -d): x ** (-offlist[k]) / d,
                                          (0, 0): -x ** (-offlist[k]) / d})
        pre = EF({(0, d): x ** offlist[k]})
        L = pre * inner                                    # int_0^u e^{-(R(u)-R(tau))} dtau
        sig_main = pre * (inner - EF({(1, 0): F(1)}))      # subtract w  (u = k h + w)
        sig_h = pre.scale(-k)                               # subtract k*h
        return L, sig_main, sig_h

    total = {}
    for k in range(n):
        dS, dT = sched[k]
        wt = EF({(0, -1): x ** (n - k)})                    # e^{-(n h - u)}
        LS, sgS, khS = pieces(k, dS, dS_list, offS)
        LT, sgT, khT = pieces(k, dT, dT_list, offT)
        if not sharp:
            total = poly_add(total, (wt * (LS + LT)).integral_0_h(x))
            continue
        t0 = ONE - EF({(0, dT): x ** offT[k]})
        total = poly_add(total, (wt * t0 * (sgS + sgT)).integral_0_h(x))
        khp = (wt * t0 * (khS + khT)).integral_0_h(x)
        total = poly_add(total, {m + 1: v for m, v in khp.items()})
    return total
