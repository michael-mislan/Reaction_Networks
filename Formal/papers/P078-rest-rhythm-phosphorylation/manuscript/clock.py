"""Shared model code for the rest--rhythm bistability paper.

Everything is built from the literal reaction list through ``phos.Model`` (exact
SymPy rationals).  This module is independent of the research-workspace
checkers: it shares no code with ``local_certificate.py`` and rebuilds the
Jacobian, the Hessian and the normal form from scratch.

  * ``patch_model(s, r)``     generalized-Hopf rational patch (Table 2 of the paper)
  * ``finite_model()``        the separate finite witness (Table 3)
  * ``FloatSystem``           binary64 chart field / Jacobian for integration
  * ``normal_form``           order-by-order centre-manifold normal form (mpmath)
"""
import json
from pathlib import Path
import numpy as np
import sympy as sp
import mpmath as mpm
from phos import Model

HERE = Path(__file__).resolve().parent
PATCH = json.loads((HERE/'data'/'rational_patch.json').read_text())
FINITE = json.loads((HERE/'data'/'finite_source_exact.json').read_text())
HUNDREDTH = sp.Rational(1, 100)
SPECIES = ['S0', 'S1', 'S2', 'S3', 'E', 'F', 'C1', 'C2', 'C3', 'D1', 'D2', 'D3']
RATE_NAMES = ['a1', 'b1', 'c1', 'a2', 'b2', 'c2', 'a3', 'b3', 'c3',
              'alpha1', 'beta1', 'gamma1', 'alpha2', 'beta2', 'gamma2', 'alpha3', 'beta3', 'gamma3']
# certified centre of the generalized-Hopf root box (workspace local_root_certificate.json)
GH_CENTER = ('-0.000000000000071327193689602375120074061959297705002906636289151',
             '1.3837873770514133594599820978726493616170481963142',
             '0.24181138881757963174653685803240572988982213287093')


def patch_model(s, r):
    s = sp.Rational(str(s)) if not isinstance(s, sp.Basic) else s
    r = sp.Rational(str(r)) if not isinstance(r, sp.Basic) else r
    x = [sp.Rational(a) + s*sp.Rational(b) for a, b in zip(PATCH['x0'], PATCH['v'])]
    q = [sp.Rational(a) + s*sp.Rational(b) for a, b in zip(PATCH['q0'], PATCH['w'])]
    return Model(3, x, q, [HUNDREDTH]*3, [r, HUNDREDTH, HUNDREDTH])


def finite_model(r=None):
    x = [sp.Rational(v) for v in FINITE['xstar']]
    q = [sp.Rational(v) for v in FINITE['currents']]
    r = sp.Rational(FINITE['r']) if r is None else r
    return Model(3, x, q, [HUNDREDTH]*3, [r, HUNDREDTH, HUNDREDTH])


def rate_list(m):
    """Eighteen rates in the order of RATE_NAMES."""
    out = []
    for j in range(6):
        out += [m.kon[j], m.koff[j], m.kcat[j]]
    return out


class FloatSystem:
    """binary64 chart dynamics  y' = Rm N v(x* + P y)  of a Model."""

    def __init__(self, m, rates=None, xstar=None):
        self.m = m
        self.P = np.array(m.P.tolist(), dtype=float)
        self.Rm = np.array(m.Rm.tolist(), dtype=float)
        self.N = np.array(m.N.tolist(), dtype=float)
        self.RN = self.Rm @ self.N
        self.x0 = np.array([float(v) for v in m.x]) if xstar is None else np.asarray(xstar, float)
        self.kon = np.array([float(v) for v in m.kon])
        self.koff = np.array([float(v) for v in m.koff])
        self.kcat = np.array([float(v) for v in m.kcat])
        if rates is not None:
            self.kon, self.koff, self.kcat = (np.array(rates[0::3], float), np.array(rates[1::3], float),
                                              np.array(rates[2::3], float))
        self.lev, self.enz, self.cpx = np.array(m.lev), np.array(m.enz), np.array(m.cpx)

    def flux(self, x, u=0.0):
        kon = self.kon.copy(); kon[3] *= (1.0 + u)          # arm 3 = phosphatase arm D_1: alpha_1
        v = np.empty(18)
        v[0::3] = kon*x[self.lev]*x[self.enz]
        v[1::3] = self.koff*x[self.cpx]
        v[2::3] = self.kcat*x[self.cpx]
        return v

    def f(self, t, y, u=0.0):
        return self.RN @ self.flux(self.x0 + self.P @ y, u)

    def jac(self, t, y, u=0.0):
        x = self.x0 + self.P @ y
        kon = self.kon.copy(); kon[3] *= (1.0 + u)
        D = np.zeros((18, 12))
        for j in range(6):
            D[3*j, self.lev[j]] = kon[j]*x[self.enz[j]]
            D[3*j, self.enz[j]] = kon[j]*x[self.lev[j]]
            D[3*j+1, self.cpx[j]] = self.koff[j]
            D[3*j+2, self.cpx[j]] = self.kcat[j]
        return self.RN @ D @ self.P

    def species(self, y):
        return self.x0 + self.P @ y


# ---------------------------------------------------------------- normal form
def mp_JB(m):
    """mpmath Jacobian and bilinear form of the chart field of an exact Model."""
    J = mpm.matrix([[mpm.mpf(sp.Rational(v).p)/mpm.mpf(sp.Rational(v).q) for v in row] for row in m.jacobian().tolist()])
    rows = m.hessian_rows(); n = m.n
    kon = [mpm.mpf(v.p)/mpm.mpf(v.q) for v in m.kon]
    srow = [[mpm.mpf(int(v)) for v in rows[j][0]] for j in range(2*n)]
    erow = [[mpm.mpf(int(v)) for v in rows[j][1]] for j in range(2*n)]

    def B(u, v):
        out = [mpm.mpc(0)]*(3*n)
        for j in range(2*n):
            su = sum(a*b for a, b in zip(srow[j], u)); sv = sum(a*b for a, b in zip(srow[j], v))
            eu = sum(a*b for a, b in zip(erow[j], u)); ev = sum(a*b for a, b in zip(erow[j], v))
            out[n + j] = kon[j]*(su*ev + sv*eu)
        return out
    return J, B


def critical_pair(J, omega_guess):
    """Eigenvalue nearest i*omega_guess, with right vector q and left vector ell, ell^T q = 1."""
    E, ER = mpm.eig(J)
    k = min(range(len(E)), key=lambda i: abs(E[i] - 1j*omega_guess))
    lam = E[k]; q = [ER[i, k] for i in range(J.rows)]
    Et, EL = mpm.eig(J.T)
    k2 = min(range(len(Et)), key=lambda i: abs(Et[i] - lam))
    ell = [EL[i, k2] for i in range(J.rows)]
    q = [v/q[-1] for v in q]                                 # q_{D3} = 1
    pair = sum(a*b for a, b in zip(ell, q)); ell = [v/pair for v in ell]
    return lam, q, ell, E


def normal_form(J, B, lam, q, ell, order=5):
    """Plain-power centre-manifold recurrence.

    H(w,wb) = w q + wb qb + sum_{j+k>=2} H[j,k] w^j wb^k,   w' = lam w + sum G[k] w^{k+1} wb^k.
    Returns (G, H); G[1], G[2] are the cubic and quintic coefficients c1, c2.
    Written independently of the factorial-normalised formulas of Appendix B.
    """
    dim = J.rows
    lamb = mpm.conj(lam)
    qb = [mpm.conj(v) for v in q]
    H = {(1, 0): list(q), (0, 1): qb}
    G = {}
    Jm = J

    def solve(A, b):
        return list(mpm.lu_solve(A, mpm.matrix(b)))

    for n in range(2, order + 1):
        for j in range(n, -1, -1):
            k = n - j
            if j < k:                                            # reality: H[j,k] = conj(H[k,j])
                H[(j, k)] = [mpm.conj(v) for v in H[(k, j)]]
                continue
            rhs = [mpm.mpc(0)]*dim
            # quadratic part: coefficient of w^j wb^k in B(H,H)/2
            for (a, b_), Ha in list(H.items()):
                c, d = j - a, k - b_
                if (c, d) in H and a + b_ >= 1 and c + d >= 1 and a + b_ < n and c + d < n:
                    rhs = [x + y/2 for x, y in zip(rhs, B(Ha, H[(c, d)]))]
            # transport by the nonlinear part of the reduced field
            for (a, b_), Ha in list(H.items()):
                if a + b_ >= n or a + b_ < 1:
                    continue
                for kk, g in G.items():
                    # d/dt (w^a wb^b) contains a*g w^{a+kk} wb^{b+kk} and b*conj(g) w^{a+kk} wb^{b+kk}
                    if (a + kk, b_ + kk) == (j, k):
                        rhs = [x - (a*g + b_*mpm.conj(g))*y for x, y in zip(rhs, Ha)]
            A = mpm.matrix(dim, dim)
            mu = j*lam + k*lamb
            for i in range(dim):
                for l in range(dim):
                    A[i, l] = (mu if i == l else 0) - Jm[i, l]
            if j == k + 1:                                       # resonant: bordered solve
                Ab = mpm.matrix(dim + 1, dim + 1)
                for i in range(dim):
                    for l in range(dim):
                        Ab[i, l] = A[i, l]
                    Ab[i, dim] = q[i]; Ab[dim, i] = ell[i]
                sol = solve(Ab, rhs + [mpm.mpc(0)])
                H[(j, k)] = sol[:dim]; G[k] = sol[dim]
            else:
                H[(j, k)] = solve(A, rhs)
    return G, H


def hopf_point(s, r0, om0, dps=40):
    """Newton solve of Re/Im det-free Hopf conditions in r for the patch at parameter s (mpmath)."""
    mpm.mp.dps = dps

    def crit(r):
        J, _ = mp_JB(patch_model(sp.Rational(str(s)), sp.Rational(mpm.nstr(r, dps))))
        lam, *_ = critical_pair(J, om0)
        return lam
    r = mpm.findroot(lambda rr: mpm.re(crit(rr)), mpm.mpf(r0), tol=mpm.mpf(10)**(-dps + 8))
    return r, mpm.im(crit(r))
