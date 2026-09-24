"""Floating-point companion to phos.py: simulation, periodic orbits, Floquet multipliers.

Everything produced here is numerical evidence (label N in the paper), never a proof input.
"""
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp
from scipy.optimize import brentq


class FloatModel:
    def __init__(self, model):
        self.m = model; n = model.n; self.n = n
        f = lambda v: np.array([float(a) for a in v], dtype=float)
        self.kon, self.koff, self.kcat = f(model.kon), f(model.koff), f(model.kcat)
        self.x0 = f(model.x)
        self.P = np.array(model.P.tolist(), dtype=float)
        self.R = np.array(model.Rm.tolist(), dtype=float)
        self.N = np.array(model.N.tolist(), dtype=float)
        self.lev, self.enz, self.cpx = map(np.array, (model.lev, model.enz, model.cpx))
        self.RN = self.R @ self.N

    def flux(self, x):
        v = np.empty(6*self.n)
        v[0::3] = self.kon*x[self.lev]*x[self.enz]
        v[1::3] = self.koff*x[self.cpx]
        v[2::3] = self.kcat*x[self.cpx]
        return v

    def species(self, y):
        return self.x0 + self.P @ y

    def F(self, t, y):
        return self.RN @ self.flux(self.x0 + self.P @ y)

    def DF(self, t, y):
        x = self.x0 + self.P @ y
        D = np.zeros((6*self.n, 3*self.n + 3))
        j = np.arange(2*self.n)
        D[3*j, self.lev] = self.kon*x[self.enz]
        D[3*j, self.enz] = self.kon*x[self.lev]
        D[3*j+1, self.cpx] = self.koff
        D[3*j+2, self.cpx] = self.kcat
        return self.RN @ D @ self.P

    def integrate(self, y0, T, rtol=1e-11, atol=1e-13, dense=False, t_eval=None):
        return solve_ivp(self.F, (0, T), y0, method='LSODA', jac=self.DF, rtol=rtol, atol=atol,
                         dense_output=dense, t_eval=t_eval)

    def flow_with_variation(self, y0, T, rtol=1e-11, atol=1e-13):
        d = len(y0)
        def rhs(t, w):
            y = w[:d]; V = w[d:].reshape(d, d)
            return np.concatenate([self.F(t, y), (self.DF(t, y) @ V).ravel()])
        sol = solve_ivp(rhs, (0, T), np.concatenate([y0, np.eye(d).ravel()]), method='LSODA',
                        rtol=rtol, atol=atol)
        w = sol.y[:, -1]
        return w[:d], w[d:].reshape(d, d)

    def periodic_orbit(self, y0, T, tol=1e-12, maxit=30):
        """Newton shooting with the phase condition <F(y0_initial), y - y0_initial> = 0."""
        d = len(y0); anchor = y0.copy(); direction = self.F(0, anchor)
        for it in range(maxit):
            yT, V = self.flow_with_variation(y0, T)
            res = np.concatenate([yT - y0, [direction @ (y0 - anchor)]])
            if np.max(np.abs(res)) < tol:
                break
            Jm = np.zeros((d + 1, d + 1))
            Jm[:d, :d] = V - np.eye(d); Jm[:d, d] = self.F(0, yT); Jm[d, :d] = direction
            step = np.linalg.solve(Jm, -res)
            y0 = y0 + step[:d]; T = T + step[d]
        yT, V = self.flow_with_variation(y0, T)
        return y0, T, V, float(np.max(np.abs(yT - y0)))


def hopf_float(build, bracket):
    J0 = np.array(build(sp.Integer(0)).jacobian().tolist(), dtype=float)
    J1 = np.array(build(sp.Integer(1)).jacobian().tolist(), dtype=float)
    def lead(r):
        ev = np.linalg.eigvals(J0 + r*(J1 - J0)); ev = ev[ev.imag > 1e-9]
        return ev[np.argmax(ev.real)]
    r = brentq(lambda s: lead(s).real, *bracket, xtol=1e-14)
    return r, lead(r).imag
