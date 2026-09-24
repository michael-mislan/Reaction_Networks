"""Non-rigorous numerics for the finite witness (binary64, SciPy).

Periodic orbits by Newton shooting with the full variational equation, Floquet
multipliers, the unstable inner cycle (found by basin bisection, refined by
shooting) and continuation of both cycles in the reverse ratio r.
Nothing here is a proof; the certified statements are those of the paper.
"""
import numpy as np
from scipy.integrate import solve_ivp
from clock import FloatSystem, finite_model

RTOL, ATOL = 1e-11, 1e-13


def flow(sys_, y0, T, u=0.0, dense=False, with_var=True):
    n = 9
    if with_var:
        def rhs(t, z):
            y = z[:n]; M = z[n:].reshape(n, n)
            return np.concatenate([sys_.f(t, y, u), (sys_.jac(t, y, u) @ M).ravel()])
        z0 = np.concatenate([y0, np.eye(n).ravel()])
        sol = solve_ivp(rhs, (0, T), z0, method='LSODA', rtol=RTOL, atol=ATOL, dense_output=dense)
        return sol.y[:n, -1], sol.y[n:, -1].reshape(n, n), sol
    sol = solve_ivp(lambda t, y: sys_.f(t, y, u), (0, T), y0, method='LSODA', rtol=RTOL, atol=ATOL,
                    jac=lambda t, y: sys_.jac(t, y, u), dense_output=dense)
    return sol.y[:, -1], None, sol


def shoot(sys_, y0, T, iters=12, tol=1e-11, verbose=False):
    """Newton on (y0, T): phi_T(y0) = y0 with phase condition f(y0_init).(y0 - y0_init) = 0."""
    y0 = np.array(y0, float); f0 = sys_.f(0, y0); yref = y0.copy()
    for it in range(iters):
        yT, M, _ = flow(sys_, y0, T)
        res = np.concatenate([yT - y0, [f0 @ (y0 - yref)]])
        if verbose:
            print(it, np.linalg.norm(res), T)
        if np.linalg.norm(res) < tol:
            break
        A = np.zeros((10, 10)); A[:9, :9] = M - np.eye(9); A[:9, 9] = sys_.f(0, yT); A[9, :9] = f0
        d = np.linalg.solve(A, -res); y0 = y0 + d[:9]; T = T + d[9]
    yT, M, _ = flow(sys_, y0, T)
    mult = np.linalg.eigvals(M)
    return y0, T, mult[np.argsort(-np.abs(mult))], np.linalg.norm(yT - y0)


def readout(sys_, Y):
    X = sys_.x0[:, None] + sys_.P @ Y
    return X[3] + X[11]


def orbit_samples(sys_, y0, T, n=2001):
    _, _, sol = flow(sys_, y0, T, dense=True, with_var=False)
    t = np.linspace(0, T, n)
    return t, sol.sol(t)


def find_attracting_cycle(sys_, kick=None, T_guess=28.7, settle=6000.0):
    """Integrate from a large kick until the attracting cycle is reached, then shoot."""
    y = np.zeros(9) if kick is None else np.array(kick, float)
    y, _, _ = flow(sys_, y, settle, with_var=False)
    # place the start on the section {f(y).(.-y)=0}: just use the current point
    return shoot(sys_, y, T_guess)


def fate(sys_, y0, horizon, amp_cycle):
    """+1 if the trajectory ends on the large cycle, -1 if it ends at rest (by final readout range)."""
    y = np.array(y0, float)
    _, _, sol = flow(sys_, y, horizon, with_var=False, dense=True)
    t = np.linspace(horizon - 60.0, horizon, 600)
    R = readout(sys_, sol.sol(t))
    return (1 if (R.max() - R.min()) > 0.5*amp_cycle else -1), sol


if __name__ == '__main__':
    import json, time
    t0 = time.time()
    S = FloatSystem(finite_model())
    ev = np.linalg.eigvals(S.jac(0, np.zeros(9)))
    print('sink eigenvalues', np.sort_complex(ev))
    y0, T, mult, err = find_attracting_cycle(S, kick=0.3*np.array([0, 0, 1.0, 0, 0, 0, 0, 0, 1.0]))
    t, Y = orbit_samples(S, y0, T)
    R = readout(S, Y)
    print('period', T, 'closure', err, 'range', R.max() - R.min(), time.time() - t0)
    print('multipliers', mult)
