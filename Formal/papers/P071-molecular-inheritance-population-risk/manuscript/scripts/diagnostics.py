"""Floating-point diagnostics (labelled N in the paper): size/preparation trends,
the first-moment survival bound of the boundary theorem, population variances,
Erlang clocks, and the slope sweep.  Writes data/diagnostics.json."""
import json, time
from pathlib import Path
import numpy as np
from scipy.sparse import csr_matrix, identity, diags
from scipy.sparse.linalg import splu, expm_multiply
from scipy.integrate import solve_ivp
from model import source, pair, step_hazard, smooth_hazard, extinction

OUT = Path(__file__).resolve().parents[1] / "data"
b = .1


def sparse_extinction(Q, D, pairs, d, tol=1e-13):
    n = len(d); lu = splu((diags(b + d) - csr_matrix(Q)).tocsc())
    Rd = lu.solve(d); out = []
    for ind in (False, True):
        z = np.zeros(n)
        for it in range(400000):
            zn = Rd + lu.solve(b * ((D @ z) ** 2 if ind else pair(pairs, z, z, n)))
            if np.max(np.abs(zn - z)) < tol:
                break
            z = zn
        out.append(zn)
    return out


def main():
    t0 = time.time(); out = dict(sizes=[], variance=[], clocks=[], slopes=[])
    for N in (2, 4, 8, 16, 32, 64, 128):
        states, ix, Q, D, pairs = source(N)
        Qs, Ds = csr_matrix(Q), csr_matrix(D)
        m = int((N + np.sqrt(N)) / 2); bd = (m, N - m)
        for smooth in (False, True):
            d = smooth_hazard(states, N) if smooth else step_hazard(states)
            qj, qi = sparse_extinction(Qs, Ds, pairs, d)
            gap = qi - qj; best = int(np.argmax(gap))
            A = Qs + b * (2 * Ds - identity(len(d))) - diags(d)
            ts = np.linspace(0, 120, 241)
            mt = expm_multiply(A.tocsc(), np.ones(len(d)), start=0, stop=120, num=241)[:, ix[bd]]
            row = dict(N=N, smooth=smooth, boundary=bd, interior_gap=float(gap[ix[N, 0]]),
                       boundary_gap=float(gap[ix[bd]]), boundary_qJ=float(qj[ix[bd]]), boundary_qI=float(qi[ix[bd]]),
                       diag_qJ=float(qj[ix[N // 2, N // 2]]), diag_qI=float(qi[ix[N // 2, N // 2]]),
                       max_gap=float(gap[best]), max_state=states[best],
                       first_moment_bound=float(min(1, mt.min())), first_moment_time=float(ts[int(mt.argmin())]))
            if N == 16:
                row["q97"] = [float(qj[ix[9, 7]]), float(qi[ix[9, 7]])]
            out["sizes"].append(row); print(row, f"{time.time() - t0:.0f}s", flush=True)
    # population variance, N=16 smooth from (9,7) and N=2 step from AA
    for N, smooth, founder in ((2, False, (2, 0)), (16, True, (9, 7))):
        states, ix, Q, D, pairs = source(N); n = len(states)
        d = smooth_hazard(states, N) if smooth else step_hazard(states)
        A = Q + b * (2 * D - np.eye(n)) - np.diag(d)
        def rhs(t, y):
            m, vj, vi = y[:n], y[n:2 * n], y[2 * n:]
            return np.concatenate([A @ m, A @ vj + 2 * b * pair(pairs, m, m, n), A @ vi + 2 * b * (D @ m) ** 2])
        tt = np.linspace(0, 60, 61)
        sol = solve_ivp(rhs, (0, 60), np.concatenate([np.ones(n), np.zeros(2 * n)]), method="LSODA",
                        t_eval=tt, rtol=1e-10, atol=1e-12)
        k = ix[founder]; m = sol.y[k]; vj = sol.y[n + k]; vi = sol.y[2 * n + k]
        varj = vj + m - m * m; vari = vi + m - m * m
        assert np.all(sol.y[2 * n:] - sol.y[n:2 * n] > -1e-7)
        out["variance"].append(dict(N=N, smooth=smooth, founder=founder, t=tt.tolist(), mean=m.tolist(),
                                    var_joint=varj.tolist(), var_ind=vari.tolist()))
        print("variance", N, founder, m[-1], varj[-1], vari[-1], flush=True)
    # Erlang clocks at N=16 smooth
    N = 16; states, ix, Q, D, pairs = source(N); n = len(states); d = smooth_hazard(states, N)
    for phase in (1, 2, 4):
        rate = phase / 10; V = np.linalg.solve(rate * np.eye(n) + np.diag(d) - Q, rate * np.eye(n))
        W = np.linalg.matrix_power(V, phase); c = 1 - W @ np.ones(n); qs = []
        for ind in (False, True):
            z = np.zeros(n)
            for _ in range(100000):
                zn = c + W @ ((D @ z) ** 2 if ind else pair(pairs, z, z, n))
                if np.max(np.abs(zn - z)) < 1e-14:
                    break
                z = zn
            qs.append(zn)
        AA = np.zeros((phase * n, phase * n))
        for p in range(phase):
            AA[p * n:(p + 1) * n, p * n:(p + 1) * n] = Q - np.diag(d) - rate * np.eye(n)
            q = (p + 1) % phase
            AA[p * n:(p + 1) * n, q * n:(q + 1) * n] += rate * (2 * D if p == phase - 1 else np.eye(n))
        out["clocks"].append(dict(phases=phase, growth=float(np.linalg.eigvals(AA).real.max()),
                                  qJ_10_6=float(qs[0][ix[10, 6]]), qI_10_6=float(qs[1][ix[10, 6]]),
                                  qJ_9_7=float(qs[0][ix[9, 7]]), qI_9_7=float(qs[1][ix[9, 7]])))
        print(out["clocks"][-1], flush=True)
    # slope sweep at (9,7)
    for s in np.linspace(7, 9, 21):
        qj, qi = extinction(Q, D, pairs, smooth_hazard(states, N, s), b)
        out["slopes"].append(dict(s=float(s), qJ=float(qj[ix[9, 7]]), qI=float(qi[ix[9, 7]])))
    out["seconds"] = time.time() - t0
    OUT.mkdir(exist_ok=True); (OUT / "diagnostics.json").write_text(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
