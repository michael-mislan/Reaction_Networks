"""Generate data/numerics.json and data/branch.npz (binary64 numerics; not proofs).

1. attracting and inner (unstable) cycle of the finite witness, DOP853-polished;
2. continuation of the cycle branch in the reverse ratio r through the fold,
   parametrised by the amplitude coordinate xi on the section zeta = 0;
3. slow-mode recovery times.
"""
import json, time
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from clock import FloatSystem, finite_model, FINITE
import sympy as sp

t00 = time.time()
S = FloatSystem(finite_model())
R0 = float(sp.Rational(FINITE['r']))
q1 = float(sp.Rational(FINITE['currents'][0]))
xs = S.x0
DKON = q1/(xs[1]*xs[5]); DKOFF = q1/xs[9]                     # d alpha_1/dr, d beta_1/dr


def set_r(r):
    S.kon[3] = (1 + r)*DKON; S.koff[3] = r*DKOFF


def dfdr(y):
    x = S.species(y); v = np.zeros(18)
    v[9] = DKON*x[1]*x[5]; v[10] = DKOFF*x[9]
    return S.RN @ v


def flow_r(y0, T, method='LSODA', rtol=1e-10, atol=1e-13):
    """Flow with monodromy M and parameter sensitivity s = d phi / d r."""
    n = 9

    def rhs(t, z):
        y = z[:n]; M = z[n:n+81].reshape(n, n); s = z[n+81:]
        Jy = S.jac(t, y)
        return np.concatenate([S.f(t, y), (Jy @ M).ravel(), Jy @ s + dfdr(y)])
    z0 = np.concatenate([y0, np.eye(n).ravel(), np.zeros(n)])
    sol = solve_ivp(rhs, (0, T), z0, method=method, rtol=rtol, atol=atol)
    return sol.y[:n, -1], sol.y[n:n+81, -1].reshape(n, n), sol.y[n+81:, -1]


# amplitude coordinates from the critical left eigenvector at the family's Hopf point
set_r(1.3446715241927645)
w, VL = np.linalg.eig(S.jac(0, np.zeros(9)).T)
k = np.argmax(w.imag); ell = VL[:, k]
w2, VR = np.linalg.eig(S.jac(0, np.zeros(9)))
k2 = np.argmax(w2.imag); qv = VR[:, k2]/VR[8, k2]
ell = ell/(ell @ qv)
XI, ZETA = 2*ell.real, -2*ell.imag                            # y ~ Re(w q): xi + i zeta ~ w... linear amplitude coordinates
set_r(R0)


def corrector(y0, T, r, p, method='LSODA', rtol=1e-10, tol=1e-9, iters=10):
    for it in range(iters):
        set_r(r)
        yT, M, s = flow_r(y0, T, method=method, rtol=rtol, atol=rtol*1e-3)
        res = np.concatenate([yT - y0, [ZETA @ y0, XI @ y0 - p]])
        if np.linalg.norm(res) < tol:
            return y0, T, r, M, True
        A = np.zeros((11, 11))
        A[:9, :9] = M - np.eye(9); A[:9, 9] = S.f(0, yT); A[:9, 10] = s
        A[9, :9] = ZETA; A[10, :9] = XI
        d = np.linalg.solve(A, -res)
        y0 = y0 + d[:9]; T += d[9]; r += d[10]
    return y0, T, r, M, False


def readout_range(y0, T):
    sol = solve_ivp(lambda t, y: S.f(t, y), (0, T), y0, method='LSODA', rtol=1e-10, atol=1e-13,
                    jac=lambda t, y: S.jac(t, y), dense_output=True)
    Y = sol.sol(np.linspace(0, T, 1500)); X = S.x0[:, None] + S.P @ Y
    Rd = X[3] + X[11]
    return float(Rd.max() - Rd.min()), X


def to_section(y0, T):
    """Move the base point along its orbit to the section zeta = 0, xi > 0."""
    sol = solve_ivp(lambda t, y: S.f(t, y), (0, T), y0, method='LSODA', rtol=1e-11, atol=1e-13,
                    jac=lambda t, y: S.jac(t, y), dense_output=True)
    ts = np.linspace(0, T, 4000); g = np.array([ZETA @ sol.sol(t) for t in ts])
    for i in range(len(ts) - 1):
        if g[i]*g[i+1] <= 0:
            tc = brentq(lambda t: ZETA @ sol.sol(t), ts[i], ts[i+1], xtol=1e-13)
            if XI @ sol.sol(tc) > 0:
                return sol.sol(tc)
    raise RuntimeError('no section crossing')


def shoot_fixed_r(y0, T, iters=8, tol=5e-13):
    """DOP853 Newton shooting at the witness value of r (unknowns y0 on the section zeta=0, and T)."""
    set_r(R0)
    for it in range(iters):
        yT, M, _ = flow_r(y0, T, method='DOP853', rtol=3e-14, atol=1e-17)
        res = np.concatenate([yT - y0, [ZETA @ y0]])
        if np.linalg.norm(res) < tol:
            return y0, T, M, True
        A = np.zeros((10, 10)); A[:9, :9] = M - np.eye(9); A[:9, 9] = S.f(0, yT); A[9, :9] = ZETA
        d = np.linalg.solve(A, -res); y0 = y0 + d[:9]; T += d[9]
    return y0, T, M, False


out = {'evidence': 'binary64 numerics (SciPy); illustrations and cross-checks, not certificates', 'r_witness': R0}

# ---- 1. the two cycles at the witness ------------------------------------------------
st = np.load('data/_stable.npz'); un = np.load('data/_unstable.npz')
cyc = {}
for name, d in (('stable', st), ('unstable', un)):
    y0 = to_section(d['y0'], float(d['T']))
    y0, T, M, ok = shoot_fixed_r(y0, float(d['T']))
    p = float(XI @ y0); r = R0                                # y0 already lies on the section zeta = 0
    mult = np.linalg.eigvals(M); mult = mult[np.argsort(-np.abs(mult))]
    rng, X = readout_range(y0, T)
    cyc[name] = dict(y0=y0, T=T, p=p)
    out[name + '_cycle'] = dict(period=T, r_recovered=r, converged=bool(ok), xi=p, readout_range=rng,
                                multipliers=[[float(m.real), float(m.imag)] for m in mult[:4]],
                                species_min=X.min(axis=1).tolist(), species_max=X.max(axis=1).tolist())
    print(name, T, r - R0, rng, mult[:3], time.time() - t00, flush=True)
np.savez('data/cycles.npz', stable_y0=cyc['stable']['y0'], stable_T=cyc['stable']['T'],
         unstable_y0=cyc['unstable']['y0'], unstable_T=cyc['unstable']['T'], XI=XI, ZETA=ZETA)

# ---- 2. branch in r -------------------------------------------------------------------
rows = []
pu, ps = cyc['unstable']['p'], cyc['stable']['p']


def sweep_simple(start, plist):
    y0, T, r = start['y0'].copy(), start['T'], R0
    hist = []
    for p in plist:
        if len(hist) >= 2:
            (pa, ya, Ta, ra), (pb, yb, Tb, rb) = hist[-2], hist[-1]
            sc = (p - pb)/(pb - pa)
            yg, Tg, rg = yb + sc*(yb - ya), Tb + sc*(Tb - Ta), rb + sc*(rb - ra)
        else:
            yg, Tg, rg = y0*(p/(XI @ y0)), T, r
        y1, T1, r1, M, ok = corrector(yg, Tg, rg, p)
        if not ok:
            print('  corrector failed at p =', p, flush=True); break
        mult = np.linalg.eigvals(M)
        nontrivial = sorted(mult, key=lambda m: abs(m - 1))[1:]
        lead = max(nontrivial, key=abs)
        rng, _ = readout_range(y1, T1)
        rows.append([p, r1, T1, rng, float(abs(lead))])
        hist.append((p, y1, T1, r1)); y0, T, r = y1, T1, r1
        print('  p=%.4f r=%.6f T=%.4f range=%.4f lead=%.5f  (%.0fs)' % (p, r1, T1, rng, abs(lead), time.time() - t00), flush=True)


print('branch: unstable cycle down to the Hopf point', flush=True)
sweep_simple(cyc['unstable'], list(pu*np.linspace(1, 0.06, 20)))
print('branch: unstable cycle up through the fold to the attracting cycle and beyond', flush=True)
sweep_simple(cyc['unstable'], list(np.linspace(pu, ps, 26)[1:]) + list(ps*np.linspace(1.04, 1.6, 15)))
rows = np.array(sorted(rows, key=lambda v: v[0]))
np.savez('data/branch.npz', rows=rows, columns=np.array(['xi', 'r', 'period', 'readout_range', 'lead_multiplier']))
ifold = int(np.argmax(rows[:, 1]))
out['branch'] = dict(points=len(rows), r_fold_estimate=float(rows[ifold, 1]), xi_at_fold=float(rows[ifold, 0]),
                     range_at_fold=float(rows[ifold, 3]), r_min_small_amplitude=float(rows[0, 1]))
print('fold estimate r =', rows[ifold, 1], flush=True)

# ---- 3. recovery times ---------------------------------------------------------------
set_r(R0)
ev = np.linalg.eigvals(S.jac(0, np.zeros(9)))
absc = float(max(ev.real)); Tst = out['stable_cycle']['period']
lead = out['stable_cycle']['multipliers'][1][0]
out['recovery'] = dict(sink_abscissa=absc, sink_efold=-1/absc, sink_efold_periods=-1/absc/Tst,
                       cycle_multiplier=lead, cycle_efold=-Tst/np.log(lead), cycle_efold_periods=-1/np.log(lead),
                       sink_eigenvalues=[[float(e.real), float(e.imag)] for e in sorted(ev, key=lambda z: z.real)])
json.dump(out, open('data/numerics.json', 'w'), indent=1)
print('done', time.time() - t00)
