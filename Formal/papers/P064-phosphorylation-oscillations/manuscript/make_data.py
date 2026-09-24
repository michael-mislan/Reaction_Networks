"""Numerical (evidence level N) data behind the figures: periodic branch, Floquet multipliers,
turnover, relaxation path, two-parameter oscillation region.  Writes figures/numerical_data.json.
None of these numbers is an input to a proof."""
import json, time
from pathlib import Path
import numpy as np
import sympy as sp
from phos import witness, Model, XA, QA, HUNDREDTH
from numerics import FloatModel, hopf_float

ROOT = Path(__file__).resolve().parent
rA, omA = hopf_float(lambda r: witness('A', r), (1.2, 1.6))
out = dict(rA=rA, omegaA=omA)


def attractor_guess(fm, T_end, y0):
    sol = fm.integrate(y0, T_end, rtol=1e-10, atol=1e-13, dense=True)
    # last upward crossing of the S3 mean through a section, period from two crossings
    ts = np.linspace(T_end - 400, T_end, 40001); Y = sol.sol(ts)
    s3 = (fm.P @ Y)[3]; s = s3 - s3.mean()
    idx = np.where((s[:-1] < 0) & (s[1:] >= 0))[0]
    return Y[:, idx[-2]], ts[idx[-1]] - ts[idx[-2]]


branch = []
y_guess = None
for r in [1.43, 1.425, 1.42, 1.41, 1.40, 1.375, 1.35, 1.325, 1.30, 1.25, 1.2, 1.1, 1.0, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2, 0.1, 0.05]:
    t0 = time.time()
    fm = FloatModel(witness('A', sp.Rational(str(r))))
    J = fm.DF(0, np.zeros(9)); ev, vec = np.linalg.eig(J); k = np.argmax(ev.real)
    if y_guess is None:
        y_start = 0.3*np.sqrt(max(rA - r, 1e-4))*np.real(vec[:, k]/vec[8, k])
    else:
        y_start = y_guess
    y0, T = attractor_guess(fm, 30000 if r > 1.41 else 6000, y_start)
    y0, T, V, res = fm.periodic_orbit(y0, T)
    y_guess = y0
    mult = np.linalg.eigvals(V); mult = mult[np.argsort(-np.abs(mult))]
    ts = np.linspace(0, T, 4001); sol = fm.integrate(y0, T, t_eval=ts); X = fm.x0[:, None] + fm.P @ sol.y
    flux = np.array([fm.flux(X[:, i]) for i in range(len(ts))])
    fwd = flux[:, 2:9:3].sum(axis=1)                       # c_i C_i, kinase arms 0..2
    Q = np.trapezoid(fwd, ts)
    edge = [float(abs(np.trapezoid(flux[:, 3*j+2] - flux[:, 3*(j+3)+2], ts))) for j in range(3)]
    row = dict(r=r, period=T, residual=res, multipliers=[[float(m.real), float(m.imag)] for m in mult],
               leading_nontrivial=float(np.abs(mult[1])), min_species=float(X.min()),
               p2p=dict(S3=float(np.ptp(X[3])), S3D3=float(np.ptp(X[3] + X[11])), D1=float(np.ptp(X[9])), F=float(np.ptp(X[5])), E=float(np.ptp(X[4]))),
               minmax=dict(S3=[float(X[3].min()), float(X[3].max())], S0=[float(X[0].min()), float(X[0].max())]),
               turnover=float(Q), edge_balance_defect=max(edge), eq_lead=[float(ev[k].real), float(abs(ev[k].imag))])
    branch.append(row)
    print(f"r={r}: T={T:.6f} res={res:.1e} |m2|={abs(mult[1]):.6f} p2p S3={row['p2p']['S3']:.5f} Q={Q:.4f} min={X.min():.4f} ({time.time()-t0:.1f}s)", flush=True)
    if r in (1.4, 1.0, 0.5):
        out[f'waveform_r{r}'] = dict(t=list(map(float, ts[::10])), X=[[float(v) for v in X[i, ::10]] for i in range(12)], T=T, y0=list(map(float, y0)))
out['branch'] = branch

# convergence to the cycle at r=1 from inside and outside
fm = FloatModel(witness('A', sp.Integer(1)))
J = fm.DF(0, np.zeros(9)); ev, vec = np.linalg.eig(J); k = np.argmax(ev.real); q = np.real(vec[:, k]/vec[8, k])
conv = {}
for name, amp in (('inside', 0.02), ('outside', 2.2)):
    ts = np.linspace(0, 700, 7001); sol = fm.integrate(amp*q, 700, t_eval=ts); X = fm.x0[:, None] + fm.P @ sol.y
    assert X.min() > 0
    conv[name] = dict(t=list(map(float, ts)), S3=list(map(float, X[3])), D1=list(map(float, X[9])), F=list(map(float, X[5])), S0=list(map(float, X[0])))
out['convergence_r1'] = conv

# relaxation path J_eps at r=r_A and at r=1.6 (stable side): leading real part versus eps
relax = []
for r in (rA, 1.0):
    m = witness('A', sp.Rational(str(round(r, 12)))); Jm = np.array(m.jacobian().tolist(), dtype=float)
    row = []
    for e in np.geomspace(0.05, 1.0099, 120):
        Je = Jm.copy(); Je[3:, :] /= e
        row.append([float(e), float(np.max(np.linalg.eigvals(Je).real))])
    relax.append(dict(r=float(r), curve=row))
L, M, A = [np.array(b.tolist(), dtype=float) for b in witness('A', sp.Rational(1)).blocks()]
out['relaxation'] = relax
out['static_eigs'] = sorted(float(v.real) for v in np.linalg.eigvals(L @ np.linalg.solve(A, M)))

# frequency response of the complex block: H(i w) versus H(0), largest singular value, at r=r_A
mA_ = witness('A', sp.Rational(str(round(rA, 12)))); L, M, A = [np.array(b.tolist(), dtype=float) for b in mA_.blocks()]
ws = np.geomspace(1e-3, 1e3, 400)
out['kernel'] = dict(w=list(map(float, ws)), sv=[float(np.linalg.svd(L @ np.linalg.solve(1j*w*np.eye(6) + A, M), compute_uv=False)[0]) for w in ws],
                     relax_rates=sorted(float(v.real) for v in np.linalg.eigvals(A)))
(ROOT/'figures').mkdir(exist_ok=True)
(ROOT/'figures'/'numerical_data.json').write_text(json.dumps(out))
print('saved')
