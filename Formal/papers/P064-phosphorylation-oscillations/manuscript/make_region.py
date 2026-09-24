"""Numerical (N) two-parameter stability map of witness A at fixed rate constants (r = 1):
the equilibrium continued from x*_A over a grid of enzyme totals, with S_T fixed.
Writes figures/region_data.json.  Not a proof input."""
import json, heapq
from pathlib import Path
import numpy as np
import sympy as sp
from phos import witness
from numerics import FloatModel

ROOT = Path(__file__).resolve().parent
R_VALUE = sp.Integer(1)
fm = FloatModel(witness('A', R_VALUE)); base = fm.x0.copy()
ET0, FT0 = 4.76, 27.58
scales = np.geomspace(0.5, 2.0, 121)
nE = nF = len(scales); c0 = nE//2


def solve_eq(dE, dF, y):
    fm.x0 = base.copy(); fm.x0[4] += dE; fm.x0[5] += dF
    for _ in range(80):
        f = fm.F(0, y); nf = np.max(np.abs(f))
        if nf < 1e-13: break
        step = np.linalg.solve(fm.DF(0, y), f); lam_ = 1.0
        while lam_ > 1e-4:                      # damped Newton, keeping the state positive
            yn = y - lam_*step
            if np.min(fm.species(yn)) > 0 and np.max(np.abs(fm.F(0, yn))) < nf: break
            lam_ /= 2
        y = y - lam_*step
    ok = np.max(np.abs(fm.F(0, y))) < 1e-10 and np.min(fm.species(y)) > 0
    ev = np.linalg.eigvals(fm.DF(0, y)); k = np.argmax(ev.real)
    return ok, y, ev[k]


lead = np.full((nE, nF), np.nan); imag = np.full((nE, nF), np.nan)
sols = {}
heap = [(0, c0, c0, np.zeros(9))]; seen = {(c0, c0)}
while heap:
    dist, i, j, guess = heapq.heappop(heap)
    ok, y, lam = solve_eq(ET0*(scales[i] - 1), FT0*(scales[j] - 1), guess)
    if not ok: continue
    lead[i, j] = lam.real; imag[i, j] = abs(lam.imag); sols[(i, j)] = y.copy()
    for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        a, b = i + di, j + dj
        if 0 <= a < nE and 0 <= b < nF and (a, b) not in seen:
            seen.add((a, b)); heapq.heappush(heap, (abs(a - c0) + abs(b - c0), a, b, y.copy()))
for sweep in range(3):                           # retry failed cells from every solved neighbour
    for i in range(nE):
        for j in range(nF):
            if not np.isnan(lead[i, j]): continue
            for di in (-1, 0, 1):
                for dj in (-1, 0, 1):
                    g = sols.get((i + di, j + dj))
                    if g is None or not np.isnan(lead[i, j]): continue
                    ok, y, lam = solve_eq(ET0*(scales[i] - 1), FT0*(scales[j] - 1), g.copy())
                    if ok and np.max(np.abs(y - g)) < 2.0:
                        lead[i, j] = lam.real; imag[i, j] = abs(lam.imag); sols[(i, j)] = y.copy()
out = dict(r=float(R_VALUE), scales=list(map(float, scales)), ET0=ET0, FT0=FT0,
           lead=[[None if np.isnan(v) else float(v) for v in row] for row in lead],
           imag=[[None if np.isnan(v) else float(v) for v in row] for row in imag])
(ROOT/'figures'/'region_data.json').write_text(json.dumps(out))
print('solved cells', int(np.sum(~np.isnan(lead))), 'of', nE*nF, 'unstable-oscillatory cells', int(np.nansum((lead > 0) & (imag > 1e-6))),
      'unstable-real cells', int(np.nansum((lead > 0) & (imag <= 1e-6))))
