"""Numerical (non-certified) estimate of the smallest linear-law stock for the
1.004 s mission from the prepared centre p, and the service lifetime at 120 microM."""
import json
import numpy as np
from pathlib import Path
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import depleted_tube as dt
p = np.array([float(x) for x in dt.P0])
R1 = lambda x: 375*(30-x)/(87.3-x)
def f(u, s):
    x, z, e1, e2, zt, h, w, v = u
    g = 371.56-2*z-e2; e0 = 50-e1-e2; y = .505-zt; r = 19.096-h-w-v
    HG = .21*e0; HT = 2.1*y*v; p1 = .04*g*e1; p2 = 10*g*e2; sG = 3.2*x*(z-1.78); sT = 20*x*(zt-.075)
    return np.array([s*R1(x)-sG-sT, p2-sG, HG-p1, p1-p2, HT-sT, .4*r+.003*w-.00072*h-15*h, .00072*h-.003*w, 15*h-HT])
def run(V, T):
    return solve_ivp(lambda t, U: np.r_[f(U[:8], .12-U[8]/V), (.12-U[8]/V)*R1(U[0])], (0, T), np.r_[p, 0.],
                     method='Radau', rtol=1e-11, atol=1e-13, dense_output=True)
HTend = lambda V: (lambda U: 2.1*(.505-U[4])*U[7])(run(V, 1.004).y[:, -1]) - 4
Vstar = brentq(HTend, 500, 1000, xtol=1e-6)
sol = run(1000., 3.); ts = np.linspace(.01, 3, 30001); U = sol.sol(ts); ht = 2.1*(.505-U[4])*U[7]
life = ts[np.argmax(ht < 4)]
out = dict(evidence='NUMERICAL_NOT_CERTIFIED', threshold_V=Vstar, threshold_Q0=.12*Vstar, lifetime_Q120_seconds=float(life))
(Path(dt.DATA)/'donor_threshold_numeric.json').write_text(json.dumps(out, indent=1)+'\n'); print(out)
