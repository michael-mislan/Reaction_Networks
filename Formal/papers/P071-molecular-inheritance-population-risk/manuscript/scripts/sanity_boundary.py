"""Floating-point sanity check of inequality (20): E_x K(t) against the proved bound."""
import numpy as np
from scipy.linalg import expm
from model import source, smooth_hazard
b, th, ell, psi, Lam, sig2 = .1, .055, .58, .145, .915, 1.07
worst = 0
for N in (8, 16, 32):
    st, ix, Q, D, _ = source(N); d = smooth_hazard(st, N)
    A = Q + b * (2 * D - np.eye(len(st))) - np.diag(d)
    c = np.array([(a - r) / N for a, r in st])
    # also check the second-moment generator bound  L c^2 <= 2 Lam c^2 + sig2/N
    Lg = Q + 2 * b * (D - np.eye(len(st)))
    assert np.all(Lg @ c**2 <= 2 * Lam * c**2 + sig2 / N + 1e-12)
    for t in (0.5, 1, 2, 5, 10, 20):
        m = expm(t * A) @ np.ones(len(st))
        bound = np.exp(-th * t) * (1 + ell * t * np.exp((psi + Lam) * t) * np.sqrt(c**2 + sig2 * t / N))
        assert np.all(m <= bound + 1e-12); worst = max(worst, float(np.max(m / bound)))
print("inequality (20) holds on all states; max ratio", worst)
