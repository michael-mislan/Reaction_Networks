r"""Figure: the top-anchor product of Theorem 2 is asymptotically exact at high renewal.

(a) r_eff^d * P_K(tau_H <= T), computed from the killed Kolmogorov equation at 60
    decimal digits (float64 suffers catastrophic cancellation here), against
    renewal, for three buffer sizes d = K - h_min.  Each curve approaches the
    predicted constant (Km)^{d+1} T / d!, which is exactly the value of the
    Theorem-2 top-anchor product r_eff^d * K m T P_{K-1} for every r_eff.
(b) Relative slack of that bound, which decays like 1/r_eff.
"""
import json
from math import factorial
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

mp.mp.dps = 60
OUT = Path(r"E:\Erdos Problems\key_results\RAFs\Reserve_Capacity_Reliable_Eradication_arxiv\figures")
OUT.mkdir(parents=True, exist_ok=True)
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9, 'axes.titlesize': 10,
                     'axes.labelsize': 9, 'legend.fontsize': 8, 'axes.spines.top': False,
                     'axes.spines.right': False, 'pdf.fonttype': 42, 'savefig.bbox': 'tight'})
BLUE, ORANGE, GREEN, GRAY = '#185e83', '#c76c2f', '#36785b', '#5d6470'


def killed(K, hmin, r, m, T):
    """Exact P_K(tau_H <= T) for the constant logistic chain (7), started full."""
    st = list(range(hmin, K + 1))
    n = len(st)
    A = mp.zeros(n, n)
    for i, h in enumerate(st):
        lam = r * h * (1 - mp.mpf(h) / K)
        mu = m * h
        if i + 1 < n:
            A[i, i + 1] = lam
        if i - 1 >= 0:
            A[i, i - 1] = mu
        A[i, i] = -(lam + mu)        # mass leaving h_min downward is killed
    E = mp.expm(A * T)
    return 1 - mp.fsum([E[n - 1, j] for j in range(n)])


def anchor_bound(K, hmin, r, m, T):
    d = K - hmin
    return K * m * T * (K * m) ** d / (mp.mpf(r) ** d * factorial(d))


m, T = mp.mpf('0.5'), mp.mpf(2)
CASES = [(4, 3, BLUE), (4, 2, ORANGE), (5, 2, GREEN)]
rs = [mp.mpf(10) ** mp.mpf(x) for x in np.linspace(0.4, 5.0, 55)]
data = {'m': 0.5, 'T': 2.0, 'method': 'mpmath expm, 60 decimal digits', 'cases': []}

fig, ax = plt.subplots(1, 2, figsize=(6.4, 3.0), layout='constrained')
for K, hmin, col in CASES:
    d = K - hmin
    coef = float((K * m) ** (d + 1) * T / factorial(d))
    scaled, ratio = [], []
    for r in rs:
        p = killed(K, hmin, r, m, T)
        scaled.append(float(r ** d * p))
        ratio.append(float(anchor_bound(K, hmin, r, m, T) / p))
    lab = rf'$d={d}$  ($K={K}$, $h_{{\min}}={hmin}$)'
    ax[0].semilogx([float(r) for r in rs], scaled, color=col, label=lab)
    ax[0].axhline(coef, color=col, ls=':', lw=.9)
    ax[1].loglog([float(r) for r in rs], [v - 1 for v in ratio], color=col, label=lab)
    data['cases'].append({'K': K, 'hmin': hmin, 'd': d, 'coefficient': coef,
                          'r': [float(r) for r in rs], 'scaled': scaled, 'ratio': ratio})
    assert min(ratio) > 1, (K, hmin, min(ratio))
    print(f"  d={d}: coefficient {coef:.6g}; scaled at r=1e5 -> {scaled[-1]:.8f}; "
          f"min bound/probability = {min(ratio):.8f} (>1 everywhere)")

ax[0].set(xlabel=r'Effective renewal $r_{\mathrm{eff}}$',
          ylabel=r'$r_{\mathrm{eff}}^{\,d}\,\mathbb{P}_K(\tau_H\leq T)$',
          title=r'(a) Convergence to $(Km)^{d+1}T/d!$')
ax[0].set_ylim(0, 15)
ax[0].legend(frameon=False, loc='lower right')
ax[1].set(xlabel=r'Effective renewal $r_{\mathrm{eff}}$',
          ylabel=r'bound / probability $-\;1$',
          title=r'(b) Relative slack of the top-anchor bound')
ax[1].legend(frameon=False, loc='upper right')
fig.savefig(OUT / 'high_renewal.pdf')
fig.savefig(OUT / 'high_renewal.png', dpi=180)
plt.close(fig)
json.dump(data, open(OUT / 'high_renewal_data.json', 'w'), indent=1)
print("wrote", OUT / 'high_renewal.pdf')
