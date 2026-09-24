"""Vector figures from the saved exact data (run check_paper.py and diagnostics.py first)."""
import json
from fractions import Fraction as Fr
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import mpmath as mp
import check_paper as cp

HERE = Path(__file__).resolve().parent
FIG = HERE / 'figures'
FIG.mkdir(exist_ok=True)
rep = json.loads((HERE / 'check_paper_report.json').read_text())
diag = json.loads((HERE / 'data' / 'diagnostics.json').read_text())
plt.rcParams.update({'font.family': 'DejaVu Serif', 'font.size': 11, 'axes.spines.top': False,
                     'axes.spines.right': False, 'pdf.fonttype': 42, 'mathtext.fontset': 'dejavuserif'})
BLUE, ORANGE, GREY = '#23648a', '#c45e26', '#8a8a8a'

# ------------------------------------------------------------------ Figure 2
fig, ax = plt.subplots(1, 2, figsize=(10, 3.7))
n = np.arange(2, 13)
lo = np.maximum(n, np.floor((2.0 ** (n - 2) + n) / 2))
lo[n == 3] = 4
ax[0].fill_between(n, lo, 2.0 ** n, color='#d8e5ef', label='proved interval for $C_n$')
ax[0].plot(n, 2.0 ** n, '--', color=BLUE, label='upper bound $2^n$')
ax[0].plot(n, lo, 'o-', color=BLUE, ms=4, label='constructive lower bound')
ax[0].plot(n, n, 's-', color=ORANGE, ms=4, label='square balanced: exactly $n$')
ax[0].set_yscale('log', base=2)
ax[0].set_xlabel('number of sites $n$')
ax[0].set_ylabel('stable-equilibrium capacity')
ax[0].legend(fontsize=9, loc='upper left', frameon=False)
ax[0].set_title('(a) capacity bounds', fontsize=11)
reads = rep['final_normalized_readouts']
err = rep['final_min_normalized_gap'] / 8
for i, r in enumerate(reads):
    ax[1].errorbar(r, i + 1, xerr=err, fmt='o', capsize=4, color=BLUE, ms=5)
    ax[1].text(r + 0.03, i + 1.12, f'{r:.4f}' if i else r'$3.3\times10^{-21}$', fontsize=9)
unst = [float(e['normalized_readout']) for e in diag['equilibria'] if e['unstable_eigenvalues']]
ax[1].plot(unst, [0.4] * len(unst), 'x', color=GREY, ms=6)
ax[1].text(unst[-1] + 0.03, 0.33, 'unstable equilibria', fontsize=9, color=GREY)
ax[1].set_yticks(range(1, 5), ['label 1', 'label 2', 'label 3', 'label 4'])
ax[1].set_ylim(0, 4.6)
ax[1].set_xlim(-0.05, 0.85)
ax[1].set_xlabel(r'readout $R/S_{\mathrm{T}}$')
ax[1].set_title('(b) readouts of the four-label source', fontsize=11)
fig.tight_layout()
fig.savefig(FIG / 'capacity_readout.pdf')
plt.close(fig)

# ------------------------------------------------------------------ Figure 3
mp.mp.dps = 60
_, tt = cp.tree_weights()
iface = cp.load('postproof_candidate_interface.json')
p, q = [Fr(x) for x in iface['p']], [Fr(x) for x in iface['q']]
src = cp.Source(p, q, tt)
mpq = lambda f: mp.mpf(f.numerator) / f.denominator


def total(z):
    z = mp.mpf(z)
    lv = mp.mpf(1)
    for j in range(1, 7):
        lv *= (z - j)
    tau = [mp.polyval(c, z) for c in src.tcoef]
    A = sum(tau)
    B = sum(mpq(p[i]) * tau[a] for i, (a, b) in enumerate(cp.EDGES))
    D = sum(mpq(q[i]) * tau[b] for i, (a, b) in enumerate(cp.EDGES)) / z
    s = (10 - z) / (z * lv)
    F = lv / (B - z * D)
    return s * A + s * z * F * (B + D), s * A


fig, ax = plt.subplots(figsize=(8.2, 3.9))
for a_, b_ in [(0, 1), (2, 3), (4, 5), (6, 10)]:
    if a_ == 0:
        us = np.concatenate([np.logspace(-9, -1, 160), np.linspace(0.1, 1 - 1e-13, 300), 1 - np.logspace(-2, -13, 120)])
    elif b_ == 10:
        us = np.concatenate([a_ + np.logspace(-13, -2, 120), np.linspace(a_ + 0.01, 9.9999, 400)])
    else:
        us = np.concatenate([a_ + np.logspace(-13, -2, 120), np.linspace(a_ + 0.01, b_ - 0.01, 300), b_ - np.logspace(-2, -13, 120)])
    us = np.unique(us)
    g = [float(mp.log10(total(x)[0])) for x in us]
    ax.plot(us, g, color=BLUE, lw=1.4)
    ax.axvspan(a_, b_, color='#eef3f7', zorder=0)
ax.axhline(np.log10(cp.ST), color=ORANGE, lw=1, ls='--')
ax.text(8.1, np.log10(cp.ST) + 0.25, r'$S_{\mathrm{T}}=264\,490\,005\,424$', color=ORANGE, fontsize=9)
for e in diag['equilibria']:
    z = float(e['u'])
    st = e['unstable_eigenvalues'] == 0
    ax.plot([z], [np.log10(cp.ST)], 'o' if st else 'x', color=BLUE if st else GREY, ms=7 if st else 7, mew=1.6, zorder=5)
ax.plot([4.1, 4.2], [np.log10(rep['free_substrate_lower'])] * 2, color='k', lw=2.2)
ax.annotate('free substrate $>1.49\\times10^{11}$\non $[4.1,4.2]$', xy=(4.15, np.log10(rep['free_substrate_lower'])),
            xytext=(5.15, 8.3), fontsize=8.5, arrowprops=dict(arrowstyle='-', lw=0.6))
ax.set_ylim(5.4, 14.5)
ax.set_xlim(-0.15, 10.1)
ax.set_xlabel(r'free-enzyme ratio $u=E/F$')
ax.set_ylabel(r'$\log_{10}$ of the substrate total $g(u)$')
fig.tight_layout()
fig.savefig(FIG / 'equilibrium_curve.pdf')
plt.close(fig)

# ------------------------------------------------------------------ Figure 4
fig, ax = plt.subplots(1, 2, figsize=(10, 3.6))
recs = [('original source, global bound', 'physical_original_global', '#a4bac9'),
        ('original source, local bound', 'physical_original_local', '#598daa'),
        ('final source, local bound', 'physical_final_local', ORANGE)]
for name, key, col in recs:
    ax[0].scatter(rep[key]['log10_trec_s'], rep[key]['log10_substrate'], s=60, color=col, label=name, zorder=3)
ax[0].set_xlabel(r'$\log_{10}$ certified recovery time (s)')
ax[0].set_ylabel(r'$\log_{10}$ sufficient substrate molecules')
ax[0].legend(fontsize=9, frameon=False, loc='upper left')
ax[0].set_xlim(30, 40)
ax[0].set_ylim(105, 150)
ax[0].set_title('(a) certified sufficient resources', fontsize=11)
cont = cp.load('postproof_continuation.json')
k = np.array([10.0, 100.0])
decay = np.array([-float(r['labels'][2]['maximum_real']) for r in cont[-2:]])
ax[1].loglog(k, decay, 'o-', color=BLUE, label='full Jacobian (diagnostic)')
ax[1].loglog(k, decay[0] * (k / k[0]) ** -2, '--', color=ORANGE, label=r'$\kappa^{-2}$ reference')
ax[1].set_xlabel(r'coefficient $\kappa$ of the positive kernel vector')
ax[1].set_ylabel('weakest decay rate (model clock)')
ax[1].legend(fontsize=9, frameon=False)
ax[1].set_title('(b) loading slows restoration', fontsize=11)
fig.tight_layout()
fig.savefig(FIG / 'cost.pdf')
plt.close(fig)
print('figures written; kappa diagnostic ratio', decay[0] / decay[1])
