"""Figures for the compatibility paper.

Curves are numerical illustrations; shaded bands are the exact-arithmetic tube
enclosures stored in data/ (see depleted_tube.py).
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import depleted_tube as dt

root = Path(__file__).resolve().parents[1]
FIG = root / 'figures'
FIG.mkdir(exist_ok=True)
BLUE, ORANGE, AQUA, INK, MUTED = '#2a78d6', '#eb6834', '#1baf7a', '#0b0b0b', '#52514e'
plt.rcParams.update({'font.size': 8.5, 'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.edgecolor': MUTED, 'axes.labelcolor': INK, 'xtick.color': MUTED,
                     'ytick.color': MUTED, 'legend.frameon': False, 'lines.linewidth': 1.6,
                     'pdf.fonttype': 42, 'axes.titlesize': 9})

M = np.array([[float(x) for x in r] for r in dt.M])


def enclosure(name):
    c = json.loads((root / 'data' / f'{name}.json').read_text())
    ts = np.array([float(F(x)) for x in c['times']])
    ref = np.array([[float(F(x)) for x in r] for r in c['reference']])
    q = np.array([[float(F(x)) for x in r] for r in c['radii']])
    d = q @ np.abs(M).T
    lo = 2.1 * (.505 - ref[:, 4] - d[:, 4]) * (ref[:, 7] - d[:, 7])
    hi = 2.1 * (.505 - ref[:, 4] + d[:, 4]) * (ref[:, 7] + d[:, 7])
    Cb = np.array([float(F(x)) for x in c['donor_reference']])
    return ts, lo, hi, 2.1 * (.505 - ref[:, 4]) * ref[:, 7], Cb


out = {}

# --- recovery under the maintained source --------------------------------------------------
ts, lo, hi, mid, _ = enclosure('tube_nominal')
fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.55))
for a, tmax, scale, lab in ((ax[0], .010, 1e3, 'Time (ms)'), (ax[1], 1.004, 1, 'Time (s)')):
    m = ts <= tmax
    a.fill_between(ts[m] * scale, lo[m], hi[m], color=BLUE, alpha=.22, lw=0, label='Exact enclosure, 0.1% box')
    a.plot(ts[m] * scale, mid[m], color=BLUE, label='Trajectory from $p$ (numerical)')
    a.axhline(4, color=MUTED, lw=1, ls=':', label='Quota $q_T=4$')
    a.set(xlabel=lab, ylabel=r'Trx service $H_T$ ($\mu$M s$^{-1}$)')
ax[0].plot([0, 4, 4, 10], [3.91, 3.91, 4.01, 4.01], color=ORANGE, lw=1.3, ls='--',
           label=r'Lean-checked floors on all of $\mathcal{R}$')
ax[0].axvline(4, color=MUTED, lw=.8)
ax[0].text(4.15, 3.925, r'$\tau=4$ ms', color=MUTED, fontsize=8)
ax[0].set_ylim(3.89, 4.22)
hd, lb = ax[0].get_legend_handles_labels()
ax[1].legend(hd, lb, fontsize=7, loc='center right')
ax[1].axhline(4.01, color=ORANGE, lw=1.3, ls='--')
fig.tight_layout()
fig.savefig(FIG / 'recovery.pdf')
plt.close(fig)
out['recovery'] = dict(times=ts.tolist(), lower=lo.tolist(), upper=hi.tolist(), center=mid.tolist())

# --- repair clock ------------------------------------------------------------------------------
old = json.loads((root / 'data/repair_clock_pilots.json').read_text())
G, zG0, EG, T, zT0, ET = 371.56, 1.78, 50., .505, .075, 19.096
a_, b_, c_, kG, at, bt, ct, dtt, et, kT = .21, .04, 10., 3.2, .4, .00072, .003, 15., 2.1, 20.
SG, ST = G - 2 * zG0, T - zT0
rho = a_ * (1 / b_ + 1 / c_)
rhot = 1 / at + 1 / dtt + bt / (ct * dtt)


def proot(A, B, C):
    disc = np.sqrt(B * B + 4 * A * C)
    return 2 * C / (B + disc) if B >= 0 else (-B + disc) / (2 * A)


def response(x):
    g = proot(1, rho - SG + 2 * EG * a_ / (kG * x), SG * rho - EG * a_ / c_)
    y = proot(rhot * et, 1 - ST * rhot * et + ET * et / (kT * x), ST)
    return EG * a_ * g / (g + rho), ET * et * y / (1 + rhot * et * y)


xs = np.geomspace(.02, 29, 300)
jj = np.array([response(x) for x in xs])
fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.55))
ax[0].semilogx(xs, jj[:, 0], color=BLUE, label='GPx branch $j_G$')
ax[0].semilogx(xs, jj[:, 1], color=ORANGE, label='Trx branch $j_T$')
ax[0].axhline(10, color=BLUE, lw=.9, ls=':')
ax[0].axhline(4, color=ORANGE, lw=.9, ls=':')
ax[0].set(xlabel=r'Stationary NADPH $x$ ($\mu$M)', ylabel=r'Stationary service ($\mu$M s$^{-1}$)',
          title=r'Identical for every $\sigma>0$')
ax[0].legend(fontsize=7.5)
sig = np.geomspace(.01, 1, 50)
bound = np.log(.95 * 19.096 / (19.096 - 4 / (2.1 * .43))) / .003
ax[1].loglog(sig, bound / sig, color=AQUA, label='Necessary delay (analytic)')
pil = [d for d in old['pilots'] if d['name'].startswith('hyper_95pct_sigma_')]
ax[1].loglog([d['sigma'] for d in pil], [d['observed_last_crossing'] for d in pil], 'o', ms=5, color=INK,
             label='Observed quota crossing (numerical)')
ax[1].set(xlabel=r'Matched repair-rate multiplier $\sigma$', ylabel=r'Time to $H_T\geq4$ (s)',
          title='95% hyperoxidized preparation')
ax[1].legend(fontsize=7.5, loc='lower left')
fig.tight_layout()
fig.savefig(FIG / 'repair_clock.pdf')
plt.close(fig)
out['repair_clock'] = dict(bound_sigma1=bound,
                           pilots=[dict(sigma=d['sigma'], crossing=d['observed_last_crossing']) for d in pil])

# --- finite donor ----------------------------------------------------------------------------------
fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.5))
s0, delta, D = .12, 1e-6, 16 * 1.004
K = np.geomspace(1e-3, 1e3, 200)
Q0 = (D - K + np.sqrt((D - K) ** 2 + 4 * (s0 / delta) * K * D)) / 2
ax[0].axhline(1927680, color=MUTED, lw=1, ls='--', label='Linear law, fixed band')
ax[0].loglog(K, Q0, color=AQUA, label='Saturating law')
ax[0].plot([.01, 1], [200, 1500], 'o', ms=4.5, color=INK, label='Worked examples')
ax[0].axhline(120, color=BLUE, lw=1, ls='-.', label='Linear law, moving tube')
ax[0].set(xlabel=r'Donor affinity scale $K$ ($\mu$M)', ylabel=r'Certified sufficient stock ($\mu$M)')
ax[0].set_ylim(30, 3e10)
ax[0].legend(fontsize=6.3, loc='upper left')
smin = 0.11371267
for name, V, col in (('tube_Q120', 1000., BLUE), ('tube_Q60', 500., ORANGE)):
    ts, lo, hi, mid, Cb = enclosure(name)
    lab = r'$Q_0=%d\,\mu$M' % round(.12 * V)
    ax[1].fill_between(ts, lo, hi, color=col, alpha=.25, lw=0)
    ax[1].plot(ts, mid, color=col, label=lab)
    ax[2].plot(ts, .12 - Cb / V, color=col, label=lab)
    out[name] = dict(times=ts.tolist(), lower=lo.tolist(), upper=hi.tolist(), center=mid.tolist(),
                     s=(.12 - Cb / V).tolist())
ax[1].axhline(4, color=MUTED, lw=1, ls=':')
ax[1].text(.02, 4.015, 'quota', color=MUTED, fontsize=7.5)
ax[1].set(xlabel='Time (s)', ylabel=r'Trx service $H_T$ ($\mu$M s$^{-1}$)')
ax[1].set_ylim(3.5, 4.6)
ax[1].legend(fontsize=7.5, loc='lower left')
ax[2].axhline(smin, color=MUTED, lw=1, ls=':')
ax[2].text(.42, smin + .0008, r'stationary $s_{\min}$', color=MUTED, fontsize=7)
ax[2].set(xlabel='Time (s)', ylabel='Source scale $s=Q/V$')
ax[2].legend(fontsize=7.5, loc='lower left')
fig.tight_layout()
fig.savefig(FIG / 'donor.pdf')
plt.close(fig)
(root / 'data/figure_data.json').write_text(json.dumps(out) + '\n')
print('figures written')
