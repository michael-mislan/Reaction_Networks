"""Generate the three vector figures used by main.tex."""
import os
import sys
from fractions import Fraction as F
from pathlib import Path

for _k in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_k] = '1'

sys.path.insert(0, str(Path(__file__).resolve().parent))
from exact_engine import reserves, log_enclosure, upper  # noqa: E402

import numpy as np  # noqa: E402
import matplotlib  # noqa: E402
matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402

OUT = Path(__file__).resolve().parents[1] / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9, 'pdf.fonttype': 42})

BLUE, GREEN, GREY, RED = '#236183', '#27805c', '#8a8a8a', '#a33b3b'


def cp_s0(x):
    x = F(x)
    A = (x**4 + x**3 + x**2 + x + 1) * (3 * x**5 + 6 * x**4 + 9 * x**3 + 12 * x**2 + 8 * x + 4)
    Q = (3 * x**8 + 12 * x**7 + 30 * x**6 + 60 * x**5 + 98 * x**4
         + 137 * x**3 + 170 * x**2 + 159 * x + 66)
    return (1 - x) * Q / (4 * A), 4 * A * x**2 * (1 - x)**3 / 210


# ============================================================ Figure 1
fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.7), layout='constrained')
for ax in axs:
    ax.axis('off')
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
ax = axs[0]
ax.text(.5, .97, 'Admitted record: one retained branch', ha='center', fontsize=9.5, weight='bold')
pts = [(.10, .55), (.36, .55), (.64, .72), (.90, .72)]
for a, b in zip(pts, pts[1:]):
    ax.annotate('', b, a, arrowprops={'arrowstyle': '->', 'color': BLUE, 'lw': 1.8})
ax.annotate('', (.64, .26), (.36, .55), arrowprops={'arrowstyle': '->', 'color': GREY, 'ls': '--'})
ax.text(.68, .17, 'discarded sister\nand her descendants', ha='center', fontsize=8, color='#666')
for (xx, yy), lab in zip(pts, ['$P$', 'division', '$S$ or $T$', 'continue']):
    ax.text(xx, yy, lab, ha='center', va='center', fontsize=8.5,
            bbox={'boxstyle': 'round,pad=.32', 'fc': 'white', 'ec': BLUE})
ax.text(.5, .02, 'states, event labels, timestamps,\ndeath and censoring', ha='center', fontsize=8)

ax = axs[1]
ax.text(.5, .97, 'Decision-focused repair: a paired read', ha='center', fontsize=9.5, weight='bold')
ax.text(.13, .55, '$P$', ha='center', va='center', fontsize=8.5,
        bbox={'boxstyle': 'round,pad=.32', 'fc': 'white', 'ec': BLUE})
for yy, lab in [(.75, 'daughter 1'), (.35, 'daughter 2')]:
    ax.annotate('', (.44, yy), (.19, .55), arrowprops={'arrowstyle': '->', 'color': BLUE, 'lw': 1.8})
    ax.text(.53, yy, lab, ha='center', va='center', fontsize=8.5,
            bbox={'boxstyle': 'round,pad=.32', 'fc': 'white', 'ec': BLUE})
ax.annotate('', (.79, .55), (.70, .55), arrowprops={'arrowstyle': '->', 'color': GREEN})
ax.text(.88, .55, 'agree?\n$0/1$', ha='center', va='center', fontsize=8.5,
        bbox={'boxstyle': 'round,pad=.32', 'fc': '#e9f3ef', 'ec': GREEN})
ax.text(.5, .02, 'independent founders; conditional\nread errors declared, not assumed away',
        ha='center', fontsize=8)
fig.savefig(OUT / 'protocol.pdf')
plt.close(fig)

# ============================================================ Figure 2
fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.9), layout='constrained')
hs = np.linspace(1e-4, .30, 601)
xx = np.exp(-hs)
A = (xx**4 + xx**3 + xx**2 + xx + 1) * (3 * xx**5 + 6 * xx**4 + 9 * xx**3 + 12 * xx**2 + 8 * xx + 4)
Q = (3 * xx**8 + 12 * xx**7 + 30 * xx**6 + 60 * xx**5 + 98 * xx**4
     + 137 * xx**3 + 170 * xx**2 + 159 * xx + 66)
ct = (1 - xx) * Q / (4 * A)
axs[0].plot(hs, ct, color=BLUE, lw=1.6, label=r'exact boundary $c_{\rm p}(e^{-h})$')
axs[0].plot(hs, 7 * hs / 8, '--', color=GREY, lw=1.2, label=r'first order $7h/8$')
axs[0].axhline(.25, color='black', lw=.7)
axs[0].text(.005, .258, 'feasible ceiling $c=1/4$', fontsize=7.5)
axs[0].axvline(np.log(8 / 7), color=GREEN, ls=':', lw=1.2)
axs[0].text(np.log(8 / 7) + .005, .01, r'$h=\log\frac{8}{7}$', fontsize=7.5, color=GREEN)
h0 = -np.log(.801205)
axs[0].plot([h0], [.25], 'o', ms=4, color=RED)
axs[0].text(h0 - .005, .285, r'$h_0$', fontsize=8, color=RED, ha='right')
axs[0].set(xlabel='pulse length $h$ (model time)', ylabel='hidden-covariance threshold',
           ylim=(0, .38), xlim=(0, .30))
axs[0].legend(fontsize=7.5, loc='upper left', framealpha=.95)

cs = np.linspace(-.25, .25, 401)
xv = 7 / 8
Av = (xv**4 + xv**3 + xv**2 + xv + 1) * (3 * xv**5 + 6 * xv**4 + 9 * xv**3 + 12 * xv**2 + 8 * xv + 4)
s0v = 4 * Av * xv**2 * (1 - xv)**3 / 210
cpv = float(F(8967219299, 65423564404))
Dv = s0v * (cpv - cs)
hlo, hhi = log_enclosure(8, 7)
WAB = float(upper(reserves('AB', F(7, 8)), hlo, hhi))
WBA = float(upper(reserves('BA', F(7, 8)), hlo, hhi))
Vsum = float(F(15317159, 150994944))
ax = axs[1]
ax.fill_between(cs, (Dv - .001 * Vsum) * 1e3, (Dv + .001 * Vsum) * 1e3,
                color=GREY, alpha=.30, lw=0,
                label=r'occupation band, $\varepsilon\leq 10^{-3}$')
ax.fill_between(cs, (Dv - .01 * WAB) * 1e3, (Dv + .01 * WBA) * 1e3,
                color=BLUE, alpha=.30, lw=0,
                label=r'sensitivity band, $\varepsilon\leq 10^{-2}$')
ax.plot(cs, Dv * 1e3, color=BLUE, lw=1.6, label=r'exact reference, $\varepsilon=0$')
ax.axhline(0, color='black', lw=.7)
ax.axvline(cpv, color=GREEN, ls=':', lw=1.2)
ax.plot([-.2, .2], [s0v * (cpv + .2) * 1e3, s0v * (cpv - .2) * 1e3], 'o', ms=4, color=RED)
ax.text(-.243, .20, r'$AB$ preferred', fontsize=7.5, color='#444')
ax.text(.243, -.47, r'$BA$ preferred', fontsize=7.5, color='#444', ha='right')
ax.set(xlabel='founder sister covariance $c$',
       ylabel=r'$(F_{AB}-F_{BA})\times 10^{3}$', xlim=(-.25, .25), ylim=(-.62, 1.55))
ax.legend(fontsize=7.2, loc='upper right', framealpha=.95)
fig.savefig(OUT / 'boundary.pdf')
plt.close(fig)

# ============================================================ Figure 3
denoms = sorted({int(round(1 / (1 - v))) for v in np.exp(-np.logspace(np.log10(2e-3), np.log10(.22), 60))})
rows = []
for d in denoms:
    if d < 4:
        continue
    x = F(d - 1, d)
    lo, hi = log_enclosure(d, d - 1)
    cp, s0 = cp_s0(x)
    wab = upper(reserves('AB', x), lo, hi)
    wba = upper(reserves('BA', x), lo, hi)
    vsum = reserves('AB', x, sharp=False)[0] + reserves('BA', x, sharp=False)[0]
    row = {'h': float(hi), 'cp': float(cp)}
    for lab, cw in [('14', F(1, 4)), ('15', F(1, 5))]:
        if cp >= cw:
            row['new' + lab] = row['old' + lab] = np.nan
        else:
            row['new' + lab] = float(min(s0 * (cp + cw) / wab, s0 * (cw - cp) / wba))
            row['old' + lab] = float(min(s0 * (cp + cw), s0 * (cw - cp)) / vsum)
    rows.append(row)
hh = np.array([r['h'] for r in rows])
fig, ax = plt.subplots(figsize=(6.6, 3.0), layout='constrained')
ax.loglog(hh, [r['new14'] for r in rows], color=BLUE, lw=1.7,
          label=r'this paper, $c=\pm\frac{1}{4}$')
ax.loglog(hh, [r['new15'] for r in rows], color=BLUE, lw=1.4, ls='--',
          label=r'this paper, $c=\pm\frac{1}{5}$')
ax.loglog(hh, [r['old14'] for r in rows], color=GREY, lw=1.5,
          label=r'occupation certificate, $c=\pm\frac{1}{4}$')
ax.loglog(hh, [r['old15'] for r in rows], color=GREY, lw=1.2, ls='--',
          label=r'occupation certificate, $c=\pm\frac{1}{5}$')
ax.axhline(1, color='black', lw=.7)
ax.text(2.4e-3, .30, r'$\varepsilon=1$: descendants divide as fast as the founder',
        fontsize=7.5, color='#444')
ax.axvline(np.log(8 / 7), color=GREEN, ls=':', lw=1.1)
ax.text(np.log(8 / 7) * 1.06, 2e-4, r'$h=\log\frac{8}{7}$', fontsize=7.5, color=GREEN)
ax.axvline(np.log(50 / 49), color=RED, ls=':', lw=1.1)
ax.text(np.log(50 / 49) * .94, 2e-4, r'$h=\log\frac{50}{49}$', fontsize=7.5,
        color=RED, ha='right')
ax.set(xlabel='pulse length $h$ (model time)',
       ylabel=r'certified descendant division rate $\varepsilon_\star$')
ax.legend(fontsize=7.5, loc='lower left', framealpha=.95)
ax.set_ylim(8e-5, 3e1)
ax.grid(True, which='both', lw=.3, alpha=.4)
fig.savefig(OUT / 'epsilon.pdf')
plt.close(fig)

print('three vector figures written to', OUT)
