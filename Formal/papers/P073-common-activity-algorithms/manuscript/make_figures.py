"""Vector figure for the paper (exact formulas only; no simulated data).

Writes figures/cycle.pdf.  The other figures are TikZ in main.tex.
"""
from pathlib import Path
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent
(ROOT/'figures').mkdir(exist_ok=True)
plt.rcParams.update({'font.size': 10, 'pdf.fonttype': 42, 'font.family': 'DejaVu Sans',
                     'mathtext.fontset': 'cm'})
BLUE, OCHRE, GREY = '#264764', '#977133', '#8a8a8a'

fig, axes = plt.subplots(1, 3, figsize=(10.2, 3.05))

# (a) least-root jump for the unit edge at t = 1/100
t = .01
x = np.linspace(.04, .24, 400)
cyc = (-1 + np.sqrt(1 + 8*((x + 2*x*x)/3 + 2*t)))/2
alpha = (5 - math.sqrt(13))/10
ax = axes[0]
ax.plot(x, cyc, color=BLUE, label=r'$T_c(x)$')
ax.plot(x, x, color=GREY, ls='--', label=r'$x$')
ax.scatter([alpha], [alpha], color=OCHRE, zorder=4)
ax.scatter([.1], [(-1 + math.sqrt(1 + 8*((.1 + .02)/3 + 2*t)))/2], color=BLUE, s=16, zorder=4)
ax.annotate(r'$P_u=0.1$', xy=(.1, .1083), xytext=(.047, .165),
            arrowprops=dict(arrowstyle='->', color='#555555'), fontsize=9)
ax.annotate(r'$\alpha=(5-\sqrt{13})/10$', xy=(alpha, alpha), xytext=(.122, .055),
            arrowprops=dict(arrowstyle='->', color=OCHRE), fontsize=9)
ax.set(xlabel=r'seed activity $x$', ylabel='cycle value', title=r'(a) forced jump, $t=1/100$')
ax.legend(frameon=False, fontsize=9, loc='upper left')

# (b) Kleene iteration approaches alpha but never reaches it
ax = axes[1]
z = .1; its = [z]
for _ in range(40):
    z = (-1 + math.sqrt(1 + 8*((z + 2*z*z)/3 + 2*t)))/2
    its.append(z)
ax.semilogy(range(len(its)), [alpha - v for v in its], color=BLUE, marker='o', ms=2.5, lw=.8)
ax.set(xlabel='iteration $n$', ylabel=r'$\alpha-T_c^{\,n}(P_u)$',
       title='(b) plain iteration never lands')

# (c) root branches of the unit edge in the margin
ax = axes[2]
tt = np.linspace(0, 1/48, 600)
ax.plot(tt, (1 - np.sqrt(np.maximum(0, 1 - 48*tt)))/2, color=BLUE)
ax.plot(tt, (1 + np.sqrt(np.maximum(0, 1 - 48*tt)))/2, color=BLUE)
ax.scatter([1/48], [.5], color=OCHRE, zorder=4)
ax.annotate('double root\n$t=1/48$', xy=(1/48, .5), xytext=(.0085, .43),
            arrowprops=dict(arrowstyle='->', color=OCHRE), fontsize=9)
ax.text(.004, .9, r'$\rho_2(t)$', fontsize=9); ax.text(.004, .13, r'$\rho_1(t)$', fontsize=9)
ax.set(xlabel=r'margin $t$', ylabel='fixed seed', title=r'(c) branches of $x(1-x)=12t$',
       xlim=(0, .0225), ylim=(0, 1))
for ax in axes:
    ax.spines[['top', 'right']].set_visible(False)
    ax.tick_params(labelsize=8)
fig.tight_layout(w_pad=1.6)
fig.savefig(ROOT/'figures'/'cycle.pdf')
print('PASS: figures/cycle.pdf')
