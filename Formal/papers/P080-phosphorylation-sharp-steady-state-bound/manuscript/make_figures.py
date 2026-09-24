"""Figures for the paper.  Curves are exact rational evaluations converted to float."""
import os
from fractions import Fraction as Q

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from phos_sharp import build, chart

HERE = os.path.dirname(os.path.abspath(__file__))
FIG = os.path.join(HERE, "figures")
os.makedirs(FIG, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif", "mathtext.fontset": "cm", "font.size": 9,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6,
})
BLUE, RED, GREY = "#1f4e79", "#b03a2e", "#777777"


def residual_curve(rec, lo, hi, npts):
    A, B, D, r = rec["A"], rec["B"], rec["D"], rec["r"]
    ST = rec["totals"][2]
    us = [lo + (hi - lo) * Q(i, npts) for i in range(npts + 1)]
    return ([float(u) for u in us],
            [float(chart(A, B, D, r, Q(2), u)[0] - ST) for u in us])


def panel(ax, n, r, lo, hi, scale, npts=900):
    xs = [Q(j + 2) for j in range(2 * n - 1)]
    rec = build(xs, Q(r))
    assert rec["positive"]
    uu, hh = residual_curve(rec, Q(lo), Q(hi), npts)
    hh = np.array(hh)
    ax.axhline(0, color=GREY, lw=0.6)
    ax.plot(uu, np.arcsinh(hh / scale), color=BLUE, lw=1.1)
    for j, st in enumerate(rec["states"]):
        stable = (j % 2 == 0)
        ax.plot([float(st["u"])], [0], "o", ms=4.5,
                mfc=BLUE if stable else "white", mec=BLUE if stable else RED, mew=1.0,
                zorder=5)
    ticks = [-10 ** k for k in (2, 1, 0)] + [0] + [10 ** k for k in (0, 1, 2)]
    ax.set_yticks([np.arcsinh(t) for t in ticks])
    ax.set_yticklabels([("%g" % t) for t in ticks])
    ax.set_xlabel(r"free-enzyme ratio $u=E/F$")
    return rec


fig, axes = plt.subplots(1, 2, figsize=(6.6, 2.7))
panel(axes[0], 3, 5, Q(3, 10), Q(447, 100), 1e-3)
axes[0].set_xticks([0.375, 1, 1.875, 3, 4.375])
axes[0].set_xticklabels(["3/8", "1", "15/8", "3", "35/8"])
axes[0].set_ylabel(r"$10^{3}\,[H(u)-S_{\mathrm{T}}]$  (arcsinh scale)")
axes[0].set_title(r"(a) $n=3$, $r=5$: five steady states", fontsize=9)
panel(axes[1], 5, 13, Q(3, 10), Q(1245, 100), 1e-6, npts=1400)
axes[1].set_xticks([0.375, 3, 6, 9.625, 12.375])
axes[1].set_xticklabels(["3/8", "3", "6", "77/8", "99/8"])
axes[1].set_ylabel(r"$10^{6}\,[H(u)-S_{\mathrm{T}}]$  (arcsinh scale)")
axes[1].set_title(r"(b) $n=5$, $r=13$: nine steady states", fontsize=9)
fig.tight_layout()
fig.savefig(os.path.join(FIG, "residuals.pdf"))
print("wrote figures/residuals.pdf")
