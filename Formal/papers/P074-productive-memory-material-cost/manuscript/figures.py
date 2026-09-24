"""Regenerate the three vector figures from the exact data files.

Run from the package directory:  python figures.py
Needs matplotlib only; all inputs are read from data/*.json.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
DATA = HERE / 'data'
FIG = HERE / 'figures'
FIG.mkdir(exist_ok=True)

# Categorical palette, fixed order, validated for CVD separation, chroma,
# lightness band and contrast against a white surface.
C_BAL, C_DIS, C_REL = '#1b4f9c', '#c2570f', '#6a3d9a'
INK, MUTED = '#1a1a1a', '#6b6b6b'
SCALE = 2 ** 31

plt.rcParams.update({
    'font.family': 'serif', 'font.size': 9, 'axes.labelsize': 9,
    'axes.titlesize': 9.5, 'legend.fontsize': 8, 'xtick.labelsize': 8,
    'ytick.labelsize': 8, 'axes.edgecolor': '#999999', 'axes.linewidth': 0.7,
    'xtick.color': MUTED, 'ytick.color': MUTED, 'text.color': INK,
    'axes.labelcolor': INK, 'grid.color': '#dddddd', 'grid.linewidth': 0.5,
    'legend.frameon': False, 'pdf.fonttype': 42, 'savefig.bbox': 'tight',
    'savefig.pad_inches': 0.02,
})


def style(ax):
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.grid(True, axis='y', zorder=0)
    ax.set_axisbelow(True)


# ---------------------------------------------------------------- figure 1 --
def support_frontier():
    d = json.loads((DATA / 'frontier_support.json').read_text())
    fig, ax = plt.subplots(figsize=(5.4, 3.1))
    style(ax)

    bal = [(r['K'], 1 - r['upper'] / SCALE, 1 - r['lower'] / SCALE) for r in d['nominal_table']]
    unt = [(r['K'], 1 - r['upper'] / SCALE, 1 - r['lower'] / SCALE)
           for r in d['untied_vertex']['rows']]

    for rows, col, mk, lab in ((bal, C_BAL, 'o', r'balanced, $\kappa_d=\kappa_r=10$'),
                               (unt, C_DIS, 's', r'dissociation-favoured, $(\kappa_d,\kappa_r)=(20,10)$')):
        ks = [r[0] for r in rows]
        ax.plot(ks, [r[1] for r in rows], marker=mk, ms=3.4, lw=1.2, color=col,
                label=lab, zorder=3, markeredgewidth=0)

    ax.axhline(1e-3, color=INK, lw=0.9, ls=(0, (4, 3)), zorder=2)
    ax.text(15.3, 1.22e-3, 'allowed failure $10^{-3}$', fontsize=7.6, color=INK, va='bottom')

    for K, col, txt in ((32, C_BAL, r'$K=32$'), (42, C_DIS, r'$K=42$')):
        row = next(r for r in (bal + unt) if r[0] == K
                   and (col == C_BAL) == (r in bal))
        ax.plot([K], [row[2]], marker='*', ms=11, color=col, zorder=5, markeredgewidth=0)
        ax.annotate(txt, (K, row[2]), textcoords='offset points', xytext=(2, -13),
                    fontsize=8, color=col)

    ax.set_yscale('log')
    ax.set_xlabel('material budget $K$')
    ax.set_ylabel('worst-start failure probability')
    ax.set_xlim(14.2, 43.5)
    ax.set_ylim(2e-4, 1.0)
    ax.legend(loc='upper right', handlelength=1.8)
    fig.savefig(FIG / 'support_frontier.pdf')
    plt.close(fig)


# ---------------------------------------------------------------- figure 2 --
def proportion_frontier():
    e = json.loads((DATA / 'proportion_extras.json').read_text())
    fig, ax = plt.subplots(figsize=(5.4, 3.1))
    style(ax)

    L = [r['L'] for r in e['scaling']]
    N = [r['N'] for r in e['scaling']]
    ax.plot(L, N, marker='o', ms=4.2, lw=1.3, color=C_BAL, zorder=4,
            markeredgewidth=0, label='exact frontier $N(\\delta)$')

    # cascade prediction 20 z_delta^2, z the standard normal upper quantile
    def zq(p):
        lo, hi = 0.0, 12.0
        for _ in range(200):
            mid = (lo + hi) / 2
            if 0.5 * math.erfc(mid / math.sqrt(2)) > p:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2

    xs = [math.log(10 ** k) for k in range(2, 8)]
    ax.plot(xs, [20 * zq(math.exp(-x)) ** 2 for x in xs], lw=1.3, ls=(0, (5, 2.5)),
            color=C_REL, zorder=3, label=r'cascade prediction $20\,z_\delta^{2}$')

    ax.plot([math.log(2000)], [414], marker='D', ms=6, color=C_DIS, zorder=5,
            markeredgewidth=0)
    ax.annotate('reference construction $\\mathcal{R}$\n(414 core units)', (math.log(2000), 414),
                textcoords='offset points', xytext=(-6, 8), fontsize=7.6,
                color=C_DIS, ha='right')
    ax.plot([math.log(2000)], [253], marker='*', ms=12, color=C_BAL, zorder=6,
            markeredgewidth=0)
    ax.annotate('frontier 253', (math.log(2000), 253), textcoords='offset points',
                xytext=(7, -10), fontsize=7.6, color=C_BAL)

    ax.set_xlabel(r'$\ln(1/\delta)$')
    ax.set_ylabel('minimum core mass $N$')
    ax.set_xlim(3.9, 17.2)
    ax.set_ylim(60, 620)
    ax.legend(loc='upper left', handlelength=2.2)
    fig.savefig(FIG / 'proportion_frontier.pdf')
    plt.close(fig)


# ---------------------------------------------------------------- figure 3 --
def branching():
    b = json.loads((DATA / 'branching_mechanism.json').read_text())
    rows = b['rows']

    def get(kd, kr, start):
        return next(r for r in rows if r['kappa_d'] == kd and r['kappa_r'] == kr
                    and r['start'] == start)

    settings = [((20, 10), C_DIS, 'dissociation\n(20, 10)'),
                ((10, 10), C_BAL, 'balanced\n(10, 10)'),
                ((10, 20), C_REL, 'release\n(10, 20)')]

    fig, (axL, axR) = plt.subplots(1, 2, figsize=(6.5, 2.85))
    for ax in (axL, axR):
        style(ax)

    # left: the two failure modes at the worst admitted start of each setting
    width, xs = 0.34, [0, 1, 2]
    for i, (kk, col, lab) in enumerate(settings):
        worst = min((get(*kk, s) for s in ([31, 0, 0], [1, 0, 0], [0, 1, 0])),
                    key=lambda r: r['success'])
        axL.bar(xs[i] - width / 2, worst['quota_failure'], width, color=col, zorder=3)
        axL.bar(xs[i] + width / 2, worst['partition_failure'], width, color=col,
                zorder=3, alpha=0.45, hatch='////', edgecolor=col, linewidth=0)
    axL.set_yscale('log')
    axL.axhline(1e-3, color=INK, lw=0.9, ls=(0, (4, 3)), zorder=2)
    axL.set_xticks(xs)
    axL.set_xticklabels([s[2] for s in settings])
    axL.set_ylabel('failure probability')
    axL.set_ylim(1e-9, 0.2)
    axL.set_title('(a) failure at the worst admitted start', loc='left')
    axL.bar(0, 0, 0, color=MUTED, label='missed product quota')
    axL.bar(0, 0, 0, color=MUTED, alpha=0.45, hatch='////', edgecolor=MUTED,
            linewidth=0, label='lost daughter after quota')
    axL.legend(loc='upper right', handlelength=1.4)

    # right: the terminal trade-off that produces it
    for kk, col, lab in settings:
        r = get(*kk, [31, 0, 0])
        axR.plot([r['mean_product']], [r['mean_R']], marker='o', ms=7, color=col,
                 zorder=4, markeredgewidth=0)
        axR.annotate(lab.replace('\n', ' '), (r['mean_product'], r['mean_R']),
                     textcoords='offset points', xytext=(6, 4), fontsize=7.6, color=col)
    axR.grid(True, axis='x')
    axR.set_xlabel(r'terminal $\mathbb{E}[\,$product$\,]$')
    axR.set_ylabel(r'terminal $\mathbb{E}[\,$carriers$\,]$')
    axR.set_xlim(6.5, 15.5)
    axR.set_ylim(17.5, 24.8)
    axR.set_title('(b) what the complex trades', loc='left')

    fig.tight_layout(w_pad=2.0)
    fig.savefig(FIG / 'branching.pdf')
    plt.close(fig)


if __name__ == '__main__':
    support_frontier()
    proportion_frontier()
    branching()
    print('wrote', *(p.name for p in sorted(FIG.glob('*.pdf'))))
