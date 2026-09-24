"""Vector figures for the manuscript.  Deterministic: fixed seed and fixed
rounded expected counts; no figure uses an unrecorded random draw."""
import json
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
from pathlib import Path
from fractions import Fraction as Q
from model import model, exp_law, extinction, strong_source, E_MARKER
from certkit import I, kl_interval, hoeffding_interval, evaluate

HERE = Path(__file__).resolve().parent
OUT = HERE / 'figures'; OUT.mkdir(exist_ok=True)
LF = Q(25, 4); LC = Q(6); NCAL = 100000
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9, 'axes.labelsize': 9,
                     'axes.titlesize': 9.5, 'legend.fontsize': 8, 'pdf.fonttype': 42,
                     'ps.fonttype': 42, 'axes.spines.top': False,
                     'axes.spines.right': False, 'savefig.bbox': 'tight'})
C = ['#236b8e', '#c0652e', '#4f865c', '#78518f']


def save(fig, name):
    fig.savefig(OUT / (name + '.pdf'))
    fig.savefig(OUT / (name + '.png'), dpi=150)
    plt.close(fig)


def fset(k, n, L, scheme):
    return kl_interval(Q(int(k), n), n, L) if scheme == 'kl' else hoeffding_interval(Q(int(k), n), n, L)


def cal_pair(scheme):
    return fset(10000, NCAL, LC, scheme), fset(85000, NCAL, LC, scheme)


def from_counts(counts, n, lam, scheme, method, cal):
    J = [[fset(counts[0, 0], n, LF, scheme), fset(counts[0, 1], n, LF, scheme)],
         [fset(counts[1, 0], n, LF, scheme), fset(counts[1, 1], n, LF, scheme)]]
    mu = fset(counts[1].sum(), n, LF, scheme)
    return evaluate(J, mu, cal[0], cal[1], I(lam), method)


def rounded(m, lam, n):
    obs = exp_law(m, lam)[0]
    c = np.floor(n * obs).astype(np.int64)
    c[0, 2] += n - int(c.sum())
    return c


def induction(lam, n, scheme, method, cal):
    out = [from_counts(rounded(model(a), lam, n), n, lam, scheme, method, cal) for a in (.05, .85)]
    return None if any(x is None for x in out) else out[1] - out[0]


# ------------------------------------------------------------------ figure 1
def assay():
    fig, ax = plt.subplots(figsize=(7.1, 3.65))
    ax.set_xlim(0, 10); ax.set_ylim(-.25, 5); ax.axis('off')

    def box(x, y, w, h, t, c='#eaf2f6'):
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle='round,pad=0.08',
                                    facecolor=c, edgecolor='#426576', lw=1))
        ax.text(x + w / 2, y + h / 2, t, ha='center', va='center', fontsize=9)

    def arrow(a, b):
        ax.annotate('', xy=b, xytext=a, arrowprops=dict(arrowstyle='->', color='#426576', lw=1.2))

    box(.3, 3.45, 2.1, 1.05, 'Founder\ninitial marker\nand treatment arm')
    box(3.25, 3.45, 3.2, 1.05, 'Competing stop\nindependent Exp($\\lambda$) deadline\nor first division / death')
    arrow((2.5, 3.98), (3.15, 3.98))
    box(.3, 1.5, 2.1, 1, 'Deadline\nendpoint marker')
    box(3.25, 1.5, 2.1, 1, 'Death\nretain flag', c='#f6eee7')
    box(6.2, 1.5, 3.15, 1, 'Division\njoint daughter records')
    for x in (1.35, 4.3, 7.77):
        arrow((4.85, 3.35), (x, 2.62))
    box(6.0, 0, 3.55, .92, 'Daughter at known delay $\\tau$:\nmarker if no division or death;\notherwise interruption flag')
    arrow((7.77, 1.4), (7.77, 1.03))
    ax.text(.3, .45, 'All founders count.\nNo survivor conditioning.\nSister birth states may be correlated.',
            fontsize=9, va='center')
    save(fig, 'assay')


# ------------------------------------------------------------------ figure 2
def inference():
    fig, axs = plt.subplots(1, 3, figsize=(7.1, 2.7), layout='constrained')
    cap = 45.
    cal = cal_pair('kl'); calH = cal_pair('hoeffding')
    ns = (1000, 5000, 20000, 50000, 200000)
    rows = []
    for lam, col in zip((.25, .5, 1, 2), C):
        xs = []; ys = []
        for n in ns:
            ci = induction(lam, n, 'kl', 'cancelled', cal)
            rows.append(dict(panel='roots', lam=lam, n=n, interval=None if ci is None else ci.pair()))
            if ci is None:
                axs[0].plot(n, cap, 'x', color=col, ms=5)
            else:
                xs.append(n); ys.append(float(ci.width()))
        axs[0].plot(xs, ys, '-o', ms=3, color=col, label='$\\lambda=%g$' % lam)
    for lam, col in zip((.25, .5, 1, 2), C):
        laws = [exp_law(model(a), lam) for a in (.05, .85)]
        per = sum(x[4] for x in laws)
        xs = []; ys = []
        for budget in (5000, 20000, 50000, 200000):
            n = int(budget / per)
            ci = induction(lam, n, 'kl', 'cancelled', cal)
            rows.append(dict(panel='hours', lam=lam, budget=budget, n=n, used_hours=n * per,
                             interval=None if ci is None else ci.pair()))
            if ci is None:
                axs[1].plot(budget, cap, 'x', color=col, ms=5)
            else:
                xs.append(budget); ys.append(float(ci.width()))
        axs[1].plot(xs, ys, '-o', ms=3, color=col)
    styles = [('hoeffding', 'matrix', 'Hoeffding, direct inverse', '#8a8a8a', '--'),
              ('hoeffding', 'cancelled', 'Hoeffding, cancelled', '#c0652e', '--'),
              ('kl', 'matrix', 'Chernoff, direct inverse', '#4f865c', '-'),
              ('kl', 'cancelled', 'Chernoff, cancelled', '#236b8e', '-')]
    for scheme, method, lab, col, ls in styles:
        cc = cal if scheme == 'kl' else calH
        xs = []; ys = []
        for n in ns:
            ci = induction(1, n, scheme, method, cc)
            rows.append(dict(panel='methods', scheme=scheme, method=method, n=n,
                             interval=None if ci is None else ci.pair()))
            if ci is None:
                axs[2].plot(n, cap, 'x', color=col, ms=5)
            else:
                xs.append(n); ys.append(float(ci.width()))
        axs[2].plot(xs, ys, ls, marker='o', ms=3, color=col, label=lab, lw=1.2)
    for ax in axs:
        ax.set_xscale('log'); ax.set_yscale('log'); ax.set_ylim(.25, 70); ax.grid(alpha=.18)
        ax.axhline(.8, ls=':', color='0.55', lw=.8)
    axs[0].set(xlabel='Independent founders per arm',
               ylabel='Induction interval width (per hour)', title='Equal root counts')
    axs[1].set(xlabel='Total expected founder-hours', title='Equal observation-time budgets')
    axs[2].set(xlabel='Independent founders per arm', title='Evaluation route, $\\lambda=1$')
    axs[0].legend(ncol=2, loc='upper right', frameon=False)
    axs[2].legend(loc='upper right', frameon=False, fontsize=6.0)
    axs[1].text(.03, .91, 'x: unresolved', transform=axs[1].transAxes, fontsize=7.5)
    (HERE / 'figure_data_inference.json').write_text(json.dumps({'rows': rows}, indent=1))
    save(fig, 'inference')


# ------------------------------------------------------------------ figure 3
def extinction_fig():
    fig, axs = plt.subplots(1, 3, figsize=(7.1, 2.65), layout='constrained')
    rec = {}
    for key, m, eps, lab, col in [('baseline', model(), [.05, .05], 'baseline', C[0]),
                                  ('large', strong_source(), [.18, .18], 'large contrast', C[1])]:
        v = extinction(m, eps)
        rec[key] = v['gap_final']
        t = v['time']
        axs[0].plot(t, v['mean'], color=col, label=lab + ' (both kernels)')
        axs[1].plot(t, v['old'], color=col, ls='--')
        axs[1].plot(t, v['new'], color=col, label=lab)
        axs[2].plot(t, v['new'] - v['old'], color=col, label=lab)
    axs[0].set(yscale='log', ylabel='Expected total cells', title='Identical mean growth')
    axs[1].set(ylabel='Extinction probability', ylim=(0, 1), title='Finite-time extinction')
    axs[2].set(ylabel='Absolute probability increase', ylim=(0, .06), title='Effect size')
    for ax in axs:
        ax.set_xlabel('Hours'); ax.grid(alpha=.15)
    axs[0].legend(frameon=False, fontsize=6.6, loc='upper left')
    axs[1].text(.04, .92, 'dashed: base $K$\nsolid: greater concordance',
                transform=axs[1].transAxes, fontsize=6.9, va='top')
    axs[2].legend(frameon=False, fontsize=7, loc='upper left')
    (HERE / 'figure_data_extinction.json').write_text(json.dumps(rec, indent=1))
    save(fig, 'extinction')


# ------------------------------------------------------------------ figure 4
def delay():
    fig, axs = plt.subplots(1, 2, figsize=(7.1, 2.65), layout='constrained')
    taus = np.linspace(0, 8, 81)
    vals = []
    for t in taus:
        F = exp_law(model(.85), 1, tau=float(t))[3]
        vals.append(np.linalg.svd(F, compute_uv=False)[-1])
    vals = np.array(vals)
    y = exp_law(model(.85), 1)[5]
    axs[0].semilogy(taus, vals, label='one-daughter channel', color=C[0])
    axs[0].semilogy(taus, vals ** 2, label='joint pair channel', color=C[1])
    axs[0].axhspan(1e-4, .01, color='0.94')
    axs[0].axhline(.01, color='0.4', ls='--', lw=.9)
    axs[0].set(xlabel='Readout delay (hours)', ylabel='Smallest singular value',
               ylim=(1e-4, 1), title='Rank versus conditioning')
    axs[0].legend(frameon=False, loc='upper right'); axs[0].grid(alpha=.15)
    axs[1].plot(taus, 2 * taus * y, color=C[2])
    axs[1].set(xlabel='Readout delay (hours)',
               ylabel='Extra daughter cell-hours per founder', title='Upper bound on added cost')
    axs[1].grid(alpha=.15)
    save(fig, 'delay')


if __name__ == '__main__':
    assay(); extinction_fig(); delay(); inference()
    print('figures written to', OUT)
