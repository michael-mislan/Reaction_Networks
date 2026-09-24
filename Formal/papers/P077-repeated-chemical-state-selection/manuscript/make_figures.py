"""Figures for main.tex.  Both figures evaluate formulas stated in the paper;
they are not stochastic simulations of the chemical source."""
from math import comb, exp, log, log10
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpmath import mp, mpf, exp as mexp

mp.dps = 40
OUT = Path(__file__).with_name("figures")
OUT.mkdir(exist_ok=True)
plt.rcParams.update({"font.size": 9, "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42, "font.family": "DejaVu Sans"})
BLUE, RED, GREEN, GREY = "#1f5a94", "#b0413e", "#2e7d4f", "#555555"

EPS = mpf(1) / 50
R0, RS = mpf(204) / 49, mpf(136) / 49
G = mpf(3) / 5 * mp.log(4) - mpf(19) / 500 - mp.log(mpf(51) / 49)
DT = mpf(4) / 1000


def c(mu):
    return min(1 / (EPS**2 * mu), mexp(-EPS**2 * mu / 2) + mexp(-EPS**2 * mu / (2 + EPS)))


def f_compiled(M, K):
    return mpf(80000) / M * (R0**K - 1) / (R0 - 1)


def f_exp_orig(M, K):
    return sum(2 * c(mpf(M) / 16 / R0**j) for j in range(K))


def f_refined(M, K):
    return sum(c(mpf(3) / 32 * M / RS**j) + c(mpf(M) / 4) for j in range(K))


def min_M(fun, K):
    lo, hi = mpf(2), mpf(10) ** 40
    for _ in range(200):
        mid = mp.sqrt(lo * hi)
        if fun(mid, K) <= DT:
            hi = mid
        else:
            lo = mid
    return float(mp.log10(hi))


Ks = list(range(1, 31))
fig, ax = plt.subplots(figsize=(6.3, 3.9))
ax.plot(Ks, [min_M(f_compiled, k) for k in Ks], color=BLUE, lw=1.8,
        label=r"second moment, $B_b^-\geq B_{b,0}$ (base $204/49$)")
ax.plot(Ks, [min_M(f_exp_orig, k) for k in Ks], color=BLUE, lw=1.2, ls=":",
        label=r"exponential tail, $B_b^-\geq B_{b,0}$ (base $204/49$)")
ax.plot(Ks, [min_M(f_refined, k) for k in Ks], color=GREEN, lw=1.8,
        label=r"exponential tail, $B_b^-\geq\frac{3}{2}B_{b,0}$ (base $136/49$)")
ax.plot(Ks, [float(mp.log10(1 + mexp(G * k) / 2)) for k in Ks], color=RED, lw=1.5, ls="--",
        label=r"necessary for the gain event: $M>1+e^{gK}/2$")
ax.plot([10], [13], marker="o", color=BLUE, ms=6, zorder=5)
ax.annotate(r"machine-checked witness $M=10^{13}$", (10, 13), xytext=(11.4, 15.1), fontsize=8,
            arrowprops=dict(arrowstyle="-", color=GREY, lw=0.6))
ax.plot([10], [log10(4e9)], marker="s", color=GREEN, ms=6, zorder=5)
ax.annotate(r"refined witness $M=4\times10^{9}$", (10, log10(4e9)), xytext=(12.2, 6.6), fontsize=8,
            arrowprops=dict(arrowstyle="-", color=GREY, lw=0.6))
ax.set_xlabel(r"number of complete cycles $K$")
ax.set_ylabel(r"$\log_{10}$ of retained population $M$")
ax.set_xlim(1, 30)
ax.set_ylim(0, 25)
ax.grid(alpha=0.25, lw=0.5)
ax.legend(frameon=False, fontsize=7.6, loc="upper left")
fig.tight_layout()
fig.savefig(OUT / "population_vs_cycles.pdf")
plt.close(fig)

# ---- conditional loss of a rare ancestry at one transfer
n, M = 400, 100
cs = list(range(1, 41))
exact = [comb(n - c_, M) / comb(n, M) for c_ in cs]
upper = [exp(-M * c_ / n) for c_ in cs]
lower = [(1 - c_ / (n - M + 1)) ** M for c_ in cs]
fig, ax = plt.subplots(figsize=(6.3, 3.4))
ax.semilogy(cs, exact, color=BLUE, lw=1.8, label="exact hypergeometric loss")
ax.semilogy(cs, upper, color=RED, lw=1.3, ls="--", label=r"upper bound $e^{-Mc/n}$")
ax.semilogy(cs, lower, color=GREY, lw=1.1, ls=":", label=r"lower bound $(1-c/(n-M+1))^{M}$")
for c_, dx, dy in [(1, 2.5, 1.35), (4, 4.5, 0.30), (20, 2, 3.0)]:
    v = comb(n - c_, M) / comb(n, M)
    ax.plot([c_], [v], "o", color=BLUE, ms=4.5)
    ax.annotate(f"c = {c_}: {v:.5g}", (c_, v), xytext=(c_ + dx, v * dy), fontsize=8)
ax.set_xlabel(r"cells of the rare ancestry at the batch endpoint, $c$")
ax.set_ylabel("conditional probability of\nretaining none of them")
ax.grid(alpha=0.25, lw=0.5, which="both")
ax.legend(frameon=False, fontsize=8)
fig.tight_layout()
fig.savefig(OUT / "minority_loss.pdf")
plt.close(fig)
print("figures written to", OUT)
