"""Regenerate the two publication figures.

Inputs are the preserved certificates in the campaign workspace
(problem_workspaces/RAF_cancer_inherited_tolerance_evolutionary_rescue).
Every plotted curve is a floating-point diagnostic; the shaded interval and the
marked integers are the only certified objects and come from exact rationals.

    python figures.py [--workspace PATH]
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, json, sys

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
DEFAULT_WS = Path(r"E:\Erdos Problems\problem_workspaces"
                  r"\RAF_cancer_inherited_tolerance_evolutionary_rescue")
ap = argparse.ArgumentParser()
ap.add_argument("--workspace", type=Path, default=DEFAULT_WS)
args = ap.parse_args()
W = args.workspace
OUT = HERE / "figures"; OUT.mkdir(exist_ok=True)

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9.5,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42})
COL = {"J": "#126782", "I": "#b65025"}

cert = json.loads((W / "results/decision_certificate.json").read_text())
diag = json.loads((W / "results/postproof/boundary_diagnostic.json").read_text())

# ---------------------------------------------------------------- figure 1
fig, ax = plt.subplots(figsize=(9, 2.55), layout="constrained")
ax.set_xlim(0, 10); ax.set_ylim(0, 3); ax.axis("off")
def box(x, y, s):
    ax.text(x, y, s, ha="center", va="center", fontsize=9.5,
            bbox=dict(boxstyle="round,pad=.5", facecolor="#edf4f7",
                      edgecolor="#126782"))
box(1.6, 2.05, "Maternal marks\n$(a,r)$")
box(5.0, 2.05, "$J$: complementary sisters\n$I$: independent marginals")
box(8.5, 2.05, "Same marginals, same means\nDifferent joint offspring PGF")
for x0, x1 in [(2.75, 3.4), (6.62, 7.25)]:
    ax.annotate("", xy=(x1, 2.05), xytext=(x0, 2.05),
                arrowprops=dict(arrowstyle="->", color="#126782"))
ax.text(5, 1.05, r"At a division: with probability $\mu_i$ exactly one daughter "
                 r"is replaced by the durable type $M$", ha="center", fontsize=9.5)
ax.text(5, .35, r"$AB$ or $BA$: $10+10$ time units  $\rightarrow$  declared clearing "
                r"continuation  $\rightarrow$  eventual total extinction",
        ha="center", fontsize=9)
fig.savefig(OUT / "source.pdf"); fig.savefig(OUT / "source.png", dpi=170)
plt.close(fig)

# ---------------------------------------------------------------- figure 2
plt.rcParams.update({"font.size": 12.5})
fig, axs = plt.subplots(1, 3, figsize=(10.2, 3.15), layout="constrained")

ax = axs[0]; rows = diag["rows"]
ax.axvspan(.120545, .120561, color="#b9d9c0", alpha=.55, label="Certified interval")
for law in ("J", "I"):
    ax.plot([x["c"] for x in rows], [x[law] * 1e6 for x in rows],
            color=COL[law], label=f"${law}$: numerical curve")
ax.axhline(0, color=".3", lw=.8)
ax.set_xlabel("Death rate $c_B$ in pulse $B$")
ax.set_ylabel(r"$10^{6}\,[\,q(AB)-q(BA)\,]$")
ax.ticklabel_format(axis="x", style="plain", useOffset=False)
ax.tick_params(axis="x", labelsize=8)
ax.set_xticks([.12054, .12055, .12056, .12057])
ax.legend(fontsize=8, loc="upper right")
ax.set_title("(a) Opposite orders across an interval", fontsize=10.5)

ax = axs[1]; n = np.arange(1, 201)
mid = lambda k: float(sum(map(F, cert["runs"][k]["bounds"][5])) / 2)
for law, hi, lo in [("J", "JBA", "JAB"), ("I", "IAB", "IBA")]:
    h, l = mid(hi), mid(lo)
    ax.plot(n, 1e6 * (h ** n - l ** n), color=COL[law], label=f"${law}$")
    ax.scatter([32], [1e6 * (h ** 32 - l ** 32)], color=COL[law], s=25, zorder=3)
ax.set_xlabel("Identical $AA$ founders")
ax.set_ylabel(r"Extinction advantage ($10^{6}$)")
ax.set_title("(b) Both advantages peak at 32 founders", fontsize=10.5)
ax.legend(fontsize=9); ax.set_ylim(bottom=0)

# (c) covariance transport: leading-order dependence error accumulated along the
#     backward flow, for the two schedules.
sys.path.insert(0, str(W / "experiments"))
from source import exact_source, PAIRS, L, KAPPA           # noqa: E402
from scipy.integrate import solve_ivp                       # noqa: E402

b, rho, eps = .1, .2, .1
Lm = np.array([[float(x) for x in row] for row in L])
kap = np.array([float(k) for k in KAPPA])
def Amat(e, c):
    d, lin, quad = exact_source(F(str(e)), F(str(c)), F(0), "J")
    A = np.zeros((6, 6))
    for i in range(6):
        for j in range(6): A[i, j] = float(lin[i][j])
        for j, k, p in quad[i]:
            if j < 6: A[i, j] += float(p)
            if k < 6: A[i, k] += float(p)
    return A
def covJ(h):
    return np.array([sum(float(p) * h[j] * h[k] for j, k, p in PAIRS[i])
                     - (Lm[i] @ h) ** 2 for i in range(6)])

A_ph, B_ph = (.3, 0., 10.), (.01, .120553, 10.)
ax = axs[2]
for name, ph, style in [("AB", [A_ph, B_ph], "-"), ("BA", [B_ph, A_ph], "--")]:
    y = np.zeros(12); ss, vv = [0.], [0.]; off = 0.
    for (e, c, t) in reversed(ph):                     # backward integration
        A = Amat(e, c); g = b * kap * (1 - rho)
        rhs = lambda s, y: np.r_[A @ y[:6] + g, A @ y[6:] - b * covJ(y[:6])]
        sol = solve_ivp(rhs, (0, t), y, method="DOP853", rtol=1e-12, atol=1e-14,
                        dense_output=True)
        grid = np.linspace(0, t, 120)
        ss += list(off + grid); vv += list(eps ** 2 * sol.sol(grid)[11] * 1e6)
        y = sol.y[:, -1]; off += t
    ax.plot(ss, vv, style, color="#444", lw=1.5, label=f"${name}$")
for law, val, lab in [("AB", 4.3371245328e-5, r"$E_{AB}$"),
                      ("BA", 3.9899318218e-5, r"$E_{BA}$")]:
    col = "#b65025" if law == "AB" else "#126782"
    ax.scatter([20], [val * 1e6], marker="*", s=95, zorder=4, color=col,
               clip_on=False)
    ax.annotate(lab, xy=(20, val * 1e6), xytext=(20.5, val * 1e6 - 1.3),
                fontsize=11, color=col, annotation_clip=False)
ax.axvline(10, color=".75", lw=.8, ls=":")
ax.set_xlim(0, 23.5); ax.set_xticks([0, 5, 10, 15, 20])
ax.set_xlabel("Backward time $s$")
ax.set_ylabel(r"$10^{6}\varepsilon^{2}\Delta_{AA}(s)$")
ax.set_title("(c) Covariance transport, leading order", fontsize=10.5)
ax.legend(fontsize=9, loc="upper left",
          title=r"$\varepsilon^2\Delta$; $\star$ = certified $E_s$",
          title_fontsize=8.5)

fig.savefig(OUT / "decision.pdf"); fig.savefig(OUT / "decision.png", dpi=170)
plt.close(fig)
print("wrote", OUT / "source.pdf", "and", OUT / "decision.pdf")
