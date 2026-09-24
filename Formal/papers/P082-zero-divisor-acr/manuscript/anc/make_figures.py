"""Figures for the zero-divisor ACR paper.

All curves are exact formulas except the thin grey trajectories in
figures/ellipsoid.pdf, which are illustrative numerical integrations and are
not used in any proof.
"""
from fractions import Fraction as Fr
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import solve_ivp

OUT = Path(__file__).resolve().parent / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.size": 9, "axes.spines.top": False, "axes.spines.right": False,
    "savefig.bbox": "tight", "mathtext.fontset": "cm", "font.family": "serif",
})
BLUE, ORANGE, RED, GREY, GREEN = "#164a70", "#a26320", "#912c2c", "#7a7a7a", "#2f6b3a"

# ---------------------------------------------------------------- reactor
k1 = k4 = 0.05; k2 = k3 = 0.05; k5 = 0.15; D = 0.01; cin = 10.0
alpha = (k2 + k3 + D) / k1
lcrit, lfloor = float(Fr(39, 1100)), float(Fr(29, 1100))
ls = np.linspace(0, lcrit, 300)
bs = (cin - alpha * (1 + ls / D)) / 2

fig, ax = plt.subplots(figsize=(5.6, 3.3))
ax.plot(ls, bs, color=BLUE, lw=1.6, label=r"equilibrium pool $b^*=c^*$")
ax.axhline(1, color=GREEN, ls="--", lw=1, label=r"required witness floor $b_{\min}=1$")
ax.axvline(lfloor, color=ORANGE, ls=":", lw=1.3, label=r"$\ell=29/1100$: floor lost")
ax.axvline(lcrit, color=RED, ls="--", lw=1.3, label=r"$\ell=39/1100$: branch lost")
ax.plot([0.02], [1.7], "o", color=BLUE, ms=4)
ax.annotate("nominal load", (0.02, 1.7), (0.0035, 0.55), fontsize=8,
            arrowprops=dict(arrowstyle="-", color=GREY, lw=0.6))
ax.set(xlabel=r"specific load $\ell$ (min$^{-1}$)", ylabel=r"concentration ($\mu$M)",
       ylim=(0, 4.2), xlim=(0, 0.0375))
ax.legend(fontsize=7.5, frameon=False, loc="upper center", bbox_to_anchor=(0.5, -0.24), ncol=2)
fig.savefig(OUT / "reactor_envelope.pdf"); plt.close(fig)

# ---------------------------------------------------------------- release
fig, axs = plt.subplots(1, 2, figsize=(6.4, 2.6))
lam = np.geomspace(0.01, 2, 150)
axs[0].loglog(lam, 3 / lam, color=BLUE, lw=1.6)
axs[0].set(xlabel=r"release rate $\lambda$ (min$^{-1}$)", ylabel=r"stored intermediates $S$ ($\mu$M)")
axs[0].set_title(r"$F=1\,\mu$M/min, three stages", fontsize=9)
loss = np.linspace(0, 0.1, 180)
for j, col in zip([1, 2, 3], [BLUE, ORANGE, RED]):
    axs[1].plot(loss, (1 / (1 + loss)) ** j, color=col, lw=1.4, label=f"stage {j}")
axs[1].set(xlabel=r"loss ratio $\delta/\lambda$", ylabel="product yield $\\pi_j$", ylim=(0.7, 1.01))
axs[1].legend(fontsize=7.5, frameon=False)
fig.tight_layout(); fig.savefig(OUT / "release_costs.pdf"); plt.close(fig)

# ---------------------------------------------------------------- ellipsoid
P = np.array([[95/4, 4075/142, 3025/142],
              [4075/142, 57115/1207, 1735/71],
              [3025/142, 1735/71, 1920/71]])
rho = 0.2
xs = np.array([2.2, 1.7, 1.7]); ell = 0.02
Pinv = np.linalg.inv(P)

def field(_, x):
    a, b, c = x
    return [-k1*a*b + k2*b - k4*a*c + k5*c + D*(cin - a) - ell*a,
            k1*a*b - (k2 + k3 + D)*b,
            k4*a*c - (k5 + D)*c + k3*b]

fig, axs = plt.subplots(1, 2, figsize=(6.4, 2.8))
th = np.linspace(0, 2*np.pi, 400)
circ = np.vstack([np.cos(th), np.sin(th)])
rng = np.random.default_rng(7)
for ax, (i, j), labs in zip(axs, [(0, 1), (1, 2)], [("a", "b"), ("b", "c")]):
    S = Pinv[np.ix_([i, j], [i, j])] * rho          # projection of the ellipsoid
    Lc = np.linalg.cholesky(S)
    e = (Lc @ circ)
    ax.fill(xs[i] + e[0], xs[j] + e[1], color=BLUE, alpha=0.13, lw=0)
    ax.plot(xs[i] + e[0], xs[j] + e[1], color=BLUE, lw=1.3)
    ax.plot([xs[i]], [xs[j]], "o", color=RED, ms=3.5)
    ax.set(xlabel=f"${labs[0]}$ ($\\mu$M)", ylabel=f"${labs[1]}$ ($\\mu$M)")
w, V = np.linalg.eigh(P)
for _ in range(7):
    z = rng.normal(size=3); z /= np.linalg.norm(z)
    u0 = V @ (z / np.sqrt(w)) * np.sqrt(rho)          # point on the boundary
    sol = solve_ivp(field, (0, 1500), xs + u0, rtol=1e-9, atol=1e-12, max_step=2.0)
    assert ((sol.y.T - xs) @ P * (sol.y.T - xs)).sum(axis=1).max() <= rho * (1 + 1e-6)
    axs[0].plot(sol.y[0], sol.y[1], color=GREY, lw=0.6)
    axs[1].plot(sol.y[1], sol.y[2], color=GREY, lw=0.6)
axs[0].set_title(r"projection to $(a,b)$", fontsize=9)
axs[1].set_title(r"projection to $(b,c)$", fontsize=9)
fig.tight_layout(); fig.savefig(OUT / "ellipsoid.pdf"); plt.close(fig)
print("figures written to", OUT)
