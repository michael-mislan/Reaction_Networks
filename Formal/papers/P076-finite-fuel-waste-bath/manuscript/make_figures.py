"""Vector figures for the paper.

Every curve evaluates a proved bound or a closed-form quantity, except the
deterministic diagnostics panel, which integrates the mass-action ODE
associated with the same reaction table and is labelled as such in the caption.

    ..\\..\\..\\.venv\\Scripts\\python.exe make_figures.py
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp

HERE = Path(__file__).resolve().parent
FIG = HERE / "figures"
FIG.mkdir(exist_ok=True)

plt.rcParams.update({
    "font.size": 9,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "savefig.bbox": "tight",
    "pdf.fonttype": 42,
    "figure.dpi": 150,
})

KAPPA = float(F(1839, 8750000000000))
OLD = 1e-10
BLUE, ORANGE, GREEN, GREY = "#27647b", "#a45723", "#4f7942", "#5b6770"

# ---------------------------------------------------------------------------
# Figure 1: the two certificates and the resulting design scales.
# ---------------------------------------------------------------------------

fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.85), layout="constrained")

V = np.linspace(2e10, 2.4e11, 600)
axs[0].semilogy(V / 1e11, 100 * 101 * np.exp(-OLD * V), color=GREY, ls="--",
                label=r"rounded  $101\,m\,e^{-V/10^{10}}$")
axs[0].semilogy(V / 1e11, 100 * 101 * np.exp(-KAPPA * V), color=BLUE,
                label=r"refined  $101\,m\,e^{-\kappa V}$")
axs[0].axhline(21e-6, color=ORANGE, lw=.8, ls=":")
axs[0].text(2.02, 3e-5, r"$2.1\times10^{-5}$", color=ORANGE, fontsize=7.5, ha="right")
for x, lab in [(0.96, "$9.6$"), (2.0, "$20$")]:
    axs[0].plot([x], [100 * 101 * np.exp(-KAPPA * x * 1e11)], "o", color=BLUE, ms=4)
axs[0].annotate(r"$V=9.6\times10^{10}$", xy=(0.96, 2.08e-5), xytext=(1.05, 3e-3),
                fontsize=7.5, arrowprops={"arrowstyle": "->", "lw": .7})
axs[0].set(xlabel=r"copy scale $V\ /\ 10^{11}$",
           ylabel=r"mission failure bound, $m=100$",
           ylim=(1e-16, 1e2))
axs[0].legend(fontsize=7.5, loc="upper right", frameon=False)

ms = np.logspace(0, 7, 200)
V_old = np.maximum(2e11, np.ceil(np.log(101 * ms / 0.01) / OLD))
V_new = np.maximum(5e10, np.ceil(np.log(101 * ms / 0.01) / KAPPA))
R_old = ms * np.floor(V_old / 5) / 0.1
R_new = ms * np.floor(V_new / 10) / 0.1
axs[1].loglog(ms, R_old, color=GREY, ls="--", label="rounded rate, $\\lfloor V/5\\rfloor$")
axs[1].loglog(ms, R_new, color=BLUE, label="refined rate, $\\lfloor V/10\\rfloor$")
axs[1].scatter([100], [4e13], c=GREY, zorder=3, s=16)
axs[1].scatter([100], [9.6e12], c=BLUE, zorder=3, s=16)
axs[1].set(xlabel="mission length $m$ (cycles)",
           ylabel="sufficient pure fuel $R$ (counts)")
axs[1].legend(fontsize=7.5, loc="upper left", frameon=False)
for ax in axs:
    ax.grid(alpha=.18)
fig.savefig(FIG / "certificate.pdf")
plt.close(fig)

# ---------------------------------------------------------------------------
# Figure 2: backward phase-transport weights (closed form) and the tilt.
# ---------------------------------------------------------------------------

fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.6), layout="constrained")

# w(n) = a^n (1, 20n/(q a), 580 n(n-1)/(q^2 a^2), 38n/(q a)) with q = 3000V,
# a = 1 - 70/q.  Plot the large-V limit in the rescaled variable t = n/V.
t = np.linspace(0, 1.05, 400)
a = np.exp(-70 * t / 3000)
wX = a
wC1 = a * 20 * t / 3000
wC2 = a * 580 * t ** 2 / 3000 ** 2
wZ = a * 38 * t / 3000
for y, lab, col, ls in [(wX, "$w_X$", BLUE, "-"), (wC1, "$w_{C_1}$", ORANGE, "--"),
                        (wZ, "$w_Z$", GREEN, "-."), (wC2, "$10^{3}\\,w_{C_2}$", GREY, ":")]:
    axs[0].plot(t, y * (1000 if lab.startswith("$10") else 1), color=col, ls=ls, label=lab)
axs[0].axvspan(89 / 100, 91 / 100, color=BLUE, alpha=.08)
axs[0].text(0.90, 0.92, "window", fontsize=7.5, ha="center", color=BLUE)
axs[0].axhline(1 / 35, color="k", lw=.6, ls=":")
axs[0].text(0.03, 1 / 35 + .012, "$1/35$", fontsize=7.5)
axs[0].set(xlabel=r"backward clock steps $n/(100V)$", ylabel="weight",
           ylim=(0, 1.05))
axs[0].legend(fontsize=7.5, frameon=False, ncol=2)

s = np.linspace(0, 2e-6, 400)
Delta, C = 3 / 7000, 12 / 5 * 91
axs[1].plot(s * 1e6, (Delta * s - C * s ** 2) * 1e10, color=BLUE)
axs[1].axhline(1.0, color=GREY, ls="--", lw=.9)
axs[1].text(0.06, 1.05, "rounded rate $10^{-10}$", fontsize=7.5, color=GREY)
axs[1].scatter([1.0], [KAPPA * 1e10], c=ORANGE, zorder=3, s=18)
axs[1].annotate(r"$s=10^{-6}$,  $\kappa=2.1017\times10^{-10}$", xy=(1.0, KAPPA * 1e10),
                xytext=(1.06, 1.35), fontsize=7.5,
                arrowprops={"arrowstyle": "->", "lw": .7})
axs[1].set(xlabel=r"tilt $s\ /\ 10^{-6}$", ylabel=r"$\kappa(s)\ /\ 10^{-10}$",
           ylim=(0, 2.4))
for ax in axs:
    ax.grid(alpha=.18)
fig.savefig(FIG / "phase.pdf")
plt.close(fig)

# ---------------------------------------------------------------------------
# Figure 3: deterministic diagnostics (mass-action ODE, not the count process).
# ---------------------------------------------------------------------------


def run(name: str, sigma: float, total: float, d: float) -> dict:
    c2 = .05 / 1.4
    y = np.array([159 / 160 - 2 * c2, 159 / 160 - 2 * c2, 0., 0., c2, 0., 1., 0., 0., 0., 0.])
    rows, series = [], []
    for cycle in range(1, 9):
        y[:6] *= .25 * .98
        y[0:2] += .745
        y[7:] = 0

        def rhs(t, y):
            u, w, x, c1, c2_, z, af = y[:7]
            ap = total - af
            j0 = 2e-9 * (u * w - x / 10)
            j1 = 20 * (x * u - c1)
            j2 = 20 * (c1 * w - c2_)
            j3 = 20 * c2_ - 2 * z
            j4 = 20 * (z - x * x)
            forward = d * af * x
            reverse = d / 8e9 * ap * u * w
            drive = forward - reverse
            return [1 - u - j0 - j1 + drive, 1 - w - j0 - j2 + drive,
                    -x + j0 - j1 + 2 * j4 - drive, -c1 + j1 - j2, -c2_ + j2 - j3,
                    -z + j3 - j4, -drive / sigma, forward, reverse,
                    (x + c1 + c2_ + 2 * z) if t >= 3 else 0, x if t >= 3 else 0]

        for lo, hi in [(0, 3), (3, 4)]:
            sol = solve_ivp(rhs, (lo, hi), y, method="Radau", rtol=1e-9, atol=1e-12,
                            t_eval=np.linspace(lo, hi, 121))
            if not sol.success:
                raise RuntimeError(sol.message)
            y = sol.y[:, -1]
            for tt, v in zip(sol.t, sol.y.T):
                series.append([4 * (cycle - 1) + float(tt), *map(float, v[:7])])
        rows.append({"cycle": cycle, "forward": float(y[7]), "reverse": float(y[8]),
                     "QI": float(y[9]), "QX": float(y[10])})
    return {"name": name, "sigma": sigma, "d": d, "cycles": rows, "series": series}


cases = [run("pure", 1, 1, .02), run("loaded", 1, 2, .02),
         run("nearly depleted", .001, 1, .02), run("zero drive", 1, 1, 0)]
(HERE / "diagnostics_summary.json").write_text(json.dumps(
    [{"name": c["name"], "sigma": c["sigma"], "d": c["d"],
      "min_QI": min(r["QI"] for r in c["cycles"]),
      "min_QX": min(r["QX"] for r in c["cycles"]),
      "forward_total": sum(r["forward"] for r in c["cycles"]),
      "reverse_total": sum(r["reverse"] for r in c["cycles"]),
      "final_fuel_activity": c["series"][-1][-1]} for c in cases], indent=2))

fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.75), layout="constrained")
for k, case in enumerate(cases):
    series = np.asarray(case["series"])
    axs[0].plot(series[:, 0], np.maximum(series[:, -1], 1e-12), label=case["name"],
                ls=["-", "--", "-.", ":"][k], lw=1.2)
    axs[1].plot(range(1, 9), [r["QI"] for r in case["cycles"]], label=case["name"],
                ls=["-", "--", "-.", ":"][k], lw=1.2)
axs[0].set(yscale="log", xlabel=r"time / $\tau$", ylabel="fuel activity $f/R$",
           ylim=(1e-11, 3))
axs[1].set(xlabel="cycle", ylabel="collected template equivalents / $V$")
axs[1].legend(fontsize=7.5, frameon=False)
for ax in axs:
    ax.grid(alpha=.18)
fig.savefig(FIG / "diagnostics.pdf")
plt.close(fig)

rows = []
for c in cases:
    rows.append("{} & {:g} & {:g} & {:.6f} & {:.6f} & {:.4g} & {:.3g} \\\\".format(
        c["name"].capitalize(), c["sigma"], c["d"],
        min(r["QI"] for r in c["cycles"]), min(r["QX"] for r in c["cycles"]),
        sum(r["forward"] for r in c["cycles"]), sum(r["reverse"] for r in c["cycles"])))
(HERE / "diagnostic_table.tex").write_text(
    "\\begin{tabular}{lrrrrrr}\n\\toprule\n"
    "Case & $R/V$ & $d$ & $\\min Q_I/V$ & $\\min Q_X/V$ & $F/V$ & $P/V$\\\\\n\\midrule\n"
    + "\n".join(rows) + "\n\\bottomrule\n\\end{tabular}\n")

print("three figures and the diagnostics table written")
