"""Render the two figures from saved data; no new computation."""
import json
from fractions import Fraction as F
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
dg = json.loads((ROOT / "data/diagnostics.json").read_text())
wide = json.loads((ROOT / "data/slope_certificate_7_9_40.json").read_text())
chk = json.loads((ROOT / "data/paper_checks.json").read_text())
plt.rcParams.update({"font.size": 9, "axes.spines.top": False, "axes.spines.right": False, "pdf.fonttype": 42,
                     "axes.titlesize": 9.5, "axes.titleweight": "bold"})
BLUE, ORNG, GREY = "#174A7E", "#BD5B26", "#555555"

# ------------------------------------------------------------------ Figure 1
fig, axs = plt.subplots(2, 2, figsize=(7.6, 6.5), layout="constrained")
ax = axs[0, 0]
for smooth, col in ((False, BLUE), (True, ORNG)):
    rows = [r for r in dg["sizes"] if r["smooth"] == smooth]; lab = "smooth" if smooth else "step"
    Ns = [r["N"] for r in rows]
    ax.plot(Ns, [r["interior_gap"] for r in rows], "o-", color=col, ms=4, label=f"{lab}, all-active $(N,0)$")
    ax.plot(Ns, [r["diag_qI"] - r["diag_qJ"] for r in rows], "s--", color=col, ms=4, label=f"{lab}, balanced $(N/2,N/2)$")
ax.plot([16], [chk["slope_certificate_7.999_8.001_1.json"]["gap97_lower"]], "*", color="k", ms=10, zorder=5,
        label="certified lower bound, $(9,7)$")
ax.set(xscale="log", yscale="log", xlabel="site count $N$", ylabel="extinction gap $q_I-q_J$",
       title="A  Preparation governs the size trend", xticks=[2, 4, 8, 16, 32, 64, 128])
ax.set_xticklabels([2, 4, 8, 16, 32, 64, 128]); ax.legend(fontsize=6.5, loc="lower left")

ax = axs[0, 1]
for smooth, col in ((False, BLUE), (True, ORNG)):
    rows = [r for r in dg["sizes"] if r["smooth"] == smooth]
    ax.plot([r["N"] for r in rows], [1 - r["diag_qJ"] for r in rows], "o-", color=col, ms=4,
            label=("smooth" if smooth else "step") + " readout")
ax.set(xscale="log", xlabel="site count $N$", ylabel="survival $1-q_J(N/2,N/2)$", ylim=(0.2, 0.42),
       title="B  Balanced founders: readout regularity", xticks=[2, 4, 8, 16, 32, 64, 128])
ax.set_xticklabels([2, 4, 8, 16, 32, 64, 128]); ax.legend(fontsize=7)

ax = axs[1, 0]
for v, col, lab in zip(dg["variance"], (BLUE, ORNG), ("$N=2$, step, founder $AA$", "$N=16$, smooth, founder $(9,7)$")):
    t = v["t"][1:]; ratio = [a / c for a, c in zip(v["var_joint"][1:], v["var_ind"][1:])]
    ax.plot(t, ratio, "-", color=col, label=lab)
ax.axhline(1, color=GREY, lw=.8, ls=":")
ax.set(xlabel="time $t$", ylabel=r"$\mathrm{Var}\,K_J(t)\,/\,\mathrm{Var}\,K_I(t)$", ylim=(0.6, 1.02),
       title="C  Equal means, ordered variances"); ax.legend(fontsize=7, loc="lower right")

ax = axs[1, 1]
r2 = chk["regrowth_two_site"]; w = wide
n16 = json.loads((ROOT / "data/slope_certificate_7.999_8.001_1.json").read_text())["rows"][0]
pJ16 = float(1 - F(n16["qJ97"][1])); pI16 = float((1 - F(n16["qI97"][0])) / (1 - F(n16["qImax_upper"]) ** 2000))
for x, lo, hi in ((0, r2["pJ_lower"], r2["pI_upper"]), (1, r2["deadline_J_lower"], r2["pI_upper"]), (2, pJ16, pI16)):
    ax.plot(x - .1, lo, "^", ms=7, color=BLUE); ax.plot(x + .1, hi, "v", ms=7, color=ORNG)
    ax.annotate(f">{int(lo * 1000) / 1000:.3f}", (x - .1, lo), xytext=(0, 8), textcoords="offset points", ha="center", fontsize=7)
    ax.annotate(f"<{(int(hi * 1000) + 1) / 1000:.3f}", (x + .1, hi), xytext=(0, -14), textcoords="offset points", ha="center", fontsize=7)
ax.plot([], [], "^", color=BLUE, label="complementary: proved lower bound")
ax.plot([], [], "v", color=ORNG, label="independent: proved upper bound")
ax.set(xticks=[0, 1, 2], xlim=(-.5, 2.5), ylim=(.42, .88), ylabel="regrowth probability",
       title="D  Certified regrowth separations")
ax.set_xticklabels(["$N=2$, $AA$\never hit 300", "$N=2$, $AA$\nhit 300 by $t=300$", "$N=16$, $(9,7)$\never hit 2000"], fontsize=7.5)
ax.legend(fontsize=7, loc="upper right")
for a in axs.flat:
    a.grid(alpha=.15)
fig.savefig(ROOT / "figures/fig_summary.pdf"); fig.savefig(ROOT / "figures/fig_summary.png", dpi=170)

# ------------------------------------------------------------------ Figure 2
fig, axs = plt.subplots(1, 2, figsize=(7.6, 3.1), layout="constrained")
ax = axs[0]
s = [r["s"] for r in dg["slopes"]]
ax.plot(s, [r["qI"] - r["qJ"] for r in dg["slopes"]], "-", color=GREY, label="floating-point gap (diagnostic)")
for k, row in enumerate(wide["rows"]):
    ax.plot([float(F(row["s0"])), float(F(row["s1"]))], [float(F(row["gap97_lower"]))] * 2, "-", color=BLUE, lw=2,
            label="certified lower bound (40 slope cells)" if k == 0 else None)
ax.axhline(.0128, color=ORNG, lw=.8, ls="--", label="uniform certified bound $0.0128$")
ax.set(xlabel="readout slope $s$", ylabel="$q_I(9,7)-q_J(9,7)$", title="A  Slope robustness, $N=16$", ylim=(.0125, .0150))
ax.legend(fontsize=6.5, loc="upper left")
ax = axs[1]
ph = [c["phases"] for c in dg["clocks"]]
ax.plot(ph, [c["qJ_9_7"] for c in dg["clocks"]], "o-", color=BLUE, label="complementary")
ax.plot(ph, [c["qI_9_7"] for c in dg["clocks"]], "s--", color=ORNG, label="independent")
ax.set(xlabel="Erlang phases $m$ (mean division time 10)", ylabel="extinction from $(9,7)$", xticks=[1, 2, 4],
       title="B  Same mean, different clock variance"); ax.legend(fontsize=7)
for a in axs:
    a.grid(alpha=.15)
fig.savefig(ROOT / "figures/fig_robustness.pdf"); fig.savefig(ROOT / "figures/fig_robustness.png", dpi=170)
