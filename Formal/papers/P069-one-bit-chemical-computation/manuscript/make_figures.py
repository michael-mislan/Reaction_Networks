"""Figures for "Certified one-bit chemical computation".

Every curve is either an exact rational quantity recomputed here or a value read
from the recorded literal-simulation output in data/.  Nothing is fitted and no
new stochastic run is performed.
"""
import json
from fractions import Fraction as F
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
OUT = HERE / "figures"
OUT.mkdir(exist_ok=True)

plt.rcParams.update({
    "font.size": 9.5, "axes.spines.top": False, "axes.spines.right": False,
    "pdf.fonttype": 42, "font.family": "DejaVu Sans", "axes.labelsize": 9.5,
    "axes.titlesize": 10, "legend.fontsize": 9, "xtick.labelsize": 9,
    "ytick.labelsize": 9,
})
BLUE, GREEN, ORANGE, GRAY = "#235c91", "#237458", "#b35629", "#555555"

S = 2 ** 31
C_IDEAL = F(2147232289, S)
C_OPS = F(2147153442, S)
B = F(3216)


def save(fig, name):
    fig.savefig(OUT / (name + ".pdf"), bbox_inches="tight")
    fig.savefig(OUT / (name + ".png"), dpi=160, bbox_inches="tight")
    plt.close(fig)


# ---------------------------------------------------------------- correction walk
def correct_by_fuel(r, L, j=2):
    """P(absorb at 0 within L jumps) for the embedded correction walk."""
    v = [F(0)] * (r + 1)
    v[0] = F(1)
    for _ in range(L):
        v = [F(1)] + [F(r - y - 1, r - 2) * v[y - 1] + F(y - 1, r - 2) * v[y + 1]
                      for y in range(1, r)] + [F(0)]
    return v[j]


def absorption(r, j, L=64):
    """Exact (mass, unnormalised spent-fuel moment) per endpoint."""
    active, hits = {j: F(1)}, []
    for k in range(1, L + 1):
        nxt = {}
        for y, p in active.items():
            for yy, q in ((y - 1, F(r - y - 1, r - 2)), (y + 1, F(y - 1, r - 2))):
                if yy in (0, r):
                    hits.append((k, yy, p * q))
                else:
                    nxt[yy] = nxt.get(yy, F()) + p * q
        active = nxt
    return {b: (sum(p for k, y, p in hits if y == b),
                sum(k * p for k, y, p in hits if y == b)) for b in (0, r)}


def fuel_bound(core, r, j, endpoint):
    v, s = absorption(r, j)[endpoint]
    return (core - 80 * F(1, 10 ** 7)) * v - 80 ** 3 * F(5, 10 ** 11) * s \
        - B * F(1, 10 ** 7) - F(1, 10 ** 12)


# ------------------------------------------------------- 1. certificate and budget
ops = json.loads((HERE / "data/operation_certificate.json").read_text())
fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.7), layout="constrained")

axs[0].plot([float(F(r["theta_exact"])) for r in ops],
            [1 - r["numerator"] / S for r in ops], "o-", color=BLUE, ms=4)
axs[0].axvspan(0.48, 0.5, alpha=0.10, color=GREEN)
axs[0].set(xlabel=r"partition probability $\theta$",
           ylabel="certified core failure", yscale="log")
axs[0].set_title(r"exact core certificate, $\eta=0.9$")
axs[0].annotate(r"$\theta=0.48$ endpoint;" + "\n" + r"covers all of $[0.48,0.52]$",
                xy=(0.4805, 1 - 2147153442 / S), xytext=(0.4735, 3.1e-4),
                fontsize=8, color=GRAY, ha="left",
                arrowprops={"arrowstyle": "->", "color": GRAY, "lw": 0.8})

labels = ["core partition\nand output", "repair deadline", "prefix clocks",
          "later departure"]
wo = [1 - 2147153442 / S, 1e-6, 3216 / 8e7, 80 * 1e-7 + 80 ** 3 * 6e-11]
fo = [float(1 - C_OPS * float(absorption(10, 2)[0][0])), 1e-12, 3216 / 1e7,
      80 * 1e-7 + 80 ** 3 * 5e-11 * float(absorption(10, 2)[0][1])]
y = range(len(labels))
axs[1].barh([i + 0.19 for i in y], wo, height=0.36, color=BLUE, label="WO (81 units)")
axs[1].barh([i - 0.19 for i in y], fo, height=0.36, color=ORANGE, label="FO (144 units)")
axs[1].set(yticks=list(y), yticklabels=labels, xscale="log",
           xlabel="failure allowance")
axs[1].set_title("certified error budget")
axs[1].legend(loc="upper center", bbox_to_anchor=(0.5, -0.30), ncol=2,
              frameon=False, handlelength=1.2, columnspacing=1.4)
save(fig, "certificate")

# --------------------------------------------------------------- 2. fuel/consensus
fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.7), layout="constrained")
for r, col in ((10, BLUE), (12, GREEN), (16, ORANGE)):
    Ls = list(range(2, 65, 2))
    axs[0].plot(Ls, [float(correct_by_fuel(r, L)) for L in Ls], color=col,
                label=f"$r={r}$")
    axs[0].axhline(float(1 - F(1, 2 ** (r - 3))), color=col, ls=":", lw=1)
axs[0].set(xlabel="available fuel $L$ (maximum correction jumps)",
           ylabel="correct-consensus probability", ylim=(0.86, 1.004))
axs[0].legend(loc="lower right", ncol=1, frameon=False, handlelength=1.2,
              labelspacing=0.3)
axs[0].set_title("two minority molecules")
axs[0].text(2, 0.8665, "dotted: exact unlimited-fuel limits", fontsize=8, color=GRAY)

rs = list(range(8, 25))
axs[1].semilogy(rs, [float(F(1, 2 ** (r - 3))) for r in rs], "o-", color=BLUE, ms=4)
axs[1].axhline(2e-4, color=ORANGE, ls="--", lw=1.1)
axs[1].text(17.2, 5.5e-4, r"target $\delta=2\cdot10^{-4}$", color=ORANGE, fontsize=8)
axs[1].axvline(16, color=GRAY, ls=":", lw=1)
axs[1].text(16.4, 2e-2, r"$r\geq 16$", color=GRAY, fontsize=8)
axs[1].set(xlabel="resident total $r$", ylabel=r"wrong consensus $u_r(2)=2^{-(r-3)}$")
axs[1].set_title("inventory rule for the correction step")
save(fig, "fuel")

# ------------------------------------------------------------------- 3. variation
fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.7), layout="constrained")
mixed = float(fuel_bound(C_OPS, 10, 2, 10))
pure = float(80 * F(1, 10 ** 7) * (1 + F(1, 10 ** 7)))
axs[0].barh([1], [mixed], color=ORANGE, height=0.45)
axs[0].barh([0], [pure], color=BLUE, height=0.45)
axs[0].set(xscale="log", yticks=[0, 1],
           yticklabels=["pure newborn\n(upper bound)", "mixed preparation\n(lower bound)"],
           xlabel="probability of an opposite-program pair")
axs[0].set_title("switching is not a label-only rate")
axs[0].annotate("", xy=(mixed, 0.5), xytext=(pure, 0.5),
                arrowprops={"arrowstyle": "<->", "color": GRAY, "lw": 1.1})
axs[0].text(4e-5, 0.57, r"$>935\times$", fontsize=9, color=GRAY)
axs[0].set_xlim(2e-6, 5e-2)


def split(weights, m):
    p = [1]
    for w in weights:
        v = [0] * (len(p) + w)
        for i, a in enumerate(p):
            v[i] += a
            v[i + w] += a
        p = v
    return F(sum(p[m:sum(weights) - m + 1]), 2 ** len(weights))


pilot = json.loads((HERE / "data/elementary_pilot.json").read_text())
sizes = [1, 2, 4]
vals = [float(split([w] * (32 // w), 8)) for w in sizes]
axs[1].bar([str(w) for w in sizes], [1 - v for v in vals],
           color=[BLUE, ORANGE, GRAY], width=0.55)
axs[1].set(yscale="log", xlabel="moieties per intact cluster",
           ylabel=r"failure: some daughter has $<8$")
axs[1].set_title("32 moieties, fair division")
for i, v in enumerate(vals):
    axs[1].text(i, (1 - v) * 1.35, f"{1 - v:.2e}", ha="center", fontsize=8)
axs[1].set_ylim(1e-3, 1.0)
save(fig, "variation")

# ------------------------------------------------------------------- 4. selection
pop = json.loads((HERE / "data/population_followup.json").read_text())
fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.7), sharey=True, layout="constrained")
for ax, key, title in zip(axs, ("selected", "neutral"),
                          ("product-dependent retention", "neutral retention")):
    rows = pop[key]
    rr = [r["round"] for r in rows]
    for i, col, label in ((0, BLUE, "X program"), (1, ORANGE, "Y program"),
                          (2, GRAY, "outside both regions")):
        ax.plot(rr, [r["counts"][i] for r in rows], marker="o", ms=4, color=col,
                label=label)
    if key == "selected":
        ax.axvline(2.5, color=GRAY, ls=":")
        ax.text(0.15, 70, r"retain on $P_X$", fontsize=8)
        ax.text(2.7, 70, r"retain on $P_Y$", fontsize=8)
    ax.set(xlabel="completed division rounds", title=title, xticks=rr)
axs[0].set_ylabel("retained compartments")
axs[1].legend(loc="upper left", frameon=False)
save(fig, "selection")

print("wrote certificate, fuel, variation, selection to", OUT)
