"""Vector figures for the manuscript.  All plotted values are exact rational
evaluations of the certificate L; nothing here is fitted or measured."""
from fractions import Fraction as F
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.size": 10, "font.family": "serif", "pdf.fonttype": 42,
    "axes.spines.top": False, "axes.spines.right": False,
})
TEAL, RUST, GREY = "#14666b", "#b05e24", "#5d6469"

def lower(q1, q2, B, e, s, J, H):
    return max(F(0), q1-B, q1+q2-B-H, e*q1+q2-e*B-(s-e)*J-H, s*q1+q2-s*B-H)

def save(fig, name):
    fig.savefig(OUT / (name + ".pdf"), bbox_inches="tight")
    plt.close(fig)

# ---- Figure: certificate as a function of the pre-wash reserve ceiling ------
q1, q2, B, e, s, H = F(29,5), F(19,5), F(10), F(1,20), F(9,10), F(1,5)
Js = [F(k, 40) for k in range(0, 201)]
vals = [float(lower(q1, q2, B, e, s, J, H)) for J in Js]
fig, ax = plt.subplots(figsize=(6.1, 3.0))
ax.plot([float(J) for J in Js], vals, color=TEAL, lw=2)
ax.axhline(1.6, color=GREY, ls=":", lw=1)
ax.axhline(1.52, color=RUST, ls="--", lw=1)
for J, L, txt, tx, ty, ha in [
        (2,        1.69, r"$J=2$:  $L=1.69$",          2.45, 3.30, "left"),
        (179/85,   1.60, r"$J=179/85$:  $L=8/5$",      2.95, 2.85, "left"),
        (11/5,     1.52, r"$J=11/5$:  ties $38/25$",   3.45, 2.40, "left"),
        (339/85,   0.00, r"$J=339/85$:  $L=0$",        4.95, 1.05, "right")]:
    ax.plot([J], [L], "o", color=RUST, ms=4.5, zorder=4)
    ax.annotate(txt, xy=(J, L), xytext=(tx, ty), fontsize=8.5, ha=ha,
                arrowprops=dict(arrowstyle="->", lw=0.8, color=GREY,
                                shrinkA=3, shrinkB=3))
ax.set_xlabel(r"pre-wash reserve ceiling $J$  ($\mu$mol equivalents)")
ax.set_ylabel(r"certificate $L$  ($\mu$mol)")
ax.set_xlim(0, 5); ax.set_ylim(-0.05, 3.6)
save(fig, "reserve")

# ---- Figure: joint activity / reserve-slack budget -------------------------
fig, ax = plt.subplots(figsize=(6.1, 3.5))
aa = [F(k, 200) for k in range(0, 201)]
for delta, style in [(F(0), "-"), (F(1,20), "--"), (F(1,10), "-."), (F(1,5), ":")]:
    ys = [float(lower(q1, F(17,10)+F(21,10)*a, B, e, s, F(2)+delta, H)) for a in aa]
    ax.plot([float(a) for a in aa], ys, style, color=TEAL, lw=1.8,
            label=rf"washed, $\delta={float(delta):g}$")
ax.axhline(1.52, color=RUST, lw=1.6, label=r"matched unwashed: $38/25$")
ax.axhline(1.6, color=GREY, ls=":", lw=1.2, label=r"target $F_\star=8/5$")
ax.axvline(193/210, color=GREY, ls="--", lw=0.8)
ax.set_xlabel(r"additional productive activity retained, $a$")
ax.set_ylabel(r"certificate $L_{\mathrm{wash}}(a,\delta)$  ($\mu$mol)")
ax.set_xlim(0, 1); ax.set_ylim(0, 1.85)
ax.legend(fontsize=8.2, loc="upper center", bbox_to_anchor=(0.5, -0.20),
          ncol=3, frameon=False, handlelength=2.4, columnspacing=1.4)
save(fig, "budget")

# ---- Figure: two histories inside the same observation envelope ------------
fig, ax = plt.subplots(figsize=(6.1, 2.8))
labels = ["first\ncollection", "second\ncollection", "pre-wash\nreserve $r$",
          "fresh total\n$F_1+F_2$"]
pos = range(4); w = 0.36
ax.bar([p - w/2 for p in pos], [6, 4, 2, 2.1], w, color=TEAL,
       label="positive witness")
ax.bar([p + w/2 for p in pos], [5.8, 3.81, 4, 0], w, color=RUST,
       label="zero-fresh alternative")
for p, (lo, hi) in zip([0, 1], [(5.8, 6.2), (3.8, 4.2)]):
    ax.hlines([lo, hi], p - 0.46, p + 0.46, color=GREY, lw=0.8, ls=":")
ax.set_xticks(list(pos)); ax.set_xticklabels(labels, fontsize=8.5)
ax.set_ylabel(r"amount ($\mu$mol equivalents)")
ax.legend(fontsize=8.5, frameon=False)
ax.text(0.5, 6.35, "dotted lines: reported output envelopes  $y_k\pm0.2$",
        fontsize=7.8, color=GREY)
ax.set_ylim(0, 7.0)
save(fig, "ambiguity")
print("wrote", sorted(p.name for p in OUT.glob("*.pdf")))
