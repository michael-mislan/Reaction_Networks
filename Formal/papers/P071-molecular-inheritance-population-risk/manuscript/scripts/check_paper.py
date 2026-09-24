"""Exact replay of every certified constant printed in the paper.

Two-site part: sympy rationals, independent of the workspace producers.
Sixteen-site part: reads the rational boxes written by slope_certificate.py.
Deadline part: reads the validated enclosures written by deadline_validated.py.
Every assertion is an exact rational comparison.  Writes data/paper_checks.json.
"""
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path
import sympy as s

R = s.Rational
DATA = Path(__file__).resolve().parents[1] / "data"
ST = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)]   # UU UR RR AU AR AA
b = R(1, 10)
out = {}

# ---------------------------------------------------------------- two-site source
Q = s.zeros(6); D = s.zeros(6); pairs = []
for i, (a, r) in enumerate(ST):
    u = 2 - a - r
    for dest, rate in (((a + 1, r), u * (R(1, 100) + R(a, 2))), ((a, r + 1), u * (R(1, 100) + R(r, 2))),
                       ((a - 1, r), a * (R(1, 100) + R(r, 4))), ((a, r - 1), r * (R(1, 100) + R(a, 4)))):
        if rate:
            j = ST.index(dest); Q[i, j] += rate; Q[i, i] -= rate
    row = []
    for x in range(a + 1):
        for y in range(r + 1):
            p = R(comb(a, x) * comb(r, y), 2 ** (a + r))
            D[i, ST.index((x, y))] += p; row.append((ST.index((x, y)), ST.index((a - x, r - y)), p))
    pairs.append(row)
d = s.Matrix([R(1, 100) if a > r else R(3, 10) for a, r in ST])
Hm = s.diag(*[b + x for x in d]) - Q
Rv = Hm.inv(); assert min(Rv) >= 0
joint = lambda z: s.Matrix([sum(p * z[j] * z[k] for j, k, p in row) for row in pairs])
sq = lambda v: v.applyfunc(lambda x: x * x)
FJ = lambda z: Rv * (d + b * joint(z)); FI = lambda z: Rv * (d + b * sq(D * z))

qIbar = s.Matrix([R(n, 10 ** 6) for n in (948115, 983103, 987779, 378814, 775706, 335634)])
qJbar = s.Matrix([R(94, 100), R(982, 1000), R(987, 1000), R(27, 100), R(735, 1000), R(235, 1000)])
resI = Hm * qIbar - d - b * sq(D * qIbar); resJ = Hm * qJbar - d - b * joint(qJbar)
assert min(resI) == R(435828959, 40000000000000) and min(resJ) >= 0 and max(qIbar) < R(988, 1000)
z = s.zeros(6, 1)
for _ in range(8):
    z = FI(z).applyfunc(lambda x: R(s.floor(x * 10 ** 6), 10 ** 6))
assert z[5] == R(313291, 10 ** 6)
w = s.Matrix([R(n, 1000) for n in (2148, 2011, 1997, 4880, 2882, 4895)])
Jbar = Rv * (2 * b) * s.diag(*list(D * qIbar)) * D
kappa = max((Jbar * w)[i] / w[i] for i in range(6)); assert kappa < R(796, 1000)
out["two_site_coarse"] = dict(min_residual_I=str(min(resI)), qI_AA_lower=str(z[5]), kappa=float(kappa))

# tight boxes: 250 downward iterates, resolvent-weighted supersolutions
lo = {}; up = {}
for lab, Fm in (("J", FJ), ("I", FI)):
    l = s.zeros(6, 1)
    for _ in range(250):
        l = Fm(l).applyfunc(lambda x: R(s.floor(x * 10 ** 12), 10 ** 12))
    if lab == "I":
        der = Rv * (2 * b) * s.diag(*list(D * l)) * D
    else:
        der = s.zeros(6)
        for i, row in enumerate(pairs):
            for j, k, p in row:
                der[i, j] += b * p * l[k]; der[i, k] += b * p * l[j]
        der = Rv * der
    v = (s.eye(6) - der).inv() * s.ones(6, 1)
    u = l + s.Matrix([R(s.ceiling(x * 10 ** 6), 10 ** 12) for x in v])
    res = Hm * u - d - b * (sq(D * u) if lab == "I" else joint(u))
    assert min(res) > 0 and max(u) < 1 and all(l[i] <= u[i] for i in range(6))
    lo[lab], up[lab] = l, u
T = Rv * b
dl = (T * (sq(D * lo["J"]) - joint(up["J"]))).applyfunc(lambda x: max(0, x))
du = T * (sq(D * up["J"]) - joint(lo["J"]))
Bl = T * s.diag(*list(D * (lo["I"] + lo["J"]))) * D; Bu = T * s.diag(*list(D * (up["I"] + up["J"]))) * D
assert max((Bu * w)[i] / w[i] for i in range(6)) < 1          # positive-vector contraction for B_+
hl = (s.eye(6) - Bl).inv() * dl; hu = (s.eye(6) - Bu).inv() * du
assert R(1144144, 10 ** 7) < hl[5] and hu[5] < R(1144331, 10 ** 7)
assert R(2207216, 10 ** 7) < lo['J'][5] and up['J'][5] < R(2207253, 10 ** 7)
assert R(3351447, 10 ** 7) < lo['I'][5] and up['I'][5] < R(3351497, 10 ** 7) and max(up['I']) < R(9875805, 10 ** 7)
assert max(max(up[m][i] - lo[m][i] for i in range(6)) for m in 'JI') < R(5, 10 ** 6)
assert min(hl) > R(246, 10 ** 5) and max(hl) > R(12347, 10 ** 5) and z[5] - qJbar[5] > R(78, 1000)
assert all(hl[i] > 0 for i in range(6))                        # strict separation at every state
out["two_site_tight"] = dict(h_AA=[float(hl[5]), float(hu[5])], qJ_AA=[float(lo["J"][5]), float(up["J"][5])],
                             qI_AA=[float(lo["I"][5]), float(up["I"][5])], qI_max_upper=float(max(up["I"])),
                             h_all_lower=[float(x) for x in hl], h_all_upper=[float(x) for x in hu])

# threshold arithmetic, coarse (Lean-checked constants) and tight (rational boxes)
L = 300
coarse_I = R(686709, 10 ** 6) / (1 - R(988, 1000) ** L); assert coarse_I < R(706, 1000)
tight_J = 1 - up["J"][5]; tight_I = (1 - lo["I"][5]) / (1 - max(up["I"]) ** L)
assert tight_J > R(779, 1000) and tight_I < R(681, 1000) and tight_J - tight_I > R(98, 1000)
dv = json.loads((DATA / "deadline_validated.json").read_text())
u0l, uzu = R(dv["u0"]["AA_lower"]), R(dv["uz"]["AA_upper"])
assert u0l > R(22, 100) and uzu < R(227, 1000)
zz = R(299, 300)
coarse_dead = 1 - R(22, 100) - zz ** (-(L - 1)) * (R(227, 1000) - R(22, 100)); assert coarse_dead > R(760, 1000)
tight_dead = 1 - u0l - zz ** (-(L - 1)) * (uzu - u0l)
assert tight_dead > R(765, 1000) and tight_dead - tight_I > R(84, 1000)
assert R(dv["u0"]["error"]) < R(181, 10 ** 9) and dv["u0"]["max_integer_round"] <= 1
out["regrowth_two_site"] = dict(pJ_lower=float(tight_J), pI_upper=float(tight_I), eventual_gap=float(tight_J - tight_I),
                                deadline_J_lower=float(tight_dead), deadline_gap=float(tight_dead - tight_I),
                                coarse=dict(pI_upper=float(coarse_I), deadline_J_lower=float(coarse_dead)))

# ---------------------------------------------------------------- sixteen sites
for name, gapmin, gapA, hitmin in (("slope_certificate_7.999_8.001_1.json", F(1427, 10 ** 5), F(122, 10 ** 6), F(13, 1000)),
                                   ("slope_certificate_7_9_40.json", F(128, 10 ** 4), F(36, 10 ** 5), F(122, 10 ** 4))):
    cert = json.loads((DATA / name).read_text()); worst = None
    for row in cert["rows"]:
        qJu, qIl = F(row["qJ97"][1]), F(row["qI97"][0]); qmax = F(row["qImax_upper"])
        assert F(row["gap97_lower"]) == qIl - qJu > gapmin and F(row["gapA_upper"]) < gapA and qmax < F(997, 1000)
        hit = (1 - qJu) - (1 - qIl) / (1 - qmax ** 2000)
        assert hit > hitmin
        worst = hit if worst is None or hit < worst else worst
    out[name] = dict(gap97_lower=cert["gap97_lower_decimal"], gapA_upper=cert["gapA_upper_decimal"],
                     hit2000_gap_lower=float(worst))
cert = json.loads((DATA / "slope_certificate_7.999_8.001_1.json").read_text())["rows"][0]
assert F(48558095, 10 ** 8) < F(cert["qJ97"][0]) and F(cert["qJ97"][1]) < F(48561304, 10 ** 8)
assert F(49988773, 10 ** 8) < F(cert["qI97"][0]) and F(cert["qI97"][1]) < F(49991904, 10 ** 8)
assert 1 - F(cert["qJ97"][1]) > F(51438, 10 ** 5)
assert (1 - F(cert["qI97"][0])) / (1 - F(cert["qImax_upper"]) ** 2000) < F(50138, 10 ** 5)
assert cert["max_width"] < 3.58e-5

# ---------------------------------------------------------------- small exact facts quoted in the text
def cov_pair(a, r, f):                       # Cov_x(f(Y), f(Z)) for parent (a, r), exact
    m = e2 = F(0)
    for x in range(a + 1):
        for y in range(r + 1):
            p = F(comb(a, x) * comb(r, y), 2 ** (a + r)); m += p * f(x, y); e2 += p * f(x, y) * f(a - x, r - y)
    return e2 - m * m, e2
assert cov_pair(2, 0, lambda x, y: 1 if x in (0, 2) else 0)[0] == F(1, 4)      # cone is essential
c = F(1, 3); f = lambda x, y: 1 if x <= 2 else c                               # state-dependent division obstruction
assert cov_pair(3, 0, f)[1] - c == F(3, 4) * (1 - c) and cov_pair(4, 0, f)[1] - c == F(3, 8) * (1 - c)
for a in range(6):                                                              # TV identity
    for r in range(6 - a):
        tv = 1 - sum(F(comb(a, x) * comb(r, y), 2 ** (a + r)) ** 2 for x in range(a + 1) for y in range(r + 1))
        assert tv == 1 - F(comb(2 * a, a) * comb(2 * r, r), 4 ** (a + r))
# pooled-covariance example: AA and RR parents mixed equally, newborn-active indicators
assert F(1, 2) * (F(1, 2) - F(9, 16)) + F(1, 2) * 0 + (F(9, 16) / 2 - (F(3, 8)) ** 2) == F(7, 64)
# boundary theorem constants for the worked parameters
k_, e_, w_, h_, bb, d0, dmin = F(1), F(1, 100), F(1, 100), F(1, 2), F(1, 10), F(155, 1000), F(1, 100)
theta = d0 - bb; Lam = k_ - e_ - F(3, 4) * bb; psi = d0 - dmin; sigma2 = max(2 * w_ + k_, e_ + h_ / 2) + bb / 2
gamma = theta / (2 * (psi + Lam))
assert (theta, Lam, psi, sigma2) == (F(55, 1000), F(915, 1000), F(145, 1000), F(107, 100)) and F(259, 10 ** 4) < gamma < F(26, 1000)
out["boundary_constants"] = dict(theta=float(theta), Lambda=float(Lam), psi=float(psi), sigma2=float(sigma2), gamma=float(gamma))
# truncation budget of the validated integrator
eta = 2 * F(2, 25) ** 21 / (1 - F(2, 25)); omega = F(1, 10 ** 40)
budget = 6 * 10 ** 11 * (15000 * (eta + omega) + omega)
assert budget == F(dv["u0"]["error"]) and budget < F(181, 10 ** 9)
out["integration_error"] = float(budget)

(DATA / "paper_checks.json").write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1)); print("ALL CHECKS PASSED")
