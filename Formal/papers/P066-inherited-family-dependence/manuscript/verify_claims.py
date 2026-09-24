"""Replay every numerical claim printed in the manuscript.

Exact (rational) checks are asserted; floating diagnostics are printed with an
[N] tag and are not asserted.  Inputs are the preserved certificates of the
campaign workspace; nothing here re-runs the four-flow interval integrator.

    python verify_claims.py [--workspace PATH]
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, json, sys

HERE = Path(__file__).resolve().parent
DEFAULT_WS = Path(r"E:\Erdos Problems\problem_workspaces"
                  r"\RAF_cancer_inherited_tolerance_evolutionary_rescue")
ap = argparse.ArgumentParser()
ap.add_argument("--workspace", type=Path, default=DEFAULT_WS)
W = ap.parse_args().workspace
sys.path.insert(0, str(W / "experiments"))
from source import exact_source, STATES, PAIRS, L, KAPPA      # noqa: E402

cert = json.loads((W / "results/decision_certificate.json").read_text())
bnd = json.loads((W / "results/postproof/boundary_certificate.json").read_text())
cont = json.loads((W / "results/postproof/continuation.json").read_text())
dec = json.loads((W / "results/postproof/decision.json").read_text())
flo = json.loads((W / "results/postproof/scalar_floor.json").read_text())
ok = []
def check(name, cond):
    assert cond, "FAILED: " + name
    ok.append(name); print("  [E] ok  " + name)

NAME = ["UU", "UR", "RR", "AU", "AR", "AA"]
b, rho, eps = F(1, 10), F(1, 5), F(1, 10)

# ---------------------------------------------------------------- Section 2
print("\nSection 2  source, means, continuation weight")
d_J, lin_J, quad_J = exact_source(F('.3'), F(0), eps, 'J')
d_I, lin_I, quad_I = exact_source(F('.3'), F(0), eps, 'I')
def mean_matrix(lin, quad):
    A = [[lin[i][j] for j in range(7)] for i in range(7)]
    for i in range(7):
        for j, k, p in quad[i]:
            A[i][j] += p; A[i][k] += p
    return A
check("J and I have identical augmented mean operators",
      mean_matrix(lin_J, quad_J) == mean_matrix(lin_I, quad_I))
check("both offspring laws are normalised (field vanishes at 1)",
      all(d_J[i] + sum(lin_J[i]) + sum(p for _, _, p in quad_J[i]) == 0 for i in range(7)))
check("mutant coordinate rho = delta/beta is an exact fixed point of Phi_M",
      F('.02') * (1 - rho) + F('.1') * (rho ** 2 - rho) == 0)

def Amol(e, c):                      # mutation-free molecular mean matrix
    d, lin, quad = exact_source(e, c, F(0), 'J')
    A = [[lin[i][j] for j in range(6)] for i in range(6)]
    for i in range(6):
        for j, k, p in quad[i]:
            if j < 6: A[i][j] += p
            if k < 6: A[i][k] += p
    return A
A0 = Amol(F('.3'), F(0)); w = [F(x) for x in (14, 11, 10, 84, 43, 107)]
resid = [-F(9, 100) * w[i] - sum(A0[i][j] * w[j] for j in range(6)) for i in range(6)]
check("clearing weight: A0 w <= -.09 w with residual (.2,.2,.2,1.56,.78,1.49)",
      all(x >= 0 for x in resid)
      and resid == [F('.2'), F('.2'), F('.2'), F('1.56'), F('.78'), F('1.49')])
check("minimum clearing weight is 10", min(w) == 10)

# ---------------------------------------------------------------- Section 3
print("\nSection 3  mechanism: quasi-monotonicity of the h equation")
def preceq(i, j):
    (a, r), (A2, R2) = STATES[i], STATES[j]
    return a <= A2 and r >= R2
COV = [(i, j) for i in range(6) for j in range(6)
       if i != j and preceq(i, j)
       and not any(k not in (i, j) and preceq(i, k) and preceq(k, j) for k in range(6))]
check("the Hasse diagram has 6 covering pairs", len(COV) == 6)
UPSETS = [[F(1) if k in S else F(0) for k in range(6)]
          for S in ({x for x in range(6) if m >> x & 1} for m in range(64))
          if all(not (preceq(k, m) and k in S and m not in S) for k in range(6) for m in range(6))]
UPSETS = [u for u in UPSETS if any(u)]
check("the poset has 7 non-empty up-sets", len(UPSETS) == 7)
check("kappa is <=-increasing", all(KAPPA[i] <= KAPPA[j] for i, j in COV))
check("base death is <=-decreasing",
      all(F('.3' if not (STATES[i][0] > STATES[i][1]) else '.01')
          >= F('.3' if not (STATES[j][0] > STATES[j][1]) else '.01') for i, j in COV))
for label, (e, c) in [("A", (F('.3'), F(0))), ("B", (F('.01'), F('.120553')))]:
    A = Amol(e, c)
    check(f"phase {label}: molecular mean matrix is Metzler",
          all(A[i][j] >= 0 for i in range(6) for j in range(6) if i != j))
    vals = [sum((A[j][k] - A[i][k]) * u[k] for k in range(6))
            for (i, j) in COV for u in UPSETS if u[i] == u[j]]
    check(f"phase {label}: all {len(vals)} quasi-monotonicity inequalities hold",
          all(v >= 0 for v in vals))
# Harris step is symbolic; record the finite covariance identity at a=0,r=1.
check("exchangeable allocation reproduces the common marginal Lambda",
      all(sum(p for j, k, p in PAIRS[i] if j == c_) == L[i][c_]
          for i in range(6) for c_ in range(6)))

# ---------------------------------------------------------------- Section 4
print("\nSection 4  certified reversal")
B = {k: [F(x) for x in v["bounds"][5]] for k, v in cert["runs"].items()}
mJ = (B["JBA"][0] - B["JAB"][1], B["JBA"][1] - B["JAB"][0])
mI = (B["IAB"][0] - B["IBA"][1], B["IAB"][1] - B["IBA"][0])
check("m_J > 1.6e-6", mJ[0] > F(16, 10 ** 7))
check("m_I > 1.6e-6", mI[0] > F(16, 10 ** 7))
check("printed table rows enclose the certified dyadic intervals",
      B["JAB"][0] >= F('.969579866104740') and B["JAB"][1] <= F('.969579866104742')
      and B["JBA"][0] >= F('.969581567445558') and B["JBA"][1] <= F('.969581567445561')
      and B["IAB"][0] >= F('.969623237350068') and B["IAB"][1] <= F('.969623237350071')
      and B["IBA"][0] >= F('.969621466763777') and B["IBA"][1] <= F('.969621466763781'))
E_AB = (B["IAB"][0] - B["JAB"][1], B["IAB"][1] - B["JAB"][0])
E_BA = (B["IBA"][0] - B["JBA"][1], B["IBA"][1] - B["JBA"][0])
dE = (E_AB[0] - E_BA[1], E_AB[1] - E_BA[0])
check("dependence errors are positive under both schedules", E_AB[0] > 0 and E_BA[0] > 0)
check("E_AB - E_BA in (3.471e-6, 3.473e-6)",
      dE[0] > F('3.471e-6') and dE[1] < F('3.473e-6'))
# The schedule-gap identity G_J = G_I - (E_AB - E_BA) is an algebraic tautology;
# the meaningful test is that the two independent enclosures of G_J agree.
check("schedule-gap identity: the two enclosures of G_J overlap",
      max(-mJ[1], mI[0] - dE[1]) <= min(-mJ[0], mI[1] - dE[0]))
check("a symmetric +/-4e-6 correction bound would leave the order unresolved",
      mI[1] - F(4, 10 ** 6) < 0 < mI[1] + F(4, 10 ** 6))
# curvature -> derivative enclosure
K = F(bnd["gap_second_derivative_bound"]); width = F('1.6e-5')
check("curvature bound 6912 equals 2 * 20 * 9 * (.2*36 + 12)",
      K == 2 * 20 * 9 * (F('.2') * 36 + 12))
check("derivative slack 6912 * 1.6e-5 = .110592", K * width == F('.110592'))
for law, (lo_g, hi_g), cstar_gap, side in [
        ("J", tuple(map(F, bnd["conclusions"]["J"]["gap"])), mJ, "left"),
        ("I", tuple(map(F, bnd["conclusions"]["I"]["gap"])), mI, "right")]:
    dlo, dhi = map(F, bnd["conclusions"][law]["derivative_enclosure"])
    check(f"G_{law}' < -.0378 uniformly on the certified interval", dhi < F('-.0378'))
    check(f"G_{law} endpoint sign is " + ("negative" if law == "J" else "positive"),
          (hi_g < 0) if law == "J" else (lo_g > 0))

# ---------------------------------------------------------------- Section 5
print("\nSection 5  decision consequences")
check("direct misspecification cost equals m_J", mJ[0] > 0)
R = [F(x) for x in dec["regret"]]
check("minimax regret in (8.67636512e-7, 8.67636514e-7)",
      R[0] > F('8.67636512e-7') and R[1] < F('8.67636514e-7'))
check("minimax regret is strictly below the direct cost m_J", R[1] < mJ[0])
check("founder maximum is 32 for both laws",
      dec["founders"]["J"]["maximizing_integer"] == 32
      and dec["founders"]["I"]["maximizing_integer"] == 32)

# ---------------------------------------------------------------- Section 6
print("\nSection 6  feedback floor")
dmax, mumin = F('.421'), F('.01')
check("d_max = .3 + .121 and mu_min = eps * .1", dmax == F('.3') + F('.121')
      and mumin == eps * F('.1'))
check("d_max >= b * rho", dmax >= b * rho)
# q' = dmax(1-q) + b[(1-mumin)q^2 + mumin*rho*q - q];  put a = 1-q, so a' = -q'.
# Recover the quadratic in a by Lagrange interpolation at a = 0, 1, 2.
adot = lambda a: -(dmax * a + b * ((1 - mumin) * (1 - a) ** 2
                                   + mumin * rho * (1 - a) - (1 - a)))
p0, p1, p2 = adot(F(0)), adot(F(1)), adot(F(2))
c0, c2 = p0, (p2 - 2 * p1 + p0) / 2
c1 = p1 - p0 - c2
check("scalar reduction is exactly a' = .0008 - .3228 a - .099 a^2",
      (c0, c1, c2) == (F('.0008'), F('-.3228'), F('-.099')))
fl = [F(x) for x in flo["bounds"]]
check("a(20) in (.0024725782, .0024725784)",
      fl[0] > F('.0024725782') and fl[1] < F('.0024725784'))
check("floor is far below the exhibited BA risk 1 - q_J(BA)",
      fl[1] < (1 - B["JBA"][1]) / 10)

# ---------------------------------------------------------------- Section 7
print("\nSection 7  continuation sensitivity (sharpened)")
U_AB, U_BA = F(cont["U"]["AB"][1]), F(cont["U"]["BA"][1])
C_AB, C_BA = F(cont["C"]["AB"][1]), F(cont["C"]["BA"][1])
check("U_AB < .050002 and U_BA < .053172", U_AB < F('.050002') and U_BA < F('.053172'))
check("C_AB < 1.430424 and C_BA < 1.452994", C_AB < F('1.430424') and C_BA < F('1.452994'))
eta = F(3, 10 ** 5)
check("eta = 3e-5 preserves both central preferences (one-sided)",
      eta * U_BA < mJ[0] and eta * U_AB < mI[0])
check("eta = 3.2e-5 does NOT follow from the same bounds",
      not (F(32, 10 ** 6) * U_BA < mJ[0]))
def exp_lower(x, n=200):
    term = s = F(1)
    for k in range(1, n):
        term *= x / k; s += term
    return s                       # e^x > s for x > 0
S152 = exp_lower(F(9, 100) * 152)
check("H = 152 preserves both preferences under the one-sided bound",
      C_BA / S152 < mJ[0] and C_AB / S152 < mI[0])
S151 = exp_lower(F(9, 100) * 151)
check("H = 151 does not suffice under the same bound", not (C_BA / S151 < mJ[0]))
S162 = exp_lower(F(9, 100) * 162)
check("H = 162 suffices even for the two-sided sum", (C_AB + C_BA) / S162 < min(mJ[0], mI[0]))
check("added clearing exposure .29*152 = 44.08", F('.29') * 152 == F('44.08'))
check("cost ratio 44.08 / 2.9 is exactly 15.2", F('44.08') / F('2.9') == F('15.2'))

# ---------------------------------------------------------------- printed values
print("\nvalues printed in the manuscript")
for k, v in [("m_J", mJ), ("m_I", mI), ("E_AB", E_AB), ("E_BA", E_BA),
             ("E_AB-E_BA", dE), ("R_*", tuple(R))]:
    print("  %-10s [%.10e, %.10e]" % (k, float(v[0]), float(v[1])))
print("  1-q_J(BA)  %.8f" % float(1 - B["JBA"][0]))
print("  a(20)      %.12f" % float(fl[0]))
print("\n[N] floating diagnostics (not asserted)")
try:
    from source import compose, no_appearance
    A_ph, B_ph = (.3, 0., 10.), (.01, .120553, 10.)
    q = compose([A_ph, B_ph], law='J')
    ext_T = compose([A_ph, B_ph], law='J', terminal=[0.] * 7)
    noM = compose([A_ph, B_ph], law='J', terminal=[1.] * 6 + [0.])
    nap = no_appearance([A_ph, B_ph], law='J')
    print("  J, AB:  survival by T %.5f | M present at T %.5f | M ever appeared %.5f"
          " | eventual survival %.5f"
          % (1 - ext_T[5], 1 - noM[5], 1 - nap[5], 1 - q[5]))
except Exception as exc:                                   # pragma: no cover
    print("  diagnostics unavailable:", exc)

print("\nPASS: %d exact checks" % len(ok))
