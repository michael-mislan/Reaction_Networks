"""Exact-rational audit of every numerical claim printed in the paper.

Standard library only.  Run:  python check_paper.py
"""
from fractions import Fraction as F

def facets(q1, q2, B, e, s, J, H):
    return {
        "zero": F(0),
        "first": q1 - B,
        "total": q1 + q2 - B - H,
        "reserve": e*q1 + q2 - e*B - (s-e)*J - H,
        "uniform": s*q1 + q2 - s*B - H,
    }

def lower(q1, q2, B, e, s, J, H):
    return max(facets(q1, q2, B, e, s, J, H).values())

def carry(e, s, J, x):
    return e*x + (s-e)*min(J, x)

def closed(q1, q2, B, e, s, J, H):
    A = max(F(0), q1-B)
    x = max(F(0), B-q1)
    return A + max(F(0), q2 - H - carry(e, s, J, x))

checks = []
def ok(name, got, want):
    assert got == want, (name, got, want)
    checks.append((name, str(got)))

# ---------------------------------------------------------------- Section 5
B, J, e, s, H = F(10), F(2), F(1,20), F(9,10), F(1,5)
y1, y2, eps = F(6), F(4), F(1,5)
q1, q2 = y1 - eps, y2 - eps
ok("q1 (washed)", q1, F(29,5))
ok("q2 (washed)", q2, F(19,5))
fw = facets(q1, q2, B, e, s, J, H)
ok("facet zero",    fw["zero"],    F(0))
ok("facet first",   fw["first"],   F(-21,5))
ok("facet total",   fw["total"],   F(-3,5))
ok("facet reserve", fw["reserve"], F(169,100))
ok("facet uniform", fw["uniform"], F(-9,50))
ok("washed certificate", lower(q1, q2, B, e, s, J, H), F(169,100))
ok("closed form agrees", closed(q1, q2, B, e, s, J, H), F(169,100))

# matched unwashed arm
q2u = F(57,10) - eps
ok("q2 (unwashed)", q2u, F(11,2))
fu = facets(q1, q2u, B, s, s, J, H)
ok("unwashed total facet", fu["total"], F(11,10))
ok("unwashed reserve facet", fu["reserve"], F(38,25))
ok("unwashed uniform facet", fu["uniform"], F(38,25))
ok("unwashed certificate", lower(q1, q2u, B, s, s, J, H), F(38,25))
ok("ideal gain (s-e)*eps1", (s-e)*eps, F(17,100))

# error-free (nominal) substitution
ok("nominal washed value", lower(y1, y2, B, e, s, J, H), F(19,10))

# ---------------------------------------------------------------- Section 6
# reserve tolerance L(J) = max(0, 339/100 - 17/20 J)
for Jt in [F(0), F(1), F(2), F(21,10), F(11,5), F(3), F(4), F(5)]:
    ok(f"reserve tolerance J={Jt}", lower(q1, q2, B, e, s, Jt, H),
       max(F(0), F(339,100) - F(17,20)*Jt))
ok("positive-certificate boundary", F(339,100)/F(17,20), F(339,85))
ok("target-1.6 boundary", (F(339,100)-F(8,5))/F(17,20), F(179,85))
ok("beat-1.52 boundary", (F(339,100)-F(38,25))/F(17,20), F(11,5))

# activity / slack budget  L(a,delta) = max(0, 21/10 a - 41/100 - 17/20 delta)
def Lwash(a, d):
    return lower(q1, F(17,10)+F(21,10)*a, B, e, s, F(2)+d, H)
for a in [F(0), F(1,2), F(9,10), F(193,210), F(67,70), F(1)]:
    for d in [F(0), F(1,20), F(1,10), F(1,5)]:
        ok(f"slack curve a={a} d={d}", Lwash(a, d),
           max(F(0), F(21,10)*a - F(41,100) - F(17,20)*d))
ok("L_wash(0.9,0)", Lwash(F(9,10), F(0)), F(37,25))
ok("L_wash(1,0)",   Lwash(F(1), F(0)),   F(169,100))
ok("strict-improvement activity", (F(38,25)+F(41,100))/F(21,10), F(193,210))
ok("target-1.6 activity",         (F(8,5)+F(41,100))/F(21,10),  F(67,70))
ok("slack coefficient", F(17,20)/F(21,10), F(17,42))
for d in [F(0), F(1,20), F(1,10), F(1,5)]:
    ok(f"improve threshold d={d}", F(193,210)+F(17,42)*d,
       (F(38,25)+F(41,100)+F(17,20)*d)/F(21,10))
    ok(f"target threshold d={d}", F(67,70)+F(17,42)*d,
       (F(8,5)+F(41,100)+F(17,20)*d)/F(21,10))
ok("delta=0.2 needs a>1", F(193,210)+F(17,42)*F(1,5), F(1))

# ---------------------------------------------------------------- Section 4
# storage counterexample
ok("false certificate from initial reserve", lower(F(6), F(18,5), B, e, s, F(2), F(0)), F(17,10))
ok("correct pre-wash certificate",           lower(F(6), F(18,5), B, e, s, F(4), F(0)), F(0))
ok("uptake route J0 = Rbar+Tbar = 4",        lower(F(6), F(18,5), B, e, s, F(2)+F(2), F(0)), F(0))
# uptake route on the worked record
ok("uptake route certifies 1.6 iff Tbar <= 9/85",
   lower(q1, q2, B, e, s, F(2)+F(9,85), H), F(8,5))
ok("uptake route ties 1.52 at Tbar = 1/5",
   lower(q1, q2, B, e, s, F(2)+F(1,5), H), F(38,25))

# ---------------------------------------------------------------- randomized
# soundness + attainment of the closed form against a direct schedule replay
import itertools, random
random.seed(20260917)
def replay(q1, q2, B, e, s, J, H, R0):
    """Rebuild the attaining schedule and return its total fresh amount,
    asserting every nonnegativity and availability constraint."""
    A = max(F(0), q1-B); x = max(F(0), B-q1); r = min(J, x); p = x - r
    U = max(F(0), R0+A-r); T = max(F(0), r-R0-A)
    P0 = B - R0
    assert min(P0, R0, A, U, T, q1) >= 0
    assert U <= R0 + A                       # release_available
    assert U <= R0 + A + T                   # enoughR
    assert T + q1 <= P0 + U                  # enoughP
    p1 = P0 + U - T - q1; r1 = R0 + A + T - U
    assert p1 == p and r1 == r and r <= J
    p20 = e*p; r20 = s*r + H
    F2 = max(F(0), q2 - H - (e*p + s*r))
    V = max(F(0), q2 - e*p)
    assert V <= r20 + F2 and p20 + V - q2 >= 0 and r20 + F2 - V >= 0
    return A + F2, T

cases = 0
grid = [F(0), F(1,4), F(1), F(7,2), F(6), F(10)]
for q1_, q2_, B_, J_, H_ in itertools.product(grid, grid, grid, grid, [F(0), F(1,5), F(1)]):
    for e_, s_ in [(F(0),F(0)), (F(0),F(1)), (F(1,20),F(9,10)), (F(1,2),F(1,2)), (F(1),F(1)), (F(9,10),F(9,10))]:
        for R0_ in [F(0), B_/2, B_]:
            tot, T = replay(q1_, q2_, B_, e_, s_, J_, H_, R0_)
            assert tot == lower(q1_, q2_, B_, e_, s_, J_, H_)
            assert tot == closed(q1_, q2_, B_, e_, s_, J_, H_)
            assert T <= max(F(0), min(J_, B_) - R0_)
            cases += 1
for _ in range(4000):
    q1_ = F(random.randint(0,400), 20); q2_ = F(random.randint(0,400), 20)
    B_  = F(random.randint(0,400), 20); J_  = F(random.randint(0,400), 20)
    H_  = F(random.randint(0,60), 20)
    e_  = F(random.randint(0,20), 20); s_ = F(random.randint(int(e_*20),20), 20)
    R0_ = F(random.randint(0,20),20) * B_
    tot, T = replay(q1_, q2_, B_, e_, s_, J_, H_, R0_)
    assert tot == lower(q1_, q2_, B_, e_, s_, J_, H_)
    assert tot == closed(q1_, q2_, B_, e_, s_, J_, H_)
    assert T <= max(F(0), min(J_, B_) - R0_)
    cases += 1

print(f"{len(checks)} printed values reproduced exactly.")
print(f"{cases} exact-rational attainment replays agreed with both forms of L.")
