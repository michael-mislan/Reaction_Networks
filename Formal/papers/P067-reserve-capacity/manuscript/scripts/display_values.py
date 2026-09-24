r"""Exact rational values quoted in the merged manuscript."""
from fractions import Fraction as F
from decimal import Decimal, getcontext
getcontext().prec = 40

M61 = F(61, 200)          # healthy mortality ceiling m = .305
TGT = F(107, 12500)       # certified target-survival bound


def dec(x, n=12):
    return str(Decimal(x.numerator) / Decimal(x.denominator))[:n + 2]


def reserve(K, hmin, M, reff=F(1), m=M61, T=120):
    P = {hmin - 1: F(1)}
    for h in range(hmin, M):
        P[h] = P[h - 1] * K * m / (reff * (K - h))
    DM = sum(P.values(), F(0))
    return P, DM, M * m * T * P[M - 1]


print("### K = 400, h_min = 200, M = 278, r_eff = 1, m = 61/200, T = 120")
P, D, simple = reserve(400, 200, 278)
q = simple / D
print("  simple  M m T P_{M-1} =", dec(simple, 16), " < 7e-6")
print("  D_M                   =", dec(D, 16))
print("  sharp   M m T q_M     =", dec(q, 16))
print()
print("### extended initial filling (Corollary: incomplete preparation)")
for h0 in (209, 220, 221, 239, 240, 250, 260, 278):
    init = sum((v for j, v in P.items() if j >= h0), F(0)) / D if h0 < 278 else F(0)
    tot = init + q
    print(f"  H0={h0:3d}  initial={dec(init,12):>16}  total={dec(tot,12):>16}"
          f"  joint>{dec(1 - TGT - tot, 10)}")
h209 = sum((v for j, v in P.items() if j >= 209), F(0)) / D + q
h240 = sum((v for j, v in P.items() if j >= 240), F(0)) / D + q
assert h209 < F(1, 100) and h240 < F(3, 10 ** 6)
assert sum((v for j, v in P.items() if j >= 208), F(0)) / D + q > F(1, 100)
print("  -> 209 is the exact minimum meeting alpha = 1/100 ; 208 fails")
print("  -> joint at H0>=209 :", dec(1 - TGT - h209, 10))
print("  -> joint at H0>=240 :", dec(1 - TGT - h240, 10))

print()
print("### smaller sufficient reserve, theta = 1/2, M = floor(.695 K)")
for K in (232, 252):
    hmin = -(-K // 2)
    M = int(F(695, 1000) * K)
    P2, D2, s2 = reserve(K, hmin, M)
    print(f"  K={K}, h_min={hmin}, M={M}:  simple={dec(s2,12)}   sharp={dec(s2/D2,12)}"
          f"   D_M={dec(D2,10)}")
    print(f"        joint (sharp) > {dec(1 - TGT - s2/D2, 10)}   "
          f"joint (simple) > {dec(1 - TGT - s2, 10)}")
_, D232, s232 = reserve(232, 116, 161)
assert s232 / D232 < F(1, 100) and s232 > F(1, 100)
# confirm 232 is minimal for the sharpened bound over this proportional family
for K in range(150, 232):
    hmin = -(-K // 2)
    M = int(F(695, 1000) * K)
    if hmin > M:
        continue
    p3, d3, s3 = reserve(K, hmin, M)
    assert s3 / d3 >= F(1, 100), K
print("  -> 232 is minimal for the sharpened bound in this proportional family;"
      " 252 is minimal for the cruder product")

print()
print("### benchmark rows, K = 20, m = 61/100, T = 120, M = K = 20")
for reff in (F(12), F(9)):
    _, _, s = reserve(20, 10, 20, reff=reff, m=F(61, 100))
    print(f"  r_eff={reff}: {dec(s,12)}")

print()
print("### assembly")
print("  1 - 107/12500 - 7/10^6 =", dec(1 - TGT - F(7, 10 ** 6), 10))
print("  LP ceiling row: 67*(3/10)/73 + 1/10 =", dec(F(67 * 3, 10 * 73) + F(1, 10), 10))
