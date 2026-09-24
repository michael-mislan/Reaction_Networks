"""Replay every printed identity and number of main.tex in exact arithmetic.

Needs sympy only.  Ends with a JSON report whose "status" must be "PASS".
No search, no simulation, no floating point in any assertion.
"""
import itertools
import json
import sympy as s

R = s.Rational
report = {"sympy": s.__version__, "checks": []}


def ok(name, cond):
    assert cond, name
    report["checks"].append(name)


# --------------------------------------------------------------------------
# Section 3.1  necessity counterexample
a, b, c, d = s.symbols("a b c d")
fa, fb, fc = -a*b + b - a*c + 3*c, b*(a - 2), c*(a - 3) + b
ok("3.1 field sums to zero", s.expand(fa + fb + fc) == 0)
ok("3.1 positive branch steady", all(s.expand(f.subs({a: 2, b: c})) == 0 for f in (fa, fb, fc)))
ok("3.1 witness for 3", s.expand((a - 3)*c*(a - 2) - ((a - 2)*fc - fb)) == 0)
ok("3.1 zero (2,1,1)", all(f.subs({a: 2, b: 1, c: 1}) == 0 for f in (fb, fc)))
ok("3.1 zero (3,0,1)", all(f.subs({a: 3, b: 0, c: 1}) == 0 for f in (fb, fc)))
ok("3.1 c(a-2) at (3,0,1)", (c*(a - 2)).subs({a: 3, c: 1}) == 1)
G = s.groebner([fb, fc], b, a, c, order="lex")
ok("3.1 quotient generator", any(s.expand(p.as_expr() - c*(a - 2)*(a - 3)) == 0 or
                                 s.expand(p.as_expr() + c*(a - 2)*(a - 3)) == 0 for p in G.polys))

# Section 3.2  sufficiency counterexample, built from the literal reactions
sp = (a, b, c, d)
rx = [((2, 0, 0, 0), (1, 0, 1, 0), 1), ((0, 0, 1, 0), (1, 0, 0, 1), 1), ((0, 0, 0, 1), (1, 1, 0, 0), 1),
      ((1, 1, 0, 0), (0, 1, 0, 0), 1), ((0, 1, 0, 0), (1, 1, 0, 0), 1), ((1, 0, 0, 0), (0, 0, 0, 0), 1),
      ((0, 2, 0, 0), (0, 0, 0, 0), R(1, 2))]
ok("3.2 bimolecular", all(sum(y) <= 2 and sum(yp) <= 2 for y, yp, _ in rx))
F = [s.expand(sum(k*s.prod(x**e for x, e in zip(sp, y))*(yp[i] - y[i]) for y, yp, k in rx)) for i in range(4)]
FA, FB, FC, FD = F
ok("3.2 field", [FA, FB, FC, FD] == [s.expand(-a**2 + c + d - a*b + b - a), d - b**2, a**2 - c, c - d])
ok("3.2 identity 1", s.expand(FA + 2*FC + FD - (a - 1)*(a - b)) == 0)
ok("3.2 identity 2", s.expand(FB + FC + FD - (a - b)*(a + b)) == 0)
ok("3.2 comaximal", s.expand((a - b) - 2*(a - 1) + (a + b)) == 2)
ok("3.2 zero (1,-1,1,1)", all(f.subs({a: 1, b: -1, c: 1, d: 1}) == 0 for f in F))
tau = s.symbols("tau", positive=True)
ok("3.2 positive curve", all(s.expand(f.subs({a: tau, b: tau, c: tau**2, d: tau**2})) == 0 for f in F))
Gam = s.Matrix([[yp[i] - y[i] for y, yp, _ in rx] for i in range(4)])
ok("3.2 stoichiometric rank 4", Gam.rank() == 4)
ok("3.2 raw rank 3 on curve", s.Matrix(F).jacobian(sp).subs({a: tau, b: tau, c: tau**2, d: tau**2}).rank() == 3)

# --------------------------------------------------------------------------
# Section 4  order example
u, v, t = s.symbols("u v t")
ideal = [u*t - v, v*t - u]
ok("4 torsion identity", s.expand((t - 1)*(u + v) - (ideal[0] + ideal[1])) == 0)
ok("4 u^2-v^2 in I", s.expand(u**2 - v**2 - (v*ideal[0] - u*ideal[1])) == 0)
mixed = s.groebner(ideal, u, v, t, order=lambda e: (e[0] + e[1], e[2], e[0]))
ok("4 mixed reduced basis", set(p.as_expr() for p in mixed.polys) == {u*u - v*v, t*u - v, t*v - u})
block = s.groebner(ideal, u, v, t, order="lex")
ok("4 lex basis", set(p.as_expr() for p in block.polys) == {u - t*v, t**2*v - v})


def candidates(basis, key):
    coeffs = []
    for poly in basis.polys:
        terms = s.Poly(poly.as_expr(), u, v).terms()
        coeffs.append(max(terms, key=lambda term: key(term[0]))[1])
    roots = sorted(set(r for p in coeffs for r in s.Poly(p, t).real_roots() if r.is_positive))
    return coeffs, roots


cm, rm = candidates(mixed, lambda e: (sum(e), e[0]))
ok("4 mixed leading coefficients", sorted(map(str, cm)) == sorted(["1", "t", "-1"]) and rm == [])
_, rb = candidates(block, lambda e: e)
ok("4 block candidates", rb == [1])


def N(p):
    out = 0
    for (i, j, k), co in s.Poly(p, u, v, t).terms():
        dd = i + j
        out += co*(t**k if dd == 0 else u**((i + k) % 2)*v**(dd - (i + k) % 2))
    return s.expand(out)


mons = [u**i*v**j*t**k for i, j, k in itertools.product(range(4), repeat=3)]
ok("4 normal form kills I", all(N(m*g) == 0 for m in mons for g in ideal))
# Remark 4.2: specialisation at t=2
spec = [p.as_expr().subs(t, 2) for p in mixed.polys]
ok("4.2 v in specialised ideal", s.expand(3*v - (2*(2*v - u) + (2*u - v))) == 0)
lead = [max(s.Poly(p, u, v).terms(), key=lambda term: (sum(term[0]), term[0][0]))[0] for p in spec]
ok("4.2 leaders u^2,u,u", sorted(lead) == sorted([(2, 0), (1, 0), (1, 0)]))

# --------------------------------------------------------------------------
# Section 6 minors
ok("6 necessity minor", s.Matrix([fb, fc]).jacobian([a, b]).det().subs({a: 2, b: 1, c: 1}) == 1)
ok("6 order minor", s.Matrix([v - t*u, u - t*v]).jacobian([t, u]).det().subs({t: 1, u: 1, v: 1}) == -2)
Q = (a - 1)**2 + (b - 2)**2
ok("6 Example 3.11 Jacobian zero", s.Matrix([a*Q, b*Q]).jacobian([a, b]).subs({a: 1, b: 2}) == s.zeros(2))

# EnvZ field from the nine literal reactions
x = s.symbols("x1:8")
k = s.symbols("k1:10", positive=True)
E = lambda *idx: tuple(1 if i in idx else 0 for i in range(7))
rxe = [(E(0), E(1)), (E(1), E(0)), (E(1), E(2)), (E(2, 3), E(5)), (E(5), E(2, 3)), (E(5), E(0, 4)),
       (E(1, 4), E(6)), (E(6), E(1, 4)), (E(6), E(1, 3))]
env = [s.expand(sum(ki*s.prod(xx**e for xx, e in zip(x, src))*(dst[i] - src[i]) for ki, (src, dst) in zip(k, rxe)))
       for i in range(7)]
printed = [-k[0]*x[0] + k[1]*x[1] + k[5]*x[5],
           k[0]*x[0] - (k[1] + k[2])*x[1] - k[6]*x[1]*x[4] + (k[7] + k[8])*x[6],
           k[2]*x[1] - k[3]*x[2]*x[3] + k[4]*x[5],
           -k[3]*x[2]*x[3] + k[4]*x[5] + k[8]*x[6],
           k[5]*x[5] - k[6]*x[1]*x[4] + k[7]*x[6],
           k[3]*x[2]*x[3] - (k[4] + k[5])*x[5],
           k[6]*x[1]*x[4] - (k[7] + k[8])*x[6]]
ok("9 printed field = literal field", all(s.expand(p - q) == 0 for p, q in zip(printed, env)))
psi = s.Matrix([env[i] for i in (0, 2, 4, 5, 6)])
minor = psi.jacobian([x[i] for i in (0, 2, 4, 5, 6)]).det()
ok("6.7 EnvZ minor", s.expand(minor + k[0]*k[3]*k[5]*k[6]*k[8]*x[1]*x[3]) == 0)
ok("9 conservation laws", s.expand(sum(env[i] for i in (0, 1, 2, 5, 6))) == 0 and s.expand(sum(env[i] for i in (3, 4, 5, 6))) == 0)
ea = k[2]*(k[7] + k[8])/(k[6]*k[8])
Cc = (k[4] + k[5])*k[2]/(k[3]*k[5])
KK = k[2]/k[5] + k[2]/k[8]
LL = (k[1] + k[2])/k[0] + 1 + KK
ok("9.1 certificate 1", s.expand(k[8]*env[6] - (k[7] + k[8])*(env[2] - env[3]) - k[6]*k[8]*x[1]*(x[4] - ea)) == 0)
ok("9.1 certificate 2", s.expand(k[2]*env[6] - k[6]*x[4]*(env[2] - env[3]) - k[6]*k[8]*x[6]*(x[4] - ea)) == 0)
tt, yy = s.symbols("t_ y_", positive=True)
ep = [(k[1] + k[2])/k[0]*tt, tt, Cc*tt/yy, yy, ea, k[2]/k[5]*tt, k[2]/k[8]*tt]
sub = dict(zip(x, ep))
ok("9.2 parametrisation steady", all(s.simplify(f.subs(sub)) == 0 for f in env))
ok("9.2 totals", s.simplify(sum(ep[i] for i in (0, 1, 2, 5, 6)) - (LL*tt + Cc*tt/yy)) == 0 and
   s.simplify(sum(ep[i] for i in (3, 4, 5, 6)) - (ea + yy + KK*tt)) == 0)
Xt, U, Ls, Cs, Ks = s.symbols("Xt U L C K", positive=True)
ok("9.2 quadratic", s.simplify((yy + Ks*Xt*yy/(Ls*yy + Cs) - U)*(Ls*yy + Cs) - (Ls*yy**2 + (Cs + Ks*Xt - Ls*U)*yy - Cs*U)) == 0)
e3, e4, e7 = s.symbols("e3 e4 e7")
g1 = (k[8]*e7 + (k[7] + k[8])*(e3 + e4))/(k[6]*k[8]*tt)
g2 = (k[2]*e7 + k[6]*ea*(e3 + e4))/(k[6]*k[8]*(k[2]/k[8]*tt))
ok("9 gains coincide at equilibrium", s.simplify(g1 - g2) == 0)


# interval helpers (exact rationals)
def add(A, B): return A[0] + B[0], A[1] + B[1]
def neg(A): return -A[1], -A[0]
def mul(A, B):
    p = [x_*y_ for x_ in A for y_ in B]
    return min(p), max(p)
def div(A, B):
    assert B[0] > 0
    return mul(A, (1/B[1], 1/B[0]))
def const(z): return (s.sympify(z),)*2


kb = (R(99, 100), R(101, 100))
eal = div(mul(kb, add(kb, kb)), mul(kb, kb))
Cb = div(mul(add(kb, kb), kb), mul(kb, kb))
ekb = add(div(kb, kb), div(kb, kb))
Lb = add(add(div(add(kb, kb), kb), const(1)), ekb)
Umin = 4 - eal[1]
ymin = Umin/(1 + ekb[1]*2/Cb[0])
tmin = 1*ymin/(Lb[1]*ymin + Cb[1])
x7min = kb[0]/kb[1]*tmin
ok("9 alpha interval", eal == (R(19602, 10201), R(20402, 9801)))
ok("9 y_-", ymin == R(1861398, 3030901))
ok("9 t_-", tmin == R(9121780899, 77264239204) and tmin > R(118, 1000))
gain1 = (kb[1] + 2*(kb[1] + kb[1]))/(kb[0]**2*tmin)
gain2 = (kb[1] + 2*kb[1]*eal[1])/(kb[0]**2*x7min)
ok("9 gains", gain1 < R(4365, 100) and gain2 < R(4599, 100))

# --------------------------------------------------------------------------
# Section 8 reactor
k1, k2, k3, k4, k5, D, ci, ell = s.symbols("k1 k2 k3 k4 k5 D ci ell", positive=True)
f = s.Matrix([-k1*a*b + k2*b - k4*a*c + k5*c + D*(ci - a) - ell*a, k1*a*b - (k2 + k3 + D)*b, k4*a*c - (k5 + D)*c + k3*b])
alpha = (k2 + k3 + D)/k1
Delta = k5 + D - k4*alpha
Nn = ci - alpha*(1 + ell/D)
r = Delta/k3
ok("8 total", s.simplify(sum(f) - D*(ci - a - b - c) + ell*a) == 0)
eq = {a: alpha, b: r*Nn/(1 + r), c: Nn/(1 + r)}
ok("8.1 equilibrium", all(s.simplify(fi.subs(eq)) == 0 for fi in f))
sg, ta, de, lam = s.symbols("sigma tau_ Delta_ lambda_")
J = f.jacobian([a, b, c]).subs(a, alpha).subs({b: sg/k1, c: ta/k4, k5: de - D + k4*alpha})
A1 = D + ell + de + sg + ta
A2 = de*(D + ell) + sg*(de + k3 + D) + D*ta
A3 = D*sg*(de + k3)
ok("8.2 characteristic polynomial", s.simplify(J.charpoly(lam).as_expr() - (lam**3 + A1*lam**2 + A2*lam + A3)) == 0)
mu, nu, B1, B2, B3 = s.symbols("mu nu B1 B2 B3", real=True)
z = mu + s.I*nu
poly = s.expand(z**3 + B1*z**2 + B2*z + B3)
re_, im_ = s.re(poly), s.im(poly)
ok("8.2 imaginary part", s.expand(im_ - nu*(3*mu**2 - nu**2 + 2*B1*mu + B2)) == 0)
nu2 = 3*mu**2 + 2*B1*mu + B2
re_sub = s.expand(mu**3 - 3*mu*nu2 + B1*(mu**2 - nu2) + B2*mu + B3)
ok("8.2 real part", s.expand(re_ - (mu**3 - 3*mu*nu**2 + B1*(mu**2 - nu**2) + B2*mu + B3)) == 0)
ok("8.2 real part substitution", s.expand(re_sub + (8*mu**3 + 8*B1*mu**2 + 2*(B1**2 + B2)*mu + B1*B2 - B3)) == 0)
nom = {k1: R(1, 20), k2: R(1, 20), k3: R(1, 20), k4: R(1, 20), k5: R(3, 20), D: R(1, 100), ci: 10}
ok("8.3 nominal", alpha.subs(nom) == R(11, 5) and Delta.subs(nom) == R(1, 20) and r.subs(nom) == 1)
ok("8.3 pools", eq[b].subs(nom).subs(ell, 0) == R(39, 10) and eq[b].subs(nom).subs(ell, R(1, 50)) == R(17, 10))
ok("8.3 fluxes", R(1, 50)*R(11, 5) == R(44, 1000) and (D*(ci - alpha)).subs(nom) == R(78, 1000))
ok("8.3 critical load", (D*(ci/alpha - 1)).subs(nom) == R(39, 1100))
ok("8.3 floor load", (D/alpha*(ci - alpha - (1 + r)/r*1)).subs(nom) == R(29, 1100))
ok("8.3 conditional bound", R(1, 1000)/(R(1, 20)*1) == R(1, 50))
Kb = {q: (R(99, 100)*val, R(101, 100)*val) for q, val in nom.items() if q in (k1, k2, k3, k4, k5)}
al = div(add(add(Kb[k2], Kb[k3]), const(R(1, 100))), Kb[k1])
delbox = add(add(Kb[k5], const(R(1, 100))), neg(mul(Kb[k4], al)))
nb = add((R(99, 10), R(101, 10)), neg(mul(al, add(const(1), div((R(99, 5000), R(101, 5000)), const(R(1, 100)))))))
rb = div(delbox, Kb[k3])
bmin = rb[0]*nb[0]/(1 + rb[0])
ok("8.3 box", al == (R(218, 101), R(74, 33)) and delbox[0] == R(2987, 66000) and nb[0] == R(5161, 1650)
   and rb[0] == R(2987, 3333) and bmin == R(15415907, 10428000) and bmin > R(147, 100))
ok("8.3 setpoint interval", R(2158, 1000) < al[0] and al[1] < R(2243, 1000))

# Proposition 8.4 ellipsoid
loaded = {**nom, ell: R(1, 50)}
xs = {a: R(11, 5), b: R(17, 10), c: R(17, 10)}
Jn = f.jacobian([a, b, c]).subs(loaded).subs(xs)
Jp = s.Matrix([[R(-1, 5), R(-3, 50), R(1, 25)], [R(17, 200), 0, 0], [R(17, 200), R(1, 20), R(-1, 20)]])
ok("8.4 J", Jn == Jp)
ua, ub, uc = s.symbols("ua ub uc")
uvec = s.Matrix([ua, ub, uc])
shifted = f.subs(loaded).subs({a: xs[a] + ua, b: xs[b] + ub, c: xs[c] + uc}, simultaneous=True)
Rv = R(1, 20)*ua*s.Matrix([-(ub + uc), ub, uc])
ok("8.4 u' = Ju + R(u)", (shifted - Jp*uvec - Rv).expand() == s.zeros(3, 1))
P = s.Matrix([[R(95, 4), R(4075, 142), R(3025, 142)], [R(4075, 142), R(57115, 1207), R(1735, 71)], [R(3025, 142), R(1735, 71), R(1920, 71)]])
ok("8.4 Lyapunov", Jp.T*P + P*Jp == -s.eye(3))
ok("8.4 minors", [P[:i, :i].det() for i in (1, 2, 3)] == [R(95, 4), R(51472525, 171394), R(401489125, 171394)])
Ctr = P.trace()
ok("8.4 trace", Ctr == R(473685, 4828))
M = s.Matrix([[0, R(1405, 568), R(-695, 568)], [R(1405, 568), R(44955, 2414), R(-40, 71)], [R(-695, 568), R(-40, 71), R(815, 142)]])
ok("8.4 cubic form", s.expand(2*(P*uvec).dot(Rv) - R(1, 10)*ua*(uvec.T*M*uvec)[0]) == 0)
F2 = sum(e**2 for e in M)
ok("8.4 Frobenius", F2 == R(9221492725, 23309584) and F2 < 400)
Pi = P.inv()
ok("8.4 P^-1 diagonal", [Pi[i, i] for i in range(3)] == [R(4678958, 16059565), R(2583847, 32119130), R(2058901, 16059565)])
rho = R(1, 5)
ok("8.4 (a) coordinate bounds", Pi[0, 0]*rho < R(1, 16) and Pi[1, 1]*rho < R(127, 1000)**2 and Pi[2, 2]*rho < R(161, 1000)**2)
ok("8.4 (c) gain", 1/(R(1, 20)*R(1573, 1000)) < R(1272, 100))
ok("8.4 (c) average", s.log(R(1827, 1573)) < R(3, 20))
ok("8.4 (d) ball", Ctr*R(45, 1000)**2 < R(1987, 10000) and R(1987, 10000) < rho)


# --------------------------------------------------------------------------
# Section 7 checker
def polybox(p, variables, box):
    result = const(0)
    for mon, co in s.Poly(s.expand(p), *variables).terms():
        term = const(co)
        for xx, n_ in zip(variables, mon):
            lo, hi = box[str(xx)]
            if n_ == 0:
                zz = const(1)
            elif n_ % 2 == 0 and lo <= 0 <= hi:
                zz = (s.Integer(0), max(lo**n_, hi**n_))
            else:
                zz = (min(lo**n_, hi**n_), max(lo**n_, hi**n_))
            term = mul(term, zz)
        result = add(result, term)
    return result


def check_certificate(cert, field):
    xsym = s.symbols(" ".join(cert["species"]))
    loc = dict(zip(cert["species"], xsym))
    parse = lambda zz: s.sympify(zz, locals=loc)
    h = parse(cert["h"]); q = list(map(parse, cert["q"])); al_ = parse(cert["alpha"]); m = cert["m"]
    if s.expand((xsym[cert["coordinate"]] - al_)**m*h - sum(qi*fi for qi, fi in zip(q, field))) != 0:
        raise ValueError("identity fails against literal field")
    box = {xx: tuple(map(R, cert["domain"][xx])) for xx in cert["species"]}
    hlo, hhi = polybox(h, xsym, box)
    floor = max(hlo, -hhi)
    h0 = R(cert["h0"])
    if h0 <= 0 or floor < h0:
        raise ValueError("unsupported witness floor (inconclusive)")
    Q_ = [max(abs(lo), abs(hi)) for lo, hi in (polybox(qi, xsym, box) for qi in q)]
    eps = list(map(R, cert["residual_bounds"]))
    dist = list(map(parse, cert.get("disturbance", ["0"]*len(field))))
    signed = s.expand(sum(qi*di for qi, di in zip(q, dist)))
    dl, du = polybox(signed, xsym, box)
    eta = max(abs(dl), abs(du))
    return ((sum(x_*y_ for x_, y_ in zip(Q_, eps)) + eta)/h0)**R(1, m), eta


fnum = [fi.subs(loaded) for fi in f]
cert = {"species": ["a", "b", "c"], "coordinate": 0, "alpha": "11/5", "m": 1, "h": "b/20", "h0": "1/20",
        "q": ["0", "1", "0"], "domain": {"a": ["0", "10"], "b": ["1", "5"], "c": ["0", "10"]},
        "residual_bounds": ["0", "1/1000", "0"], "disturbance": ["-a/50", "0", "0"]}
bound, eta = check_certificate(cert, fnum)
ok("7 checker accepts", bound == R(1, 50) and eta == 0)
for bad in ({**cert, "h": "b/10"}, {**cert, "domain": {**cert["domain"], "b": ["0", "5"]}}):
    try:
        check_certificate(bad, fnum)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid certificate accepted")
ok("7 checker rejects wrong identity and unsupported floor", True)

# --------------------------------------------------------------------------
# Section 10 release: three-product example  y -> P1+P2+P3 with two intermediates
Fx, l1, l2, z1, z2 = s.symbols("F lambda1 lambda2 z1 z2", positive=True)
E1, E2 = Fx - l1*z1, Fx - l2*z2
ok("10 intermediate equations", s.expand((l1*z1 - l2*z2) - (E2 - E1)) == 0)
ok("10 old field", s.expand((l1*z1 + 2*l2*z2) - (3*Fx - (1*E1 + 2*E2))) == 0)
ok("10 leak yield", R(100, 101)**3 == R(1000000, 1030301))
ok("10 storage", [3*1/R(q) for q in ("1", "1/10", "1/100")] == [3, 30, 300])
aa, bb = s.symbols("aa bb")
ok("10 product-loss step", s.expand(1 - aa*bb - ((1 - aa) + aa*(1 - bb))) == 0)

report["status"] = "PASS"
report["count"] = len(report["checks"])
print(json.dumps(report, indent=1))
