"""Exact model builder and interval Hopf certifier for the sequential
distributive n-site phosphorylation cycle

    S_{i-1} + E <-> C_i -> S_i + E,      S_i + F <-> D_i -> S_{i-1} + F.

Everything here is built from the literal reaction list.  Exact objects are
SymPy rationals; rigorous enclosures use the outward-rounded dyadic rational
intervals of ``interval_arithmetic.py``.  Nothing in this file is a Lean proof.

Species order:  S_0..S_n, E, F, C_1..C_n, D_1..D_n      (3n+3 species)
Chart order  :  u_1..u_n, C_1..C_n, D_1..D_n             (3n coordinates)
"""
from fractions import Fraction as Fr
import sympy as sp
from interval_arithmetic import I, C, solve, dot, BITS

t = sp.Symbol('t')


def R_(v):
    return sp.Rational(str(v)) if not isinstance(v, sp.Basic) else v


class Model:
    """Literal mass-action source at a prescribed positive equilibrium."""

    def __init__(self, n, x, q, rho, sigma, clampE=False, clampF=False):
        self.n = n
        self.x = [R_(v) for v in x]
        self.q = [R_(v) for v in q]
        self.ratio = [R_(v) for v in rho] + [R_(v) for v in sigma]
        self.clampE, self.clampF = clampE, clampF
        assert len(self.x) == 3*n + 3 and len(self.q) == n and len(self.ratio) == 2*n
        self.iE, self.iF = n + 1, n + 2
        m = 2*n
        # arm j < n : kinase arm C_{j+1};  arm j >= n : phosphatase arm D_{j-n+1}
        self.lev = [j for j in range(n)] + [j - n + 1 for j in range(n, m)]
        self.out = [j + 1 for j in range(n)] + [j - n for j in range(n, m)]
        self.enz = [self.iE]*n + [self.iF]*n
        self.cpx = [n + 3 + j for j in range(m)]
        self.site = [j % n for j in range(m)]
        ns = 3*n + 3
        self.N = sp.zeros(ns, 3*m)
        for j in range(m):
            s, e, c, o = self.lev[j], self.enz[j], self.cpx[j], self.out[j]
            self.N[s, 3*j] -= 1; self.N[e, 3*j] -= 1; self.N[c, 3*j] += 1      # binding
            self.N[s, 3*j+1] += 1; self.N[e, 3*j+1] += 1; self.N[c, 3*j+1] -= 1  # dissociation
            self.N[o, 3*j+2] += 1; self.N[e, 3*j+2] += 1; self.N[c, 3*j+2] -= 1  # catalysis
        self.kon, self.koff, self.kcat = [], [], []
        for j in range(m):
            qq = self.q[self.site[j]]
            self.kon.append((1 + self.ratio[j])*qq/(self.x[self.lev[j]]*self.x[self.enz[j]]))
            self.koff.append(self.ratio[j]*qq/self.x[self.cpx[j]])
            self.kcat.append(qq/self.x[self.cpx[j]])
        # chart
        self.P = sp.zeros(ns, 3*n)
        for l in range(n + 1):
            if l >= 1:
                self.P[l, l - 1] += 1
            if l + 1 <= n:
                self.P[l, l] -= 1
        for j in range(m):
            self.P[self.lev[j], n + j] -= 1
            self.P[self.cpx[j], n + j] = 1
            if not (clampE if j < n else clampF):
                self.P[self.enz[j], n + j] -= 1
        self.Rm = sp.zeros(3*n, ns)
        for i in range(1, n + 1):
            for l in range(i, n + 1):
                self.Rm[i - 1, l] = 1
            for j in range(m):
                if self.lev[j] >= i:
                    self.Rm[i - 1, self.cpx[j]] = 1
        for j in range(m):
            self.Rm[n + j, self.cpx[j]] = 1
        assert self.Rm*self.P == sp.eye(3*n)

    # ---------------- exact objects -----------------
    def rates(self):
        return dict(kon=self.kon, koff=self.koff, kcat=self.kcat)

    def fluxes(self, x=None):
        x = self.x if x is None else x
        v = []
        for j in range(2*self.n):
            v += [self.kon[j]*x[self.lev[j]]*x[self.enz[j]], self.koff[j]*x[self.cpx[j]],
                  self.kcat[j]*x[self.cpx[j]]]
        return sp.Matrix(v)

    def field(self, x=None):
        f = self.N*self.fluxes(x)
        if self.clampE: f[self.iE] = 0
        if self.clampF: f[self.iF] = 0
        return f

    def totals(self):
        n, x = self.n, self.x
        return (x[self.iE] + sum(x[n+3:2*n+3]), x[self.iF] + sum(x[2*n+3:]),
                sum(x[:n+1]) + sum(x[n+3:]))

    def full_jacobian(self):
        ns = 3*self.n + 3
        D = sp.zeros(6*self.n, ns)
        for j in range(2*self.n):
            D[3*j, self.lev[j]] = self.kon[j]*self.x[self.enz[j]]
            D[3*j, self.enz[j]] = self.kon[j]*self.x[self.lev[j]]
            D[3*j+1, self.cpx[j]] = self.koff[j]
            D[3*j+2, self.cpx[j]] = self.kcat[j]
        return self.N*D

    def jacobian(self):
        return self.Rm*self.full_jacobian()*self.P

    def hessian_rows(self):
        """Rows (s_j, e_j) of the lift with B(u,v)_{n+j}=kon_j (s_j.u e_j.v + s_j.v e_j.u)."""
        out = []
        for j in range(2*self.n):
            col = self.Rm*self.N[:, 3*j]
            assert col == sp.eye(3*self.n)[:, self.n + j]
            out.append((self.P[self.lev[j], :], self.P[self.enz[j], :]))
        return out

    def blocks(self):
        n = self.n; J = self.jacobian()
        return J[:n, n:], J[n:, :n], -J[n:, n:]          # L, M, A


def affine_charpoly(build, s=sp.Symbol('s')):
    """p(s,r)=p0(s)+r p1(s) for a family build(r) whose Jacobian is affine, rank one, in r."""
    c0 = build(sp.Integer(0)).jacobian().charpoly(s).all_coeffs()
    c1 = build(sp.Integer(1)).jacobian().charpoly(s).all_coeffs()
    c2 = build(sp.Integer(2)).jacobian().charpoly(s).all_coeffs()
    p1 = [b - a for a, b in zip(c0, c1)]
    assert c2 == [a + 2*b for a, b in zip(c0, p1)]
    return c0, p1


def even_odd(cs):
    """p(i sqrt t)=E(t)+i sqrt(t) O(t) for the coefficient list cs (descending)."""
    E = 0; O = 0; d = len(cs) - 1
    for i, c in enumerate(cs):
        k = d - i
        if k % 2: O += c*(-1)**((k-1)//2)*t**((k-1)//2)
        else: E += c*(-1)**(k//2)*t**(k//2)
    return sp.expand(E), sp.expand(O)


def ipoly(expr, iv):
    out = I(0)
    for c in sp.Poly(expr, t).all_coeffs():
        out = out*iv + I(str(c))
    return out


def routh_first_column(g):
    d = len(g) - 1
    width = d//2 + 1
    rows = [list(g[0::2]) + [I(0)]*(width - len(g[0::2])), list(g[1::2]) + [I(0)]*(width - len(g[1::2]))]
    while len(rows) < d + 1:
        a, b = rows[-2], rows[-1]
        rows.append([(b[0]*a[k+1] - a[0]*b[k+1])/b[0] for k in range(width - 1)] + [I(0)])
    return [r[0] for r in rows]


def imat(Mx):
    return [[I(str(v)) for v in Mx.row(i)] for i in range(Mx.rows)]


def hopf_core(J0, J1, makeBC, norm_index=None, eps=sp.Rational(1, 10**55), relax_rows=None):
    """Generic interval Hopf certificate for J(r)=J0+r(J1-J0) (exact SymPy matrices).

    makeBC(ri) returns (B, Cfun) acting on lists of complex intervals; Cfun may be None.
    Asserts: exactly one positive root of the frequency eliminant, simple; r>0;
    Hurwitz complementary factor; nonzero crossing; nonzero first Lyapunov coefficient.
    """
    dim = J0.rows; s = sp.Symbol('s')
    p0 = J0.charpoly(s).all_coeffs(); pa = J1.charpoly(s).all_coeffs()
    p1 = [b - a for a, b in zip(p0, pa)]
    assert (2*J1 - J0).charpoly(s).all_coeffs() == [a + 2*b for a, b in zip(p0, p1)]
    E0, O0 = even_odd(p0); E1, O1 = even_odd(p1)
    phi = sp.Poly(sp.expand(O0*E1 - E0*O1), t)
    pos = [(a, b, mult) for ((a, b), mult) in sp.polys.polytools.intervals(phi, eps=eps) if a > 0]
    assert len(pos) == 1, [(float(a), float(b)) for a, b, _ in pos]
    a, b, mult = pos[0]
    assert mult == 1 and phi.count_roots(a, b) == 1 and phi.count_roots(0, sp.oo) == 1
    ti = I(str(a), str(b)); omega = ti.sqrt()
    e0, o0, e1, o1 = (ipoly(v, ti) for v in (E0, O0, E1, O1))
    ri = -(e0*e1 + ti*o0*o1)/(e1*e1 + ti*o1*o1)
    assert ri.a > 0
    c0 = [I(str(v)) for v in p0]; c1 = [I(str(v)) for v in p1]
    p = [u + ri*v for u, v in zip(c0, c1)]
    g = []
    for k in range(dim - 1):
        g.append(p[k] - (ti*g[k-2] if k >= 2 else I(0)))
    routh = routh_first_column(g)
    assert all(v.a > 0 for v in routh)
    z = C(0, omega)
    def evalc(cs):
        out = C()
        for c in cs: out = out*z + C(c)
        return out
    dp = [p[k]*(dim - k) for k in range(dim)]
    lam_r = -evalc(c1)/evalc(dp)
    assert lam_r.re.b < 0 or lam_r.re.a > 0
    iJ0 = imat(J0); iD = imat(J1 - J0)
    J = [[iJ0[i][j] + ri*iD[i][j] for j in range(dim)] for i in range(dim)]
    Mz = [[C(J[i][j]) - (z if i == j else C()) for j in range(dim)] for i in range(dim)]
    k = dim - 1 if norm_index is None else norm_index
    rest = [i for i in range(dim) if i != k]
    rsol = solve([[Mz[i][j] for j in rest] for i in rest], [-Mz[i][k] for i in rest])
    lsol = solve([[Mz[j][i] for j in rest] for i in rest], [-Mz[k][i] for i in rest])
    right = [C(1)]*dim; left = [C(1)]*dim
    for pos_, i in enumerate(rest):
        right[i] = rsol[pos_]; left[i] = lsol[pos_]
    nrm = dot(left, right); left = [v/nrm for v in left]
    B, Cf = makeBC(ri)
    conj = [v.conj() for v in right]
    h11 = solve(J, B(right, conj))
    h20 = solve([[(2*z if i == j else C()) - C(J[i][j]) for j in range(dim)] for i in range(dim)], B(right, right))
    term = [-2*u + v for u, v in zip(B(right, h11), B(conj, h20))]
    if Cf is not None:
        term = [u + v for u, v in zip(term, Cf(right, right, conj))]
    g21 = dot(left, term); l1 = g21.re/(2*omega)
    assert l1.a > 0 or l1.b < 0
    # derivative of the critical eigenvalue along the relaxation path (sign check is done by the caller)
    res = dict(dim=dim, t=ti, r=ri, omega=omega, routh=routh, crossing=lam_r, l1=l1, g21=g21,
               right=right, left=left, p0=p0, p1=p1, J=J, B=B,
               const_coeff_positive=bool(p0[-1] > 0 and p1[-1] >= 0))
    if relax_rows is not None:
        dJ = [[(-J[i][j] if i in relax_rows else I(0)) for j in range(dim)] for i in range(dim)]
        res['eps_derivative'] = dot(left, [dot([C(v) for v in rw], right) for rw in dJ])
    return res


def model_B(m0, m1, ri):
    """Interval Hessian of the chart field of a Model family at parameter interval ri."""
    n = m0.n; dim = 3*n; rows = m0.hessian_rows()
    kon = [I(str(m0.kon[j])) + ri*I(str(m1.kon[j] - m0.kon[j])) for j in range(2*n)]
    srow = [[C(I(str(v))) for v in rows[j][0]] for j in range(2*n)]
    erow = [[C(I(str(v))) for v in rows[j][1]] for j in range(2*n)]
    def B(u, v):
        out = [C() for _ in range(dim)]
        for j in range(2*n):
            su, sv, eu, ev = dot(srow[j], u), dot(srow[j], v), dot(erow[j], u), dot(erow[j], v)
            out[n + j] = C(kon[j])*(su*ev + sv*eu)
        return out
    return B


def certify_hopf(build, norm_index=None):
    """Closed (or clamped) source family build(r): full chart field, quadratic."""
    m0, m1 = build(sp.Integer(0)), build(sp.Integer(1)); n = m0.n
    res = hopf_core(m0.jacobian(), m1.jacobian(), lambda ri: (model_B(m0, m1, ri), None),
                    norm_index=norm_index, relax_rows=set(range(n, 3*n)))
    res['n'] = n
    return res


def certify_reduced(build, fast, norm_index):
    """Local algebraic elimination of chart coordinate ``fast`` (F_fast=0 solved implicitly).

    The induced quadratic and cubic terms are those of Section 6 of the paper.
    norm_index refers to the full chart; the same coordinate is normalised in the reduction.
    """
    m0, m1 = build(sp.Integer(0)), build(sp.Integer(1)); n = m0.n; dim = 3*n
    slow = [i for i in range(dim) if i != fast]
    def red(J):
        d = -J[fast, fast]
        return sp.Matrix(len(slow), len(slow), lambda i, j: J[slow[i], slow[j]] + J[slow[i], fast]*J[fast, slow[j]]/d)
    J0f, J1f = m0.jacobian(), m1.jacobian()
    assert J0f.row(fast) == J1f.row(fast)            # fast row independent of r
    d = I(str(-J0f[fast, fast])); assert d.a > 0
    h1 = [C(I(str(J0f[fast, j]))/d) for j in slow]
    def makeBC(ri):
        Bfull = model_B(m0, m1, ri)
        Jsf = [C(I(str(J0f[i, fast])) + ri*I(str(J1f[i, fast] - J0f[i, fast]))) for i in slow]
        ef = [C(1) if i == fast else C() for i in range(dim)]
        def lift(u):
            out = [C()]*dim
            for pos_, i in enumerate(slow): out[i] = u[pos_]
            out[fast] = dot(h1, u)
            return out
        def h2(u, v): return Bfull(lift(u), lift(v))[fast]/C(d)
        def Bred(u, v):
            full = Bfull(lift(u), lift(v)); hh = full[fast]/C(d)
            return [full[i] + Jsf[pos_]*hh for pos_, i in enumerate(slow)]
        def Cred(u, v, w):
            out = [C()]*len(slow); h3 = C()
            for a_, (b_, c_) in ((u, (v, w)), (v, (u, w)), (w, (u, v))):
                be = Bfull(lift(a_), ef); hh = h2(b_, c_)
                out = [o + be[i]*hh for o, i in zip(out, slow)]
                h3 = h3 + be[fast]*hh
            h3 = h3/C(d)
            return [o + Jsf[pos_]*h3 for pos_, o in enumerate(out)]
        return Bred, Cred
    res = hopf_core(red(J0f), red(J1f), makeBC, norm_index=slow.index(norm_index))
    res['n'] = n
    return res


def gain_constants(build, cert, sensors):
    """|c^T (i omega - J(0))^{-1} e| r q1 for the exact resonance law of Section 8.

    Relative modulation of alpha_1 enters the chart row of D_1 only, as does r.
    """
    m0, m1 = build(sp.Integer(0)), build(sp.Integer(1)); n = m0.n; dim = 3*n
    row = 2*n                                                     # chart index of D_1
    D = m1.jacobian() - m0.jacobian()
    assert all(D[i, j] == 0 for i in range(dim) for j in range(dim) if i != row)
    z = C(0, cert['omega']); J0 = imat(m0.jacobian())
    e = [C(1) if i == row else C() for i in range(dim)]
    w = solve([[(z if i == j else C()) - C(J0[i][j]) for j in range(dim)] for i in range(dim)], e)
    vRe = dot([C(I(str(D[row, j]))) for j in range(dim)], w)       # equals 1/r exactly at the Hopf point
    out = {}
    for name, c in sensors.items():
        val = dot([C(I(str(v))) for v in c], w)*C(cert['r']*I(str(m0.q[0])))
        out[name] = (val.re*val.re + val.im*val.im).sqrt()
    return out, vRe


def parameter_gradient(build, cert):
    """d lambda / d(log k) for all 6n rate constants and d lambda/d(total) for the three totals,
    with the equilibrium moving (rates and the other totals held fixed)."""
    m0, m1 = build(sp.Integer(0)), build(sp.Integer(1)); n = m0.n; dim = 3*n; ns = 3*n + 3
    ri = cert['r']; J = cert['J']; left, right = cert['left'], cert['right']
    aff = lambda a0, a1: I(str(a0)) + ri*I(str(a1 - a0))
    x = [I(str(v)) for v in m0.x]
    kon = [aff(m0.kon[j], m1.kon[j]) for j in range(2*n)]
    koff = [aff(m0.koff[j], m1.koff[j]) for j in range(2*n)]
    kcat = [I(str(v)) for v in m0.kcat]
    P = imat(m0.P); RN = imat(m0.Rm*m0.N)
    Pq = [dot([C(v) for v in P[i]], right) for i in range(ns)]
    def hess_full(a, b):
        """R D^2 f (a,b) for species-space vectors a,b (lists of complex intervals)."""
        out = [C() for _ in range(dim)]
        for j in range(2*n):
            val = C(kon[j])*(a[m0.lev[j]]*b[m0.enz[j]] + b[m0.lev[j]]*a[m0.enz[j]])
            for i in range(dim): out[i] = out[i] + C(RN[i][3*j])*val
        return out
    def response(Fk, dJq):
        """Fk = dF/dk at equilibrium (chart), dJq = (dJ/dk at fixed state) q."""
        y1 = solve(J, [-v for v in Fk])
        Py1 = [dot([C(v) for v in P[i]], y1) for i in range(ns)]
        tot = [u + v for u, v in zip(dJq, hess_full(Py1, Pq))]
        return dot(left, tot)
    out = {}
    for j in range(2*n):
        s_, e_, c_ = m0.lev[j], m0.enz[j], m0.cpx[j]
        for kind, kval, mono, dmono in (
                ('on', kon[j], x[s_]*x[e_], lambda: C(x[e_])*Pq[s_] + C(x[s_])*Pq[e_]),
                ('off', koff[j], x[c_], lambda: Pq[c_]),
                ('cat', kcat[j], x[c_], lambda: Pq[c_])):
            col = 3*j + ('on', 'off', 'cat').index(kind)
            # derivative with respect to log k:  k * d/dk
            Fk = [C(RN[i][col]*kval*mono) for i in range(dim)]
            dJq = [C(RN[i][col]*kval)*dmono() for i in range(dim)]
            out[f'{kind}{j}'] = response(Fk, dJq)
    Df = imat(m0.full_jacobian()); Df1 = imat(m1.full_jacobian() - m0.full_jacobian())
    Dfull = [[Df[i][j] + ri*Df1[i][j] for j in range(ns)] for i in range(ns)]
    Rm = imat(m0.Rm)
    for name, idx in (('E_T', m0.iE), ('F_T', m0.iF), ('S_T', 0)):
        w = [C(1) if i == idx else C() for i in range(ns)]
        RDf_w = [dot([C(v) for v in Rm[i]], [C(Dfull[k][idx]) for k in range(ns)]) for i in range(dim)]
        y1 = solve(J, [-v for v in RDf_w])
        Py1 = [dot([C(v) for v in P[i]], y1) + w[i] for i in range(ns)]
        out[name] = dot(left, hess_full(Py1, Pq))
    return out


def bounds(v):
    if isinstance(v, I): return [str(v.a), str(v.b)]
    return dict(re=[str(v.re.a), str(v.re.b)], im=[str(v.im.a), str(v.im.b)])


def mid(v):
    if isinstance(v, I): return float((v.a + v.b)/2)
    return complex(float((v.re.a + v.re.b)/2), float((v.im.a + v.im.b)/2))


def width(v):
    if isinstance(v, I): return float(v.b - v.a)
    return max(float(v.re.b - v.re.a), float(v.im.b - v.im.a))


# ------------------------------------------------------------------ witnesses
XA = ['2', '12', '1/5', '2/5', '23/10', '2/5', '23/50', '3/10', '17/10', '23', '9/50', '4']
QA = ['1/10', '32/5', '6/5']
XH = ['30', '13', '19/100', '9/100', '33/10', '1', '13/25', '7/250', '39/50', '93/10', '3/20', '5/2']
QH = ['1/10', '39/5', '1']
HUNDREDTH = sp.Rational(1, 100)


def witness(which, r, **kw):
    x, q = (XA, QA) if which == 'A' else (XH, QH)
    return Model(3, x, q, [HUNDREDTH]*3, [r, HUNDREDTH, HUNDREDTH], **kw)


def extended(which, r, loads, **kw):
    """Append len(loads) sites with loads eps_k to a three-site witness (all-n section)."""
    x, q = (XA, QA) if which == 'A' else (XH, QH)
    x = [R_(v) for v in x]; q = [R_(v) for v in q]
    S, E, F_, Cs, Ds = x[:4], x[4], x[5], x[6:9], x[9:12]
    rho = [HUNDREDTH]*3; sigma = [r, HUNDREDTH, HUNDREDTH]
    for e in loads:
        e = R_(e)
        S = S + [2*e]; Cs = Cs + [e]; Ds = Ds + [e]; q = q + [e]
        rho = rho + [sp.Integer(1)]; sigma = sigma + [sp.Integer(1)]
    return Model(3 + len(loads), S + [E, F_] + Cs + Ds, q, rho, sigma, **kw)
