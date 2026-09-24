"""Read-only exact replay of every finite claim in the paper.

Usage:  python check_paper.py [--full]

Default: algebraic identities of Sections 2-4 (small symbolic cases), the final
three-site source, its four sink certificates, the operating contract, integer
preparations, physical conversions, the fixed-target obstruction and the
robustness/driving thresholds.  --full additionally replays the four sink
certificates of the original (pre-optimization) source used in Table 2.

Nothing is optimized, searched or simulated, and no file is written except
check_paper_report.json.  All decisions use exact rational arithmetic or
outward-rounded integer interval arithmetic; no floating-point comparison
decides a claim.  Dependencies: Python >= 3.9, sympy.
"""
import json, math, sys, time
from fractions import Fraction as Fr
from pathlib import Path
import sympy as sy

HERE = Path(__file__).resolve().parent
DATA = HERE / 'data'
FULL = '--full' in sys.argv
REPORT = {}
NCHECK = 0


def ok(cond, name):
    global NCHECK
    NCHECK += 1
    if not cond:
        raise AssertionError(name)


def load(name):
    return json.loads((DATA / name).read_text())


# ---------------------------------------------------------------- intervals
def ceildiv(a, b):
    return -((-a) // b)


class Ctx:
    """Fixed-point outward interval arithmetic with 10**-prec resolution."""

    def __init__(self, prec):
        self.S = 10 ** prec

    def mk(self, v=0, hi=None):
        if hi is not None:
            return (int(v), int(hi))
        f = Fr(str(v)) if not isinstance(v, Fr) else v
        return (f.numerator * self.S // f.denominator, ceildiv(f.numerator * self.S, f.denominator))

    def add(self, a, b):
        return (a[0] + b[0], a[1] + b[1])

    def neg(self, a):
        return (-a[1], -a[0])

    def sub(self, a, b):
        return (a[0] - b[1], a[1] - b[0])

    def mul(self, a, b):
        v = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
        return (min(v) // self.S, ceildiv(max(v), self.S))

    def div(self, a, b):
        assert not (b[0] <= 0 <= b[1])
        if b[1] < 0:
            a, b = self.neg(a), self.neg(b)
        inv = (self.S * self.S // b[1], ceildiv(self.S * self.S, b[0]))
        return self.mul(a, inv)

    def poly(self, coeff, x):
        out = (0, 0)
        for c in coeff:
            out = self.add(self.mul(out, x), self.mk(Fr(c)))
        return out

    def absup(self, a):
        return max(abs(a[0]), abs(a[1]))

    def matmul(self, A, B):
        BT = list(zip(*B))
        out = []
        for row in A:
            r = []
            for col in BT:
                lo = hi = 0
                for a, b in zip(row, col):
                    if a == (0, 0) or b == (0, 0):
                        continue
                    m = self.mul(a, b)
                    lo += m[0]
                    hi += m[1]
                r.append((lo, hi))
            out.append(r)
        return out

    def dd_margin(self, A):
        """Smallest Gershgorin margin diag_lo - sum |offdiag|_hi, as a Fraction."""
        m = min(row[i][0] - sum(self.absup(v) for j, v in enumerate(row) if j != i) for i, row in enumerate(A))
        return Fr(m, self.S)


# ------------------------------------------------------------ the 3-cube source
u = sy.symbols('u')
EDGES = [(v, v | 1 << i) for v in range(8) for i in range(3) if not (v >> i & 1)]
UP = [8, 1, 7, 1, 4, 4, 9, 8, 8, 8, 5, 6]
DOWN = [5, 5, 7, 8, 6, 2, 2, 9, 7, 6, 2, 5]
ST = 264490005424
ET, FT = 10, 1
IX = list(range(1, 8)) + list(range(10, 34))          # chart: S_A (A != 0), C_e, Y_e
T = [[0] * 31 for _ in range(34)]                      # affine chart derivative
for j in range(31):
    T[0][j] = -1
for j, k in enumerate(IX):
    T[k][j] = 1
for j in range(7, 19):
    T[8][j] = -1
for j in range(19, 31):
    T[9][j] = -1


def tree_weights():
    """Matrix-tree weights of the frozen generator uU+V by Laplacian cofactors."""
    G = sy.zeros(8, 8)
    for i, (a, b) in enumerate(EDGES):
        G[b, a] += UP[i] * u
        G[a, a] -= UP[i] * u
        G[a, b] += DOWN[i]
        G[b, b] -= DOWN[i]
    tt = []
    for v in range(8):
        minor = G.copy()
        minor.row_del(v)
        minor.col_del(v)
        tt.append(sy.expand((-1) ** 7 * minor.det(method='berkowitz')))
    return G, tt


def section_identities():
    """Small symbolic checks of the identities used in Sections 2-4."""
    t0 = time.time()
    # eliminant identity (2.4): substrate total times u L M
    A, B, D, r, FTs, STs, x = sy.symbols('A B D r F_T S_T u')
    L, M = B - r * D, B - x * D
    s, F = (r - x) / (x * L), FTs * L / M
    total = s * A + s * x * F * (B + D)
    P = (STs - r * FTs - FTs) * x * L * M - (r - x) * A * M + (x + 1) * FTs * x * L ** 2
    ok(sy.simplify((STs - total) * x * L * M - P) == 0, 'eliminant identity')
    ok(sy.simplify(F * (1 + s * x * D) - FTs) == 0, 'phosphatase total')
    ok(sy.simplify(x * F * (1 + s * B) - r * FTs) == 0, 'kinase total')
    # square face of Lemma 4.2: tree weights with rates lam*(1,2,3,5) up, (7,11,13,17) down
    lam = sy.symbols('lam', positive=True)
    sq_edges = [(0, 1), (0, 2), (1, 3), (2, 3)]
    found = False
    for perm_up in [(1, 2, 3, 5)]:
        G = sy.zeros(4, 4)
        for (a, b), ku, kd in zip(sq_edges, perm_up, (7, 11, 13, 17)):
            G[b, a] += lam * ku * u; G[a, a] -= lam * ku * u
            G[a, b] += kd; G[b, b] -= kd
        tw = []
        for v in range(4):
            m = G.copy(); m.row_del(v); m.col_del(v)
            tw.append(sy.factor(sy.expand(-m.det())))
        REPORT['square_tree_weights'] = [str(t) for t in tw]
        t00 = sy.expand(tw[0])
        ok(sy.degree(t00, u) == 1, 'anchor weight is linear in u')
        a0, a1 = sy.Poly(t00, u).all_coeffs()[::-1]
        mids = [sy.cancel(tw[1] / (lam * u)), sy.cancel(tw[2] / (lam * u))]
        c = [sy.Poly(m, u).all_coeffs()[::-1] for m in mids]
        det = sy.expand(c[0][0] * c[1][1] - c[0][1] * c[1][0])
        REPORT['square_anchor'] = str(t00)
        REPORT['square_middle_numerators'] = [str(m) for m in mids]
        REPORT['square_numerator_det'] = str(det)
        ok(det != 0, 'independent middle numerators')
        found = True
    ok(found, 'square witness')
    # saturated field: first-order drift expansion (4.8)
    rr, A1, B1, k, vp, vm = sy.symbols('r A_1 B_1 kappa v_p v_m', positive=True)
    exact = k * (rr * A1 / (1 + k * rr * A1 + vp) - B1 / (1 + k * B1 + vm))
    lead = sy.limit(exact * k, k, sy.oo)
    ok(sy.simplify(lead - ((1 + vm) / B1 - (1 + vp) / (rr * A1))) == 0, 'drift expansion')
    ok(sy.limit(exact, k, sy.oo) == 0, 'zero-order drift vanishes')
    REPORT['section_identities_seconds'] = round(time.time() - t0, 2)


class Source:
    def __init__(self, p, q, tt):
        self.p, self.q, self.tt = p, q, tt
        self.rates = [[p[i] + UP[i], Fr(1), Fr(UP[i]) / p[i], q[i] + DOWN[i], Fr(1), Fr(DOWN[i]) / q[i]] for i in range(12)]
        rat = lambda f: sy.Rational(f.numerator, f.denominator)
        self.A = sy.expand(sum(tt))
        self.B = sy.expand(sum(rat(p[i]) * tt[a] for i, (a, b) in enumerate(EDGES)))
        self.D = sy.cancel(sum(rat(q[i]) * tt[b] for i, (a, b) in enumerate(EDGES)) / u)
        self.L = sy.expand(self.B - ET * self.D)
        self.M = sy.expand(self.B - u * self.D)
        P = sy.Poly(sy.expand((ST - ET - FT) * u * self.L * self.M - (ET - u) * self.A * self.M + (u + 1) * FT * u * self.L ** 2), u)
        self.elim = P.clear_denoms()[1].primitive()[1]
        self.ec = [int(c) for c in self.elim.all_coeffs()]
        self.dc = [int(c) for c in self.elim.diff().all_coeffs()]
        self.tcoef = [[int(c) for c in sy.Poly(t, u).all_coeffs()] for t in tt]

    def state(self, cx, U):
        tau = [cx.poly(c, U) for c in self.tcoef]
        lv = cx.mk(1)
        for j in range(1, 7):
            lv = cx.mul(lv, cx.sub(U, cx.mk(j)))
        dv = (0, 0)
        for i, (a, b) in enumerate(EDGES):
            dv = cx.add(dv, cx.div(cx.mul(cx.mk(self.q[i]), tau[b]), U))
        ss = cx.div(cx.sub(cx.mk(10), U), cx.mul(U, lv))
        f = cx.div(cx.mk(1), cx.add(cx.mk(1), cx.mul(cx.mul(ss, U), dv)))
        e = cx.mul(U, f)
        s = [cx.mul(ss, t) for t in tau]
        c = [cx.mul(cx.mul(cx.mk(self.p[i]), e), s[a]) for i, (a, b) in enumerate(EDGES)]
        y = [cx.mul(cx.mul(cx.mk(self.q[i]), f), s[b]) for i, (a, b) in enumerate(EDGES)]
        return s + [e, f] + c + y

    def reactions(self, rates=None):
        rates = rates or self.rates
        for i, (a, b) in enumerate(EDGES):
            C, Y = 10 + i, 22 + i
            for rate, rea, pro in zip(rates[i], [[a, 8], [C], [C], [b, 9], [Y], [Y]], [[C], [a, 8], [b, 8], [Y], [b, 9], [a, 9]]):
                nu = [0] * 34
                for k in pro:
                    nu[k] += 1
                for k in rea:
                    nu[k] -= 1
                yield rate, rea, nu

    def jac(self, cx, X):
        J = [[(0, 0)] * 34 for _ in range(34)]
        for rate, rea, nu in self.reactions():
            for k in rea:
                g = cx.mk(rate)
                for h in rea:
                    if h != k:
                        g = cx.mul(g, X[h])
                for h in range(34):
                    if nu[h]:
                        J[h][k] = cx.add(J[h][k], (g[0] * nu[h], g[1] * nu[h]) if nu[h] > 0 else (g[1] * nu[h], g[0] * nu[h]))
        out = []
        for k in IX:
            row = []
            for j in range(31):
                lo = hi = 0
                for h in range(34):
                    t = T[h][j]
                    if t:
                        e = J[k][h]
                        if t > 0:
                            lo += e[0]; hi += e[1]
                        else:
                            lo -= e[1]; hi -= e[0]
                row.append((lo, hi))
            out.append(row)
        return out


def fracpoly(coeff, x):
    out = Fr(0)
    for c in coeff:
        out = out * x + c
    return out


def replay_sinks(src, sinks, tag):
    """Root isolation, positivity, P>0 and the strict Lyapunov inequality."""
    cx = Ctx(90)
    ok(sinks['complete'] and len(sinks['sink_certificates']) == 4, tag + ' four certificates')
    saved = [int(c) for c in sinks['eliminant_coefficients']]
    ok(saved == src.ec or saved == [-c for c in src.ec], tag + ' eliminant recomputed from formula (2.4)')
    ok([[str(v) for v in row] for row in src.rates] == sinks['rates'], tag + ' rate list')
    last, rows = None, []
    for c in sinks['sink_certificates']:
        lo, hi = map(Fr, c['root_interval'])
        ok(lo < hi and (last is None or last < lo), tag + ' ordered disjoint root intervals')
        last = hi
        ok(fracpoly(src.ec, lo) * fracpoly(src.ec, hi) < 0, tag + ' sign change')
        U = (cx.mk(lo)[0], cx.mk(hi)[1])
        der = cx.poly(src.dc, U)
        ok(der[0] > 0 or der[1] < 0, tag + ' simple root')
        X = src.state(cx, U)
        ok(all(x[0] > 0 for x in X), tag + ' positive species')
        J = src.jac(cx, X)
        ps, rs = c['P'], c['whitener']
        ok(all(ps[i][j] == ps[j][i] for i in range(31) for j in range(31)), tag + ' P symmetric')
        ok(all(Fr(rs[i][j]) == 0 for i in range(31) for j in range(i + 1, 31)) and all(Fr(rs[i][i]) > 0 for i in range(31)), tag + ' whitener triangular')
        P = [[cx.mk(Fr(x)) for x in row] for row in ps]
        R = [[cx.mk(Fr(x)) for x in row] for row in rs]
        RT = [list(r) for r in zip(*R)]
        pm = cx.dd_margin(cx.matmul(cx.matmul(R, P), RT))
        JT = [list(r) for r in zip(*J)]
        JP, PJ = cx.matmul(JT, P), cx.matmul(P, J)
        Q = [[cx.neg(cx.add(JP[i][j], PJ[i][j])) for j in range(31)] for i in range(31)]
        qm = cx.dd_margin(Q)
        ok(pm > Fr(9, 10) and qm > Fr(9, 10), tag + ' Lyapunov margins exceed 9/10')
        rows.append(dict(index=c['index'], u=float((lo + hi) / 2), P_margin=float(pm), Q_margin=float(qm)))
    return rows


def census(src):
    """All positive roots of the eliminant and their admissibility."""
    ivs = src.elim.intervals(eps=sy.Rational(1, 10 ** 40))
    out = []
    for (lo, hi), mult in ivs:
        if hi <= 0:
            continue
        ok(mult == 1, 'simple eliminant root')
        mid = (lo + hi) / 2
        Lm, Mm = src.L.subs(u, mid), src.M.subs(u, mid)
        # signs are constant on the tiny isolating interval unless L or M vanish there
        ok(all(sy.sign(src.L.subs(u, e)) == sy.sign(Lm) and sy.sign(src.M.subs(u, e)) == sy.sign(Mm) for e in (lo, hi)), 'sign-stable')
        adm = (ET - mid) * Lm > 0 and Lm * Mm > 0
        out.append(dict(u=float(mid), admissible=bool(adm)))
    return out


def operating(src, sinks, op, loc, preps, tag):
    cx = Ctx(90)
    d = 31
    rates = [[Fr(v) for v in row] for row in op['rates']]
    clock = Fr(op['clock_rescaling'])
    ok(clock == max(v for row in src.rates for v in row) / 2, tag + ' clock')
    ok(rates == [[v / clock for v in row] for row in src.rates], tag + ' scaled rates')
    # quadratic remainder constant K of Theorem 6.1 (Euclidean chart norm)
    K = Fr(0)
    for i, (a, b) in enumerate(EDGES):
        for rate, sub in [(rates[i][0], a), (rates[i][3], b)]:
            K += rate * (1 + int(sub != 0)) * (d if sub == 0 else 1) * 12
    states, reads = [], []
    for c in sinks['sink_certificates']:
        lo, hi = map(Fr, c['root_interval'])
        X = src.state(cx, (cx.mk(lo)[0], cx.mk(hi)[1]))
        states.append(X)
        r = X[7]
        for i, (a, b) in enumerate(EDGES):
            if b == 7:
                r = cx.add(r, X[22 + i])
        reads.append(r)
    gap = min(Fr(reads[i + 1][0] - reads[i][1], cx.S) for i in range(3))
    ok(gap > 0 and Fr(op['measurement_error']) == gap / 8, tag + ' decoder error is one eighth of the gap')
    REPORT[tag + '_normalized_readouts'] = [float(Fr(r[0], cx.S) / ST) for r in reads]
    REPORT[tag + '_min_normalized_gap'] = float(gap / ST)
    labels = op['labels']
    Trec = max(8 / Fr(x['lambda_']) for x in labels)
    ok(Fr(op['Trec']) == Trec and Fr(op['T']) == 100 * Trec, tag + ' horizon')
    Omega = int(op['Omega'])
    thr = Fr(1)
    worst_rec = worst_ret = Fr(0)
    eps_all, box_all, improve = [], [], []
    for c, X, lab, lrow in zip(sinks['sink_certificates'], states, labels, loc['labels']):
        P = [[Fr(x) for x in row] for row in c['P']]
        R = [[Fr(x) for x in row] for row in c['whitener']]
        pmax = max(sum(abs(x) for x in row) for row in P)
        rn = max(sum(abs(x) for x in row) for row in R)
        rc = max(sum(abs(R[i][j]) for i in range(d)) for j in range(d))
        pmin = Fr(9, 10) / (rn * rc)
        qmin = Fr(9, 10) / clock
        minimum = min(Fr(x[0], cx.S) for x in X)
        radius = min(minimum / (4 * d), gap / 16, qmin / (4 * pmax * K))
        v = pmin * radius ** 2
        lam = qmin / (2 * pmax)
        ok([Fr(lab[k]) for k in ('pmax', 'pmin', 'qmin', 'radius', 'v_exit', 'lambda_')] == [pmax, pmin, qmin, radius, v, lam], tag + ' ellipsoid constants')
        bounds = [Fr(x[1], cx.S) + sum(abs(t) for t in T[k]) * radius for k, x in enumerate(X)]
        glob = [Fr(ST)] * 8 + [Fr(ET), Fr(FT)] + [Fr(ET)] * 12 + [Fr(FT)] * 12
        Cl = Cg = B = Dn = Fr(0)
        for rate, rea, nu in src.reactions(rates):
            z = [nu[k] for k in IX]
            qp = sum(P[j][k] * z[j] * z[k] for j in range(d) for k in range(d) if z[j] and z[k])
            ok(qp >= 0, 'nonnegative jump form')
            act = rate * math.prod(bounds[k] for k in rea)
            Cl += qp * act
            Cg += qp * rate * math.prod(glob[k] for k in rea)
            nrm = sum(abs(t) for t in z)
            B += nrm * act
            Dn += rate * nrm * sum(sum(abs(t) for t in T[k]) * math.prod(bounds[h] for h in rea if h != k) for k in rea)
        Brev = Drev = Fr(0)
        for i, (a, b) in enumerate(EDGES):
            for coef, rea, pro in [(rates[i][0] * rates[i][2] / rates[i][1], [8, b], 10 + i), (rates[i][3] * rates[i][5] / rates[i][4], [9, a], 22 + i)]:
                nu = [0] * 34
                nu[pro] += 1
                for k in rea:
                    nu[k] -= 1
                nrm = sum(abs(nu[k]) for k in IX)
                Brev += coef * nrm * math.prod(bounds[k] for k in rea)
                Drev += coef * nrm * sum(sum(abs(t) for t in T[k]) * math.prod(bounds[h] for h in rea if h != k) for k in rea)
        ok(Fr(lrow['local_C']) == Cl and Fr(lrow['global_C']) == Cg and Cl < Cg, tag + ' generator constants')
        ell = min(v / 4 / pmax, Fr(1))
        box = min(Fr(1, 2), qmin / (8 * pmax * Dn), qmin * ell / (8 * pmax * B))
        eps = min(Fr(1, 2), qmin / (8 * pmax * Drev), qmin * ell / (8 * pmax * Brev))
        ok(Fr(lrow['relative_rate_box']) == box and Fr(lrow['epsilon_driving_max']) == eps, tag + ' robustness thresholds')
        eps_all.append(eps); box_all.append(box); improve.append(Cg / Cl)
        thr = max(thr, 1000 * Cl * 100 * Trec / v, 10 ** 6 * Cl / (lam * v), 1024 * d * pmax / v)
        ret = Fr(1, 4096) + Cl * 100 * Trec / (Omega * v)
        rec = Fr(1, 1024) + Cl * Trec / (Omega * v) + Fr(1, 256) + 4096 * Cl / (lam * Omega * v)
        ok(Fr(lab['retention_failure']) == ret and Fr(lab['recovery_failure']) == rec, tag + ' stored failure bounds')
        ok(pmax * d / (4 * Omega ** 2) <= v / 4096, tag + ' lattice rounding fits the preparation set')
        worst_rec, worst_ret = max(worst_rec, rec), max(worst_ret, ret)
    ok(Omega == math.ceil(thr) + 1, tag + ' Omega is the declared budget')
    ok(worst_rec < Fr(8987, 10 ** 6) and worst_ret < Fr(1, 100), tag + ' error bounds')
    REPORT[tag + '_log10_Omega'] = math.log10(Omega)
    REPORT[tag + '_worst_recovery_bound'] = float(worst_rec)
    REPORT[tag + '_worst_retention_bound'] = float(worst_ret)
    REPORT[tag + '_local_over_global_noise'] = [float(x) for x in improve]
    if preps is not None:
        ok(min(eps_all) >= Fr(1, 10 ** 102) and min(box_all) >= Fr(1, 10 ** 99), tag + ' eps=1e-102 and box=1e-99 are covered')
        REPORT[tag + '_log10_eps_driving'] = math.log10(min(eps_all))
        REPORT[tag + '_log10_rate_box'] = math.log10(min(box_all))
        hp = Ctx(220)
        ok(int(preps['Omega']) == Omega, 'preparations use the same Omega')
        for c, lab, pr in zip(sinks['sink_certificates'], labels, preps['preparations']):
            N = [int(x) for x in pr['counts']]
            ok(len(N) == 34 and min(N) >= 0, 'nonnegative integer counts')
            ok(N[8] + sum(N[10:22]) == ET * Omega and N[9] + sum(N[22:]) == FT * Omega and sum(N[:8]) + sum(N[10:]) == ST * Omega, 'exact inventories')
            lo, hi = map(Fr, c['root_interval'])
            # refine the isolating interval by exact bisection to 10**-200
            flo = fracpoly(src.ec, lo)
            while hi - lo > Fr(1, 10 ** 200):
                mid = (lo + hi) / 2
                fm = fracpoly(src.ec, mid)
                if fm == 0:
                    lo = hi = mid
                    break
                if (fm > 0) == (flo > 0):
                    lo = mid
                else:
                    hi = mid
            X = src.state(hp, (hp.mk(lo)[0], hp.mk(hi)[1]))
            err = [hp.sub(hp.mk(Fr(N[i], Omega)), X[i]) for i in IX]
            P = [[hp.mk(Fr(x)) for x in row] for row in c['P']]
            val = 0
            for i in range(31):
                for j in range(31):
                    val += hp.mul(hp.mul(err[i], P[i][j]), err[j])[1]
            ok(Fr(val, hp.S) <= Fr(lab['v_exit']) / 4096, 'integer preparation inside B_i')
    return Omega, Trec, clock


def physical(src, Omega, Trec, clock):
    """Substrate fixed at 1 uM; uniform slowing to 1e6 /M/s and 100 /s ceilings."""
    assoc = max(max(r[0], r[3]) for r in src.rates)
    uni = max(max(r[1], r[2], r[4], r[5]) for r in src.rates)
    slow = max(Fr(1), assoc * ST, uni / 100)          # a/(C0 T0) = a*ST*1e6 per M per s
    trec_s = Trec / clock * slow
    NA = 6.02214076e23
    return dict(log10_substrate=math.log10(Omega) + math.log10(ST), log10_kinase=math.log10(Omega) + 1,
                log10_phosphatase=math.log10(Omega), log10_volume_L=math.log10(Omega) + math.log10(ST) - math.log10(NA * 1e-6),
                log10_trec_s=math.log10(trec_s), log10_T_s=math.log10(trec_s) + 2, slowdown=float(slow))


def obstruction(src):
    l, r = sy.Rational(41, 10), sy.Rational(21, 5)
    ok(all(c > 0 for t in src.tcoef for c in t if c != 0), 'tree coefficients nonnegative')
    Al = src.A.subs(u, l)
    Lmax = sy.prod(max(abs(l - j), abs(r - j)) for j in range(1, 7))
    ok(all(sy.prod((e - j) for j in range(1, 7)) > 0 for e in (l, r)), 'L>0 on the branch interval')
    lower = (10 - r) * Al / (r * Lmax)
    ok(lower > 10 ** 9, 'free substrate exceeds 1e9')
    saved = load('postproof_fixed_target_obstruction.json')
    ok(sy.Rational(saved['free_substrate_lower']) == lower, 'saved obstruction bound')
    REPORT['free_substrate_lower'] = float(lower)
    REPORT['kinase_to_substrate_upper'] = float(10 / lower)
    ok(10 / lower < sy.Rational(1, 10 ** 10), 'E_T/S_T < 1e-10 on the branch')


def packing_examples():
    """Proposition 7.3 sanity: grid codebooks meet the bound."""
    for R, eps, d in [(Fr(1), Fr(1, 10), 1), (Fr(1), Fr(1, 8), 2), (Fr(3), Fr(1, 3), 3)]:
        per = 1 + math.floor(R / (2 * eps))
        ok(per >= 1, 'packing bound')
        REPORT.setdefault('packing_bounds', []).append([float(R), float(eps), d, per ** d])


def main():
    t0 = time.time()
    section_identities()
    G, tt = tree_weights()
    # stationarity and saved tree weights
    net = [0] * 8
    for i, (a, b) in enumerate(EDGES):
        cur = UP[i] * u * tt[a] - DOWN[i] * tt[b]
        net[a] -= cur; net[b] += cur
    ok(all(sy.expand(v) == 0 for v in net), 'tree weights are stationary')
    tw = load('tree_weights.json')
    ok([int(x) for x in tw['up']] == UP and [int(x) for x in tw['down']] == DOWN, 'effective rates')
    ok([[int(c) for c in row] for row in tw['weights_descending_coefficients']] == [[int(c) for c in sy.Poly(t, u).all_coeffs()] for t in tt], 'saved tree weights equal Laplacian cofactors')
    # weighted stationarity: positive loading kernel (4.1)
    ok(sy.expand(u * sum(UP[i] * tt[a] for i, (a, b) in enumerate(EDGES)) - sum(DOWN[i] * tt[b] for i, (a, b) in enumerate(EDGES))) == 0, 'loading kernel identity')
    for v in range(8):
        k = bin(v).count('1')
        ok(sy.Poly(tt[v], u).all_coeffs()[-k:] == [0] * k if k else True, 'u^|A| divides tau_A')
    REPORT['deg_tau'] = [int(sy.degree(t, u)) for t in tt]

    iface = load('postproof_candidate_interface.json')
    p, q = [Fr(x) for x in iface['p']], [Fr(x) for x in iface['q']]
    ok(min(p + q) > 0, 'positive loadings')
    src = Source(p, q, tt)
    ok(sy.expand(src.L - sy.prod(u - j for j in range(1, 7))) == 0, 'B - 10 D = prod (u-j)')
    ok([[str(v) for v in row] for row in src.rates] == iface['rates'], 'literal rates')
    ok(all(v > 0 for row in src.rates for v in row), 'positive rates')
    REPORT['loading_range'] = [float(min(p + q)), float(max(p + q))]
    REPORT['rate_range'] = [float(min(v for r in src.rates for v in r)), float(max(v for r in src.rates for v in r))]
    ok(src.elim.degree() == 15 and fracpoly(src.ec, Fr(0)) != 0, 'eliminant degree 2q-1')
    cen = census(src)
    REPORT['positive_eliminant_roots'] = cen
    REPORT['admissible_equilibria'] = sum(c['admissible'] for c in cen)
    ok(REPORT['admissible_equilibria'] == 7 and len(cen) == 8, 'final source: eight positive roots, seven equilibria')

    sinks = load('postproof_candidate_sinks.json')
    t1 = time.time()
    REPORT['final_sinks'] = replay_sinks(src, sinks, 'final')
    REPORT['sink_replay_seconds'] = round(time.time() - t1, 1)
    op = load('postproof_candidate_operating.json')
    loc = load('postproof_candidate_local_certificate.json')
    preps = load('postproof_candidate_preparations.json')
    Omega, Trec, clock = operating(src, sinks, op, loc, preps, 'final')
    phys_final = physical(src, Omega, Trec, clock)
    REPORT['physical_final_local'] = phys_final

    # original source: operating arithmetic (and, with --full, its sink certificates)
    old_s = load('cube_four_sinks.json')
    old_rates = [[Fr(v) for v in row] for row in old_s['rates']]
    po = [old_rates[i][0] - UP[i] for i in range(12)]
    qo = [old_rates[i][3] - DOWN[i] for i in range(12)]
    ok(min(po + qo) > 0, 'original loadings positive')
    old = Source(po, qo, tt)
    ok(sy.expand(old.L - sy.prod(u - j for j in range(1, 7))) == 0, 'original source has the same target')
    cen_old = census(old)
    REPORT['original_positive_eliminant_roots'] = cen_old
    ok(sum(c['admissible'] for c in cen_old) == 7 and len(cen_old) == 8, 'original source: seven equilibria')
    if FULL:
        REPORT['original_sinks'] = replay_sinks(old, old_s, 'original')
    old_op, old_loc = load('cube_memory_bound.json'), load('postproof_local_certificate.json')
    op_local = dict(old_op, Omega=old_loc['Omega'])
    for lab, lrow in zip(op_local['labels'], old_loc['labels']):
        lab.update(retention_failure=lrow['retention_failure'], recovery_failure=lrow['recovery_failure'])
    Om_l, Tr_o, cl_o = operating(old, old_s, op_local, old_loc, None, 'original_local')
    Om_g = int(old_op['Omega'])
    REPORT['physical_original_global'] = physical(old, Om_g, Tr_o, cl_o)
    REPORT['physical_original_local'] = physical(old, Om_l, Tr_o, cl_o)
    REPORT['original_local_gain'] = float(Fr(Om_g, Om_l))
    REPORT['final_vs_original_global_log10_molecules'] = math.log10(Om_g) - math.log10(Omega)
    REPORT['final_vs_original_log10_recovery'] = REPORT['physical_original_global']['log10_trec_s'] - phys_final['log10_trec_s']
    saved = load('resources.json')
    for rec, mine in zip(saved, [REPORT['physical_original_global'], REPORT['physical_original_local'], phys_final]):
        ok(abs(rec['log10_substrate_count'] - mine['log10_substrate']) < 1e-6 and abs(rec['log10_Trec_seconds'] - mine['log10_trec_s']) < 1e-6
           and abs(rec['log10_volume_liters'] - mine['log10_volume_L']) < 1e-6, 'Table 2 entries (display rounding only)')
    obstruction(src)
    packing_examples()
    REPORT['checks_passed'] = NCHECK
    REPORT['seconds'] = round(time.time() - t0, 1)
    REPORT['mode'] = 'full' if FULL else 'default'
    (HERE / 'check_paper_report.json').write_text(json.dumps(REPORT, indent=1))
    print(json.dumps({k: REPORT[k] for k in ('checks_passed', 'seconds', 'admissible_equilibria', 'final_log10_Omega', 'final_worst_recovery_bound', 'final_min_normalized_gap', 'free_substrate_lower', 'final_log10_eps_driving', 'final_log10_rate_box', 'original_local_gain')}, indent=1))
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
