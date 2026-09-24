"""Exact-rational moving-tube certificate for the depleting linear donor law.

Model: the printed eight-state shared-NADPH field with sigma = 1, coupled to
spent donor C through  s = 3/25 - C/V,  C' = s R_1(x)  (so Q = Q_0 - C).

  build  V name   : integrate a float reference, propose radii, verify exactly,
                    and write data/<name>.json
  verify name     : replay every inequality of data/<name>.json using only
                    Python integers/Fractions (no floating point enters).

The certificate is a finite list of rational times t_k, rational reference
points (c_k, Cbar_k), and rational radii (q_k, qC_k).  Between grid times the
reference and the radii are affine.  Verified on every step, uniformly in t:

  (F)  signed face inequality  eta * adot_i < q_i'(t)  on each of the 16 modal
       faces of  {c(t) + M a : |a_j| <= q_j(t)}  and both donor faces;
  (P)  strict physicality of the whole tube slice;
  (S)  service floors (and, at the final time, a ceiling) from the enclosure.

Evidence level: exact rational arithmetic, NOT a Lean kernel proof.
"""
import json
import sys
from fractions import Fraction as F
from math import ceil, floor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
cert0 = json.loads((DATA / 'modal_box.json').read_text())
M = [[F(x) for x in r] for r in cert0['M']]
MI = [[F(x) for x in r] for r in cert0['inverse']]
C0 = [F(x[0]) for x in cert0['center']]
N8 = range(8)
assert all(sum(MI[i][k] * M[k][j] for k in N8) == (1 if i == j else 0) for i in N8 for j in N8)
AM = [[abs(x) for x in r] for r in M]
AMI0 = [abs(MI[i][0]) for i in N8]

D_ = F(873, 10)
TAU = F(1, 250)
HOR = F(251, 250)
S0 = F(3, 25)
KAPPA = F(1, 1000)                          # independent relative preparation tolerance
QC0 = F(1, 1000)                            # initial donor tolerance (microM)
P0 = [C0[i] + F(5, 6) * M[i][1] for i in N8]            # prepared centre p
SRAD = [F(9, 10)] + [F(7, 10)] * 7          # terminal rectangle S of the Lean-verified theorem


def R1(x):
    return 375 * (30 - x) / (D_ - x)


def field(u, s):
    x, z, e1, e2, zt, h, w, v = u
    g = F(37156, 100) - 2 * z - e2
    e0 = 50 - e1 - e2
    y = F(505, 1000) - zt
    r = F(19096, 1000) - h - w - v
    HG = F(21, 100) * e0
    HT = F(21, 10) * y * v
    p1 = F(4, 100) * g * e1
    p2 = 10 * g * e2
    sG = F(32, 10) * x * (z - F(178, 100))
    sT = 20 * x * (zt - F(75, 1000))
    return [s * R1(x) - sG - sT, p2 - sG, HG - p1, p1 - p2, HT - sT,
            F(4, 10) * r + F(3, 1000) * w - F(72, 100000) * h - 15 * h,
            F(72, 100000) * h - F(3, 1000) * w, 15 * h - HT]


def jacobian(u, s):
    x, z, e1, e2, zt, h, w, v = u
    g = F(37156, 100) - 2 * z - e2
    y = F(505, 1000) - zt
    J = [[F(0)] * 8 for _ in N8]
    # psi_G = 3.2 x (z-1.78): -x', -z'
    a, b = F(32, 10) * (z - F(178, 100)), F(32, 10) * x
    J[0][0] -= a; J[0][1] -= b; J[1][0] -= a; J[1][1] -= b
    # psi_T = 20 x (zt-.075): -x', -zt'
    a, b = 20 * (zt - F(75, 1000)), 20 * x
    J[0][0] -= a; J[0][4] -= b; J[4][0] -= a; J[4][4] -= b
    # source
    J[0][0] += -s * 375 * F(573, 10) / (D_ - x) ** 2
    # phi_1 = .04 g e1 : -e1', +e2'   (dg = -2dz - de2)
    k = F(4, 100)
    for col, val in ((1, -2 * k * e1), (3, -k * e1), (2, k * g)):
        J[2][col] -= val; J[3][col] += val
    # phi_2 = 10 g e2 : +z', -e2'
    for col, val in ((1, -20 * e2), (3, 10 * g - 10 * e2)):
        J[1][col] += val; J[3][col] -= val
    # H_G = .21 (50-e1-e2): +e1'
    J[2][2] -= F(21, 100); J[2][3] -= F(21, 100)
    # H_T = 2.1 y v : +zt', -v'
    for col, val in ((4, -F(21, 10) * v), (7, F(21, 10) * y)):
        J[4][col] += val; J[7][col] -= val
    # h' = .4 r + .003 w - .00072 h - 15 h ; r = 19.096-h-w-v
    J[5][5] += -F(4, 10) - F(72, 100000) - 15
    J[5][6] += -F(4, 10) + F(3, 1000)
    J[5][7] += -F(4, 10)
    J[6][5] += F(72, 100000); J[6][6] -= F(3, 1000)
    J[7][5] += 15
    return J


VECS = [[F(-32, 10), F(-32, 10), 0, 0, 0, 0, 0, 0], [-20, 0, 0, 0, -20, 0, 0, 0],
        [0, 0, F(-4, 100), F(4, 100), 0, 0, 0, 0], [0, 10, 0, -10, 0, 0, 0, 0],
        [0, 0, 0, 0, F(-21, 10), 0, 0, F(21, 10)]]
TV = [[abs(sum(MI[i][k] * v[k] for k in N8)) for i in N8] for v in VECS]


def matvec(A, x):
    return [sum(A[i][k] * x[k] for k in N8) for i in N8]


def faces(u):
    x, z, e1, e2, zt, h, w, v = u
    return [x, 30 - x, z - F(178, 100), e1, e2, F(37156, 100) - 2 * z - e2, 50 - e1 - e2,
            zt - F(75, 1000), F(505, 1000) - zt, h, w, v, F(19096, 1000) - h - w - v]


FACE_GRAD = [[1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0],
             [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0, 0],
             [0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
             [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1],
             [0, 0, 0, 0, 0, 1, 1, 1]]
ELL = [1, -1, -1, -1, -1, 0, 0, 0]          # W = 234.43 + ELL.u
ELLM = [abs(sum(ELL[k] * M[k][j] for k in N8)) for j in N8]


def step_pre(V, h, ck, cn, Ck, Cn):
    """Radius-independent exact data of one step (expansion at the step midpoint)."""
    dl = [b - a for a, b in zip(ck, cn)]
    cm = [(a + b) / 2 for a, b in zip(ck, cn)]
    dC = Cn - Ck
    sm = S0 - (Ck + Cn) / 2 * V      # V holds 1/V here (0 for the maintained source)
    assert sm > 0
    J = jacobian(cm, sm)
    JM = [[sum(J[i][k] * M[k][j] for k in N8) for j in N8] for i in N8]
    A = [[sum(MI[i][k] * JM[k][j] for k in N8) for j in N8] for i in N8]
    Fc = field(cm, sm)
    b = matvec(MI, [Fc[i] - dl[i] / h for i in N8])
    bth = [abs(x) / 2 for x in matvec(MI, matvec(J, dl))]
    const = [abs(b[i]) + bth[i] for i in N8]
    absA = [[abs(A[i][j]) if j != i else F(0) for j in N8] for i in N8]
    return dict(V=V, h=h, dl=dl, cm=cm, dC=dC, sm=sm, diag=[A[i][i] for i in N8], absA=absA,
                const=const, donor_res=abs(sm * R1(cm[0]) - dC / h), facec=faces(cm))


def step_eval(pre, q, qn, qC, qCn):
    """Exact right-hand sides of the face inequalities on one step, uniformly in t."""
    cm, dl, sm, V = pre['cm'], pre['dl'], pre['sm'], pre['V']
    qh = [max(a, c) for a, c in zip(q, qn)]
    qCh = max(qC, qCn)
    d = [sum(AM[j][k] * qh[k] for k in N8) + abs(dl[j]) / 2 for j in N8]
    prods = [d[0] * d[1], d[0] * d[4], (2 * d[1] + d[3]) * d[2], (2 * d[1] + d[3]) * d[3], d[4] * d[7]]
    den = D_ - cm[0]
    assert den - d[0] > 0 and cm[0] - d[0] > 0 and cm[0] + d[0] < 30
    srem = 375 * sm * F(573, 10) * d[0] ** 2 / (den ** 2 * (den - d[0]))
    sig = (qCh + abs(pre['dC']) / 2) * V
    r1max = R1(cm[0] - d[0])
    rest = []
    for i in N8:
        n_i = sum(TV[m][i] * prods[m] for m in range(5)) + AMI0[i] * srem
        off = sum(pre['absA'][i][j] * qh[j] for j in N8)
        rest.append(off + pre['const'][i] + n_i + sig * r1max * AMI0[i])
    lip = 375 * F(573, 10) / (den - d[0]) ** 2
    gC = pre['donor_res'] + sm * lip * d[0] + sig * r1max
    phys = [fc - sum(abs(g) * dd for g, dd in zip(gr, d)) for fc, gr in zip(pre['facec'], FACE_GRAD)]
    yl, vl = F(505, 1000) - cm[4] - d[4], cm[7] - d[7]
    LG = F(21, 100) * (50 - cm[2] - cm[3] - d[2] - d[3])
    LT = F(21, 10) * yl * vl if yl > 0 and vl > 0 else F(0)
    return pre['diag'], rest, gC, min(phys), LG, LT


def step_bounds(V, h, ck, cn, Ck, Cn, q, qn, qC, qCn):
    return step_eval(step_pre(V, h, ck, cn, Ck, Cn), q, qn, qC, qCn)


def up(x, dig=16):
    return F(ceil(x * 10 ** dig), 10 ** dig)


def verify(name, quiet=False):
    c = json.loads((DATA / f'{name}.json').read_text())
    V = F(0) if c['V'] == 'inf' else 1 / F(c['V'])      # inverse stock scale
    ts = [F(x) for x in c['times']]
    ref = [[F(x) for x in r] for r in c['reference']]
    Cb = [F(x) for x in c['donor_reference']]
    qs = [[F(x) for x in r] for r in c['radii']]
    qC = [F(x) for x in c['donor_radii']]
    n = len(ts) - 1
    assert ts[0] == 0 and ts[-1] == HOR and TAU in ts and all(ts[k] < ts[k + 1] for k in range(n))
    # initial inclusion: the independent box |u_j - p_j| <= KAPPA p_j lies in p + M Box(q_0)
    assert ref[0] == P0, 'reference must start at p'
    assert all(KAPPA * sum(abs(MI[i][j]) * P0[j] for j in N8) <= qs[0][i] for i in N8), 'initial inclusion'
    assert all(F(1, 2000000) <= KAPPA * P0[j] for j in N8)          # the 0.5 pM box P lies inside
    assert F(21, 10) * (F(505, 1000) - P0[4] * (1 - KAPPA)) * (P0[7] * (1 + KAPPA)) < 4   # all deficient
    assert min(faces([P0[j] * (1 - KAPPA) for j in N8]) + faces([P0[j] * (1 + KAPPA) for j in N8])) > 0
    assert abs(Cb[0]) + QC0 <= qC[0], 'initial donor inclusion'
    minLG, minLT, short, minphys, margin = F(10 ** 6), F(10 ** 6), F(0), F(10 ** 6), F(10 ** 6)
    LTs = []
    for k in range(n):
        h = ts[k + 1] - ts[k]
        diag, rest, gC, phys, LG, LT = step_bounds(V, h, ref[k], ref[k + 1], Cb[k], Cb[k + 1],
                                                   qs[k], qs[k + 1], qC[k], qC[k + 1])
        for i in N8:
            qsel = min(qs[k][i], qs[k + 1][i]) if diag[i] < 0 else max(qs[k][i], qs[k + 1][i])
            lhs = diag[i] * qsel + rest[i]
            rhs = (qs[k + 1][i] - qs[k][i]) / h
            assert lhs < rhs, ('face', k, i, float(lhs), float(rhs))
            margin = min(margin, rhs - lhs)
        assert gC < (qC[k + 1] - qC[k]) / h, ('donor face', k)
        assert phys > 0, ('physical', k)
        LTs.append(LT)
        minphys = min(minphys, phys)
        if ts[k] >= TAU:
            minLG, minLT = min(minLG, LG), min(minLT, LT)
        else:
            short += h * max(F(0), 4 - LT)
            assert LG >= 10
    # endpoint enclosures (radii at the grid time itself)
    def encl(k):
        d = [sum(AM[j][m] * qs[k][m] for m in N8) for j in N8]
        u = ref[k]
        lo = F(21, 10) * (F(505, 1000) - u[4] - d[4]) * (u[7] - d[7])
        hi = F(21, 10) * (F(505, 1000) - u[4] + d[4]) * (u[7] + d[7])
        wc = F(23443, 100) + sum(ELL[i] * u[i] for i in N8)
        wr = sum(ELLM[j] * qs[k][j] for j in N8)
        return lo, hi, wc - wr, wc + wr
    kt = ts.index(TAU)
    loH, hiH, WloH, WhiH = encl(n)
    _, _, Wlo0, Whi0 = encl(0)
    spent_lo = (Cb[n] - qC[n]) - (Cb[kt] + qC[kt])
    spent_hi = (Cb[n] + qC[n]) - (Cb[kt] - qC[kt])
    s_final_hi = S0 - (Cb[n] - qC[n]) * V
    s_final_lo = S0 - (Cb[n] + qC[n]) * V
    a_end = matvec(MI, [ref[n][i] - C0[i] for i in N8])
    in_S = all(abs(a_end[i]) + qs[n][i] <= SRAD[i] for i in N8)
    first_in_S = None
    for k in range(n + 1):
        a_k = matvec(MI, [ref[k][i] - C0[i] for i in N8])
        if all(abs(a_k[i]) + qs[k][i] <= SRAD[i] for i in N8):
            first_in_S = ts[k]
            break
    certified_from = ts[n]
    for k in range(n - 1, -1, -1):
        if LTs[k] >= 4:
            certified_from = ts[k]
        else:
            break
    smin_lo = F(1137126, 10 ** 7)   # certified lower end of the stationary threshold (companion paper)
    t_below = next((ts[k] for k in range(n + 1) if S0 - (Cb[k] - qC[k]) * V < smin_lo), None)
    out = dict(name=name, V=c['V'], Q0=(None if V == 0 else str(S0 / V)), steps=n, kappa=str(KAPPA),
               final_slice_inside_S=in_S, first_grid_time_inside_S=(str(first_in_S) if first_in_S is not None else None), HT_floor_4_holds_from=float(certified_from),
               min_face_margin=float(margin), min_physical_margin=float(minphys),
               min_LG_after_tau=float(minLG), min_LT_after_tau=float(minLT),
               trx_shortfall_bound_before_tau=float(short),
               HT_enclosure_at_H=[float(loH), float(hiH)],
               spent_on_service_window=[float(spent_lo), float(spent_hi)],
               spent_total=[float(Cb[n] - qC[n]), float(Cb[n] + qC[n])],
               s_final=[float(s_final_lo), float(s_final_hi)],
               first_grid_time_with_s_below_stationary_threshold=(float(t_below) if t_below is not None else None),
               storage_drawdown_W0_minus_WH=[float(Wlo0 - WhiH), float(Whi0 - WloH)],
               final_radii=[float(x) for x in qs[n]], final_donor_radius=float(qC[n]),
               mission_success=bool(minLG >= 10 and minLT >= 4),
               mission_failure_at_H=bool(hiH < 4))
    out['exact'] = dict(min_LT_after_tau=str(minLT), min_LG_after_tau=str(minLG), HT_upper_at_H=str(hiH),
                        shortfall=str(short), spent_window=[str(spent_lo), str(spent_hi)],
                        s_final=[str(s_final_lo), str(s_final_hi)],
                        drawdown=[str(Wlo0 - WhiH), str(Whi0 - WloH)])
    if not quiet:
        print(json.dumps({k: v for k, v in out.items() if k != 'exact'}, indent=1))
    return out


def build(Vs, name, nsteps=900, h0=2e-6, growth=1.05, infl=1.03):
    import numpy as np
    from scipy.integrate import solve_ivp
    Mf = np.array([[float(x) for x in r] for r in M]); Mif = np.array([[float(x) for x in r] for r in MI])
    c0 = np.array([float(x) for x in C0])

    def R1f(x): return 375 * (30 - x) / (87.3 - x)

    def ff(u, s):
        x, z, e1, e2, zt, h, w, v = u
        g = 371.56 - 2 * z - e2; e0 = 50 - e1 - e2; y = .505 - zt; r = 19.096 - h - w - v
        HG = .21 * e0; HT = 2.1 * y * v; p1 = .04 * g * e1; p2 = 10 * g * e2
        sG = 3.2 * x * (z - 1.78); sT = 20 * x * (zt - .075)
        return np.array([s * R1f(x) - sG - sT, p2 - sG, HG - p1, p1 - p2, HT - sT,
                         .4 * r + .003 * w - .00072 * h - 15 * h, .00072 * h - .003 * w, 15 * h - HT])
    V = F(0) if Vs == 'inf' else 1 / F(Vs)
    Vf = float('inf') if Vs == 'inf' else float(F(Vs))
    u0 = np.array([float(x) for x in P0])
    sol = solve_ivp(lambda t, U: np.r_[ff(U[:8], .12 - U[8] / Vf), (.12 - U[8] / Vf) * R1f(U[0])],
                    (0, float(HOR)), np.r_[u0, 0.], method='Radau', rtol=1e-12, atol=1e-14, dense_output=True)
    assert sol.success
    ts = [F(0)]; h = F(h0).limit_denominator(10 ** 8); hmax = HOR / nsteps
    while ts[-1] < HOR:
        t = ts[-1] + h
        if ts[-1] < TAU <= t: t = TAU
        if t >= HOR - hmax / 4: t = HOR
        ts.append(F(round(t * 10 ** 8), 10 ** 8) if t not in (TAU, HOR) else t)
        h = min(hmax, h * F(growth).limit_denominator(100))
    ref, Cb = [], []
    for k, t in enumerate(ts):
        U = sol.sol(float(t))
        ref.append([F(round(U[i] * 10 ** 13), 10 ** 13) for i in N8]); Cb.append(F(round(U[8] * 10 ** 13), 10 ** 13))
    ref[0] = list(P0); Cb[0] = F(0)                     # exact region centre
    qs = [[up(KAPPA * sum(abs(MI[i][j]) * P0[j] for j in N8)) for i in N8]]; qC = [QC0]
    for k in range(len(ts) - 1):
        h = ts[k + 1] - ts[k]
        q = qs[-1]; qn = list(q); qCn = qC[-1]
        pre = step_pre(V, h, ref[k], ref[k + 1], Cb[k], Cb[k + 1])
        for it in range(60):
            diag, rest, gC, *_ = step_eval(pre, q, qn, qC[-1], qCn)
            rest = [up(x, 20) for x in rest]; gC = up(gC, 20)
            new = []
            for i in N8:
                a = diag[i]; r_ = rest[i] * F(infl).limit_denominator(1000) + F(1, 10 ** 13)
                cand = (q[i] / h + r_) / (1 / h - a)
                if cand <= q[i]:
                    new.append(up(cand))
                else:
                    new.append(up(q[i] + h * (a * q[i] + r_)) if a * q[i] + r_ > 0 else q[i])
            newC = up(qC[-1] + h * gC * F(infl).limit_denominator(1000) + F(1, 10 ** 15))
            done = all(abs(float(x) - float(y)) <= 1e-9 * float(y) + 1e-15 for x, y in zip(new, qn)) \
                and abs(float(newC - qCn)) < 1e-14
            qn, qCn = new, newC
            if done and it > 0:
                break
        # final exact check with slack; inflate if needed
        for attempt in range(20):
            diag, rest, gC, *_ = step_eval(pre, q, qn, qC[-1], qCn)
            bad = [i for i in N8 if not diag[i] * (min(q[i], qn[i]) if diag[i] < 0 else max(q[i], qn[i])) + rest[i]
                   < (qn[i] - q[i]) / h]
            badC = not gC < (qCn - qC[-1]) / h
            if not bad and not badC:
                break
            for i in bad:
                qn[i] = up(qn[i] * F(1001, 1000) + F(1, 10 ** 12))
            if badC:
                qCn = up(qCn * F(1001, 1000) + F(1, 10 ** 12))
        else:
            raise RuntimeError(f'step {k} failed')
        qs.append(qn); qC.append(qCn)
        if k % 100 == 0:
            print(k, float(ts[k]), [float(x) for x in qn][:5], float(qCn), flush=True)
    out = dict(description='Moving-tube certificate, linear donor law s=3/25-C/V; exact rationals as strings',
               V=Vs, horizon=str(HOR), tau=str(TAU), kappa=str(KAPPA), donor_tolerance=str(QC0),
               times=[str(x) for x in ts], reference=[[str(x) for x in r] for r in ref],
               donor_reference=[str(x) for x in Cb], radii=[[str(x) for x in r] for r in qs],
               donor_radii=[str(x) for x in qC])
    (DATA / f'{name}.json').write_text(json.dumps(out) + '\n')


if __name__ == '__main__':
    if sys.argv[1] == 'build':
        build(sys.argv[2], sys.argv[3], *(int(x) for x in sys.argv[4:5]))
        res = verify(sys.argv[3])
    else:
        res = verify(sys.argv[2])
    (DATA / f'{sys.argv[3] if sys.argv[1] == "build" else sys.argv[2]}_summary.json').write_text(json.dumps(res, indent=1) + '\n')
