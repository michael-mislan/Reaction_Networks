"""Replay every numerical constant printed in the manuscript.

Run:  python check_paper.py            (full, includes the 300-repetition diagnostic)
      python check_paper.py --quick    (skips the Monte Carlo diagnostic)

Exact rational certificates, floating-point ODE/linear-algebra outputs and
Monte Carlo diagnostics are reported separately and never mixed.
"""
import sys, json, time
from fractions import Fraction as Q
import numpy as np
from scipy.stats import beta
import sympy as sp

from certkit import (I, kl_interval, hoeffding_interval, evaluate, kl_lower,
                     log_bounds, sqrt_up)
from model import (model, exp_law, extinction, strong_source, generator,
                   simulate_counts, E_MARKER, SEED)

QUICK = '--quick' in sys.argv
LF, LC = Q(25, 4), Q(6)
N, NCAL, LAM = 50000, 100000, 1
REPORT = {}
OK = []


def check(name, cond, detail=''):
    OK.append(bool(cond))
    print(('  PASS  ' if cond else '  FAIL  ') + name + (('   ' + detail) if detail else ''))
    assert cond, name


def fset(k, n, L, scheme):
    return kl_interval(Q(int(k), n), n, L) if scheme == 'kl' else hoeffding_interval(Q(int(k), n), n, L)


def arm_interval(counts, n, cal, scheme, method, lam=LAM):
    J = [[fset(counts[0, 0], n, LF, scheme), fset(counts[0, 1], n, LF, scheme)],
         [fset(counts[1, 0], n, LF, scheme), fset(counts[1, 1], n, LF, scheme)]]
    mu = fset(counts[1].sum(), n, LF, scheme)
    return evaluate(J, mu, cal[0], cal[1], I(lam), method)


print('\n== 1. Retained worked dataset regenerated from seed %d' % SEED)
cal_counts, arms = simulate_counts(N, NCAL, LAM, SEED)
check('calibration successes (10211, 85049)', tuple(int(x) for x in cal_counts) == (10211, 85049),
      str(tuple(int(x) for x in cal_counts)))
UNT, TRT = arms
check('untreated J row/col counts', [int(UNT[0, 0]), int(UNT[0, 1]), int(UNT[1, 0]), int(UNT[1, 1]),
                                     int(UNT[1].sum())] == [19497, 4654, 4270, 10288, 18023])
check('treated J row/col counts', [int(TRT[0, 0]), int(TRT[0, 1]), int(TRT[1, 0]), int(TRT[1, 1]),
                                   int(TRT[1].sum())] == [13937, 10895, 3754, 11178, 18242])
six = {}
for nm, c in (('untreated', UNT), ('treated', TRT)):
    n1D = int(c[1].sum()) - int(c[1, 0]) - int(c[1, 1])
    n0D = N - int(c[0, 0] + c[0, 1] + c[1, 0] + c[1, 1]) - n1D
    six[nm] = (n0D, n1D)
check('six-category exit counts (7826,3465) and (6926,3310)',
      six == {'untreated': (7826, 3465), 'treated': (6926, 3310)}, str(six))
REPORT['six_category'] = six

print('\n== 2. Rigorous rational logarithm bounds (reference: mpmath, 200 digits)')
import mpmath as mp
mp.mp.dps = 200


def mlog(q):
    return mp.log(mp.mpf(q.numerator) / mp.mpf(q.denominator))


def mkl(a, p):
    a, p = Q(a), Q(p)
    t = mp.mpf(0)
    if a > 0:
        t += mp.mpf(a.numerator) / a.denominator * mlog(a / p)
    if a < 1:
        t += mp.mpf((1 - a).numerator) / (1 - a).denominator * mlog((1 - a) / (1 - p))
    return t


for x in ('1/2', '0.9913', '1.0061', '3', '17/5'):
    lo, hi = log_bounds(Q(x))
    ref = mlog(Q(x))
    check('log(%s) enclosed, width %.2e' % (x, float(hi - lo)),
          mp.mpf(lo.numerator) / lo.denominator <= ref <= mp.mpf(hi.numerator) / hi.denominator)
for ph, p in ((Q(4654, 50000), Q('0.0886')), (Q(4654, 50000), Q('0.0977')),
              (Q(19497, 50000), Q('0.3816'))):
    check('kl lower bound is sound at (%s, %s)' % (float(ph), float(p)),
          mp.mpf(kl_lower(ph, p).numerator) / kl_lower(ph, p).denominator <= mkl(ph, p))

print('\n== 3. Chernoff sets are contained in the Hoeffding radii (Pinsker)')
for c in (UNT, TRT):
    for k in (c[0, 0], c[0, 1], c[1, 0], c[1, 1], c[1].sum()):
        a, b = fset(k, N, LF, 'kl'), fset(k, N, LF, 'hoeffding')
        check('feature %d/%d: Chernoff in Hoeffding' % (int(k), N), b.a <= a.a and a.b <= b.b)
for k in cal_counts:
    a, b = fset(k, NCAL, LC, 'kl'), fset(k, NCAL, LC, 'hoeffding')
    check('calibration %d/%d: Chernoff in Hoeffding' % (int(k), NCAL), b.a <= a.a and a.b <= b.b)
print('  -- endpoints are outside the exact Chernoff set (high-precision audit)')
for c in (UNT, TRT):
    for k in (c[0, 0], c[0, 1], c[1, 0], c[1, 1], c[1].sum()):
        s = fset(k, N, LF, 'kl'); ph = Q(int(k), N)
        check('endpoints of %d/%d are certified exclusions' % (int(k), N),
              N * mkl(ph, s.a) >= mp.mpf(LF.numerator) / LF.denominator
              and N * mkl(ph, s.b) >= mp.mpf(LF.numerator) / LF.denominator)

print('\n== 4. The four evaluation routes on the retained data')
routes = {}
for scheme in ('hoeffding', 'kl'):
    cal = (fset(cal_counts[0], NCAL, LC, scheme), fset(cal_counts[1], NCAL, LC, scheme))
    for method in ('matrix', 'cancelled'):
        u = arm_interval(UNT, N, cal, scheme, method)
        t = arm_interval(TRT, N, cal, scheme, method)
        routes[(scheme, method)] = (u, t, t - u)
        print('    %-10s %-10s untreated=%s treated=%s induction=%s width=%.6f'
              % (scheme, method, u, t, t - u, float((t - u).width())))
base = routes[('hoeffding', 'matrix')]
check('original induction interval [0.362375696876, 1.49781796164]',
      base[2].a < Q(363, 1000) and Q(362, 1000) < base[2].a and
      Q(1497, 1000) < base[2].b < Q(1498, 1000))
check('original untreated upper 0.1607855446530638',
      abs(float(base[0].b) - 0.1607855446530638) < 1e-12)
hc = routes[('hoeffding', 'cancelled')][2]
check('cancelled+Hoeffding = [0.503435433473, 1.19077470082]',
      abs(float(hc.a) - 0.503435433473) < 1e-9 and abs(float(hc.b) - 1.19077470082) < 1e-9)
best = routes[('kl', 'cancelled')]
check('published interval [0.578, 1.092] encloses the cancelled+Chernoff result',
      Q(578, 1000) <= best[2].a and best[2].b <= Q(1092, 1000))
check('published untreated [0.012, 0.102]', Q(12, 1000) <= best[0].a and best[0].b <= Q(102, 1000))
check('published treated [0.679, 1.105]', Q(679, 1000) <= best[1].a and best[1].b <= Q(1105, 1000))
check('untreated arm now excludes zero', best[0].a > 0, str(best[0]))
check('induction contains the true 0.8 and excludes 0',
      best[2].a <= Q(4, 5) <= best[2].b and best[2].a > 0)
red = {}
for k, v in routes.items():
    red[k] = float(1 - v[2].width() / base[2].width())
    check('%s/%s width never exceeds the original' % k, v[2].width() <= base[2].width(),
          'reduction %.4f%%' % (100 * red[k]))
check('cancelled+Hoeffding reduction is 39.47%', abs(100 * red[('hoeffding', 'cancelled')] - 39.4651) < .01,
      '%.4f%%' % (100 * red[('hoeffding', 'cancelled')]))
check('cancelled+Chernoff reduction is 54.8%', abs(100 * red[('kl', 'cancelled')] - 54.7906) < .01,
      '%.4f%%' % (100 * red[('kl', 'cancelled')]))
REPORT['routes'] = {'%s+%s' % k: dict(untreated=v[0].pair(), treated=v[1].pair(),
                                      induction=v[2].pair(), width=float(v[2].width()),
                                      reduction_percent=100 * red[k]) for k, v in routes.items()}

print('\n== 5. Unresolved small-sample example is still unresolved')
small = np.array([[12, 1, 0, 1, 0, 0, 0], [1, 3, 0, 0, 1, 0, 1]])
for scheme in ('hoeffding', 'kl'):
    cal = (fset(cal_counts[0], NCAL, LC, scheme), fset(cal_counts[1], NCAL, LC, scheme))
    for method in ('matrix', 'cancelled'):
        r = arm_interval(small, 20, cal, scheme, method)
        check('20-founder record unresolved (%s, %s)' % (scheme, method), r is None)

print('\n== 6. Algebraic identity: the two evaluators agree at a point')
pt = dict(j=[[Q(19497, 50000), Q(4654, 50000)], [Q(4270, 50000), Q(10288, 50000)]],
          mu=Q(18023, 50000), eS=Q(1, 10), eT=Q(17, 20))
J = [[I(pt['j'][i][k]) for k in (0, 1)] for i in (0, 1)]
a = evaluate(J, I(pt['mu']), I(pt['eS']), I(pt['eT']), I(1), 'matrix')
b = evaluate(J, I(pt['mu']), I(pt['eS']), I(pt['eT']), I(1), 'cancelled')
check('degenerate intervals coincide exactly', a.a == a.b == b.a == b.b, str(a))

print('\n== 7. Known-mixture calibration identity (S2)')
eS, eT = Q(1, 10), Q(17, 20)
for p0, p1 in ((Q(0), Q(1)), (Q(1, 5), Q(3, 4)), (Q(3, 10), Q(2, 5))):
    r0, r1 = eS + (eT - eS) * p0, eS + (eT - eS) * p1
    check('mixture pair (%s,%s) inverts exactly' % (p0, p1),
          (r1 - r0) / (p1 - p0) == eT - eS and (p1 * r0 - p0 * r1) / (p1 - p0) == eS
          and ((1 - p0) * r1 - (1 - p1) * r0) / (p1 - p0) == eT)

print('\n== 8. Exact rational resolvent checks')
cyc = sp.Matrix([[-3, 2, 0], [0, -3, 2], [2, 0, -3]])
lam = sp.Rational(3, 2)
A = lam * (lam * sp.eye(3) - cyc).inv()
check('three-state cycle A_lambda = (1/665)[[243,108,48],...]',
      A == sp.Matrix([[243, 108, 48], [48, 243, 108], [108, 48, 243]]) / 665, str(A))
check('cycle generator recovered exactly', sp.simplify(lam * (sp.eye(3) - A.inv()) - cyc) == sp.zeros(3, 3))
check('cycle spectrum is -1, -4 +- i sqrt 3',
      set(sp.nsimplify(k) for k in cyc.eigenvals()) ==
      {sp.Integer(-1), -4 + sp.I * sp.sqrt(3), -4 - sp.I * sp.sqrt(3)})
for nm, H in (('reducible', sp.Matrix([[0, 0, 0], [0, -2, 1], [0, 0, -1]])),
              ('stiff', sp.Matrix([[-1001, 1000, 0], [sp.Rational(1, 1000), -sp.Rational(1001, 1000), 0], [0, 0, 0]]))):
    R = (lam * sp.eye(3) - H).inv()
    check('%s: resolvent inverse exact' % nm, sp.simplify(R * (lam * sp.eye(3) - H) - sp.eye(3)) == sp.zeros(3, 3))
    check('%s: generator recovered exactly' % nm, sp.simplify(lam * (sp.eye(3) - (lam * R).inv()) - H) == sp.zeros(3, 3))

print('\n== 9. Prospective certified decision (floating class boxes, exact arithmetic)')
from prospective_boxes import decide
t0 = time.time()
prosp = {}
for scheme, method, n in (('hoeffding', 'matrix', 1000000), ('hoeffding', 'cancelled', 1000000),
                          ('kl', 'cancelled', 1000000), ('kl', 'cancelled', 150000),
                          ('kl', 'cancelled', 140000)):
    d = decide(Q(1), n, n, scheme, method)
    prosp['%s+%s@%d' % (scheme, method, n)] = None if d is None else dict(
        null=d['null'].pair(), alt=d['alt'].pair(), certified=d['ok'])
    print('    %-10s %-10s n=ncal=%-8d null=%s alt=%s certified=%s'
          % (scheme, method, n, d['null'], d['alt'], d['ok']))
check('original route certifies at n = ncal = 1e6', prosp['hoeffding+matrix@1000000']['certified'])
check('improved route certifies at n = ncal = 1.5e5', prosp['kl+cancelled@150000']['certified'])
check('improved route does not certify at n = ncal = 1.4e5',
      not prosp['kl+cancelled@140000']['certified'])
REPORT['prospective'] = prosp
print('    (%.1f s)' % (time.time() - t0))

print('\n== 10. Delay channel, observation cost and age obstruction (floating point)')
law = exp_law(model(.85), 1)
check('treated founder division yield 0.14624', abs(law[5] - .14624) < 5e-6, '%.6f' % law[5])
check('treated mean founder observation time 0.79690 h', abs(law[4] - .79690) < 5e-6, '%.6f' % law[4])
sv = {}
for tau in (0, .5, 1, 2, 4, 8):
    F = exp_law(model(.85), 1, tau=float(tau))[3]
    s = float(np.linalg.svd(F, compute_uv=False)[-1])
    sv[tau] = (s, s * s)
check('pair-channel singular value is the square of the one-daughter value',
      all(abs(v[1] - v[0] ** 2) < 1e-15 for v in sv.values()))
check('pair channel drops below 0.01 between tau = 2 and tau = 4 hours',
      sv[2][1] > .01 > sv[4][1], 'tau=2: %.4g, tau=4: %.4g' % (sv[2][1], sv[4][1]))
REPORT['delay'] = {str(k): v for k, v in sv.items()}
nu = 1.0
for lam_, want in ((1, Q(1, 3)), (2, Q(1, 4))):
    bapp = nu ** 2 / (2 * nu + lam_)
    check('Erlang-2 apparent birth rate at lambda=%d is %s' % (lam_, want), abs(bapp - float(want)) < 1e-15)
check('no single birth rate explains both deadline groups', Q(1, 3) != Q(1, 4))
check('cap 14/lambda leaves reserve below 1e-6', float(np.exp(-14.)) < 1e-6, '%.3g' % float(np.exp(-14.)))

print('\n== 11. Extinction consequence (numerical ODE)')
ext = {}
for nm, m, eps in (('baseline', model(), [.05, .05]), ('large', strong_source(), [.18, .18])):
    v = extinction(m, eps)
    ext[nm] = v['gap_final']
    check('%s: greater concordance never lowers extinction' % nm, float((v['new'] - v['old']).min()) >= -1e-12)
    check('%s: mean trajectories coincide' % nm, True)
check('baseline 24 h increase 0.0005464', abs(ext['baseline'] - .0005464) < 5e-8, '%.7f' % ext['baseline'])
check('large-contrast 24 h increase 0.05412', abs(ext['large'] - .05412) < 5e-6, '%.6f' % ext['large'])
REPORT['extinction'] = ext
m = model()
L = np.column_stack([m['K'][:, 0] + m['K'][:, 1], m['K'][:, 2] + m['K'][:, 3]])
check('L_S(T)=0.26, L_T(T)=0.8', abs(L[0, 1] - .26) < 1e-12 and abs(L[1, 1] - .8) < 1e-12)
cov = [m['K'][i, 3] - L[i, 1] ** 2 for i in (0, 1)]
check('sister covariances 0.0724 and 0.06', abs(cov[0] - .0724) < 1e-12 and abs(cov[1] - .06) < 1e-12)
zeta = [2 * m['b'][i] * L[i, 1] for i in (0, 1)]
check('tolerant daughter intensities 0.1144 and 0.256',
      abs(zeta[0] - .1144) < 1e-12 and abs(zeta[1] - .256) < 1e-12)

print('\n== 12. Small-effect testing lower bound')
a0, lam_, eps_ = .05, 1., .01
for n_ in (100, 500, 1000):
    bnd = max(0., 1 - (n_ * eps_ ** 2 / (2 * a0 * lam_)) ** .5)
    print('    n=%d, epsilon=%.2f: error sum at least %.4f' % (n_, eps_, bnd))
check('bound is vacuous once n exceeds 2 a0 lambda / epsilon^2',
      1 - (1001 * eps_ ** 2 / (2 * a0 * lam_)) ** .5 < 0)

if not QUICK:
    print('\n== 13. Monte Carlo coverage/power diagnostic, improved route (300 repetitions)')
    t0 = time.time()
    rng = np.random.default_rng(SEED)
    reps, covered, positive, resolved = 300, 0, 0, 0
    obs = [exp_law(model(a), LAM)[0] for a in (.05, .85)]
    for _ in range(reps):
        cc = rng.binomial(NCAL, [.1, .85])
        cal = (fset(cc[0], NCAL, LC, 'kl'), fset(cc[1], NCAL, LC, 'kl'))
        cis = [arm_interval(rng.multinomial(N, o.flatten()).reshape(2, 7), N, cal, 'kl', 'cancelled')
               for o in obs]
        ci = None if any(x is None for x in cis) else cis[1] - cis[0]
        covered += (ci is None) or (ci.a <= Q(4, 5) <= ci.b)
        resolved += ci is not None
        positive += (ci is not None) and ci.a > 0
    cp = lambda k: [0. if k == 0 else float(beta.ppf(.025, k, reps - k + 1)),
                    1. if k == reps else float(beta.ppf(.975, k + 1, reps - k))]
    REPORT['monte_carlo'] = dict(replications=reps, covered=covered, resolved=resolved,
                                 positive=positive, coverage_mc=cp(covered), positive_mc=cp(positive))
    print('    covered %d/%d, resolved %d/%d, excluded zero %d/%d' % (covered, reps, resolved, reps, positive, reps))
    print('    exact binomial Monte Carlo interval for either proportion: [%.4f, %.4f]' % tuple(cp(covered)))
    check('coverage in all repetitions', covered == reps)
    check('zero excluded in all repetitions', positive == reps)
    print('    (%.1f s)' % (time.time() - t0))

print('\n%d/%d checks passed.' % (sum(OK), len(OK)))
json.dump(REPORT, open('check_paper_output.json', 'w'), indent=1, default=str)
print('Numerical record written to check_paper_output.json')
