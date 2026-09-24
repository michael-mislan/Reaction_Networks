"""Replay every exact / interval-certified number printed in the paper.

    python check_paper.py            # all certificate stages (about two minutes)
    python check_paper.py --quick    # skip the five- and six-site witnesses and the pulse flow

Evidence levels follow the paper: exact rational algebra and outward-rounded
rational interval arithmetic (160-bit dyadic grid).  Nothing here is a Lean proof,
and no floating-point number is an acceptance condition.  Output:
certificates/paper_certificates.json (rational endpoints) and a PASS/FAIL log.
"""
import json, sys, time, subprocess
from fractions import Fraction as Fr
from pathlib import Path
import sympy as sp
from phos import *

ROOT = Path(__file__).resolve().parent
QUICK = '--quick' in sys.argv
OUT = {}
NPASS = [0]


def ok(cond, label):
    NPASS[0] += 1
    print(('PASS  ' if cond else 'FAIL  ') + label, flush=True)
    if not cond:
        raise SystemExit('check failed: ' + label)


def inside(iv, lo, hi):
    """interval iv strictly inside the printed decimal window (lo,hi)."""
    return Fr(lo) < iv.a and iv.b < Fr(hi)


def dump(cert):
    keep = dict(t=bounds(cert['t']), r=bounds(cert['r']), omega=bounds(cert['omega']),
                crossing=bounds(cert['crossing']), l1=bounds(cert['l1']),
                routh_first_column=[bounds(v) for v in cert['routh']],
                right_eigenvector=[bounds(v) for v in cert['right']],
                left_eigenvector=[bounds(v) for v in cert['left']],
                p0=[str(v) for v in cert['p0']], p1=[str(v) for v in cert['p1']])
    if 'eps_derivative' in cert: keep['eps_derivative'] = bounds(cert['eps_derivative'])
    return keep


# ------------------------------------------------------------------ 1. sources
t0 = time.time()
half = sp.Rational(1, 2)
for w, tot in (('A', ('119/25', '1379/50', '1106/25')), ('H', ('1157/250', '259/20', '28279/500'))):
    m = witness(w, half)
    ok(m.field() == sp.zeros(12, 1), f'witness {w}: exact equilibrium of the literal 18-reaction field')
    ok(tuple(m.totals()) == tuple(sp.Rational(v) for v in tot), f'witness {w}: conserved totals {tot}')
    ok(m.N.rank() == 9, f'witness {w}: stoichiometric rank nine')
rs = sp.Symbol('r', positive=True)
mA = witness('A', rs)
table = dict(a=[str(v) for v in mA.kon[:3]], b=[str(v) for v in mA.koff[:3]], c=[str(v) for v in mA.kcat[:3]],
             alpha=[str(sp.factor(v)) for v in mA.kon[3:]], beta=[str(v) for v in mA.koff[3:]],
             gamma=[str(v) for v in mA.kcat[3:]])
OUT['rate_table_A'] = table
ok(table['a'] == ['101/4600', '404/1725', '303/115'] and table['b'] == ['1/460', '16/75', '3/425']
   and table['c'] == ['5/23', '64/3', '12/17'] and table['beta'][1:] == ['16/45', '3/1000']
   and table['gamma'] == ['1/230', '320/9', '3/10'] and mA.kon[4] == sp.Rational(404, 5)
   and mA.kon[5] == sp.Rational(303, 40) and sp.simplify(mA.kon[3] - (1 + rs)/48) == 0
   and sp.simplify(mA.koff[3] - rs/230) == 0, 'rate table of witness A')
mH = witness('H', rs)
OUT['rate_table_H'] = dict(kon=[str(sp.factor(v)) for v in mH.kon], koff=[str(v) for v in mH.koff], kcat=[str(v) for v in mH.kcat])
ok(mH.kon[0] == sp.Rational(101, 99000) and mH.kcat[1] == sp.Rational(1950, 7) and mH.kcat[4] == 52, 'rate table of witness H')
cat = [v for v in mA.kcat]; bind = [v.subs(rs, sp.Rational(3, 2)) for v in mA.kon]
ok(max(cat)/min(cat) == sp.Rational(73600, 9), 'catalytic span 73600/9 at A')
uni = [v.subs(rs, sp.Rational(14, 10)) for v in mA.kcat + mA.koff]
OUT['spans_A'] = dict(catalytic=str(max(cat)/min(cat)))

# ------------------------------------------------------------------ 2. Hopf certificates
certs = {}
for w in 'AH':
    build = (lambda ww: (lambda r: witness(ww, r)))(w)
    c = certify_hopf(build); certs[w] = c; OUT['hopf_' + w] = dump(c)
    ok(c['const_coeff_positive'], f'witness {w}: p(0,r)>0 for all r>0 (no zero eigenvalue along the family)')
cA, cH = certs['A'], certs['H']
for w, fname in (('A', 'compressed_attracting_certificate.json'), ('H', 'closed_certificate.json')):
    wsf = ROOT/'workspace_certificates'/fname
    if wsf.exists():
        src = json.loads(wsf.read_text())['source']
        ok([str(v) for v in certs[w]['p0']] == src['p0'] and [str(v) for v in certs[w]['p1']] == src['p1'],
           f'{w}: characteristic polynomials from the reaction list agree with the workspace block-formula certificate')
ok(inside(cA['r'], '1.43322830681119', '1.43322830681120'), 'A: r_A window')
ok(inside(cA['omega'], '0.23508019956219', '0.23508019956220'), 'A: omega_A window')
ok(inside(cA['t'], '0.0552627002262007', '0.0552627002262009'), 'A: t_A window')
ok(inside(cA['crossing'].re, '-0.05131591007519', '-0.05131591007517'), 'A: Re lambda\'(r_A) window')
ok(inside(cA['l1'], '-0.08915942680579', '-0.08915942680577'), 'A: first Lyapunov coefficient window (negative)')
ok(all(v.a >= Fr(b) for v, b in zip(cA['routh'], ['1', '123', '4107', '57834', '328922', '598584', '160490', '6202'])),
   'A: Routh first column 1,123,4107,57834,328922,598584,160490,6202')
ok(inside(cA['eps_derivative'].re, '0.1120758', '0.1120759'), 'A: relaxation derivative +0.11207...')
ok(inside(cH['r'], '0.26553704252', '0.26553704254') and inside(cH['omega'], '0.18038559401', '0.18038559403'), 'H: r_H, omega_H windows')
ok(inside(cH['l1'], '0.66961007953', '0.66961007956') and inside(cH['crossing'].re, '-0.04649665728', '-0.04649665726'), 'H: l1>0 and crossing windows')
ok(inside(cH['eps_derivative'].re, '0.0507344', '0.0507345'), 'H: relaxation derivative window')
omegaA = cA['omega']; a_cross = -cA['crossing'].re
cR = omegaA*cA['l1']
OUT['A_cubic_physical_time'] = bounds(cR)
ok(inside(cR, '-0.0209597', '-0.0209596'), 'A: physical-time cubic coefficient omega*l1')

# ------------------------------------------------------------------ 3. clamps
for w, rwin, l1win in (('H', ('1.6427061084', '1.6427061085'), ('13.32438121', '13.32438122')),
                       ('A', ('3.5573550512', '3.5573550513'), ('0.009159097', '0.009159098'))):
    build = (lambda ww: (lambda r: witness(ww, r, clampE=True)))(w)
    c = certify_hopf(build); OUT[f'kinase_clamped_{w}'] = dump(c)
    ok(inside(c['r'], *rwin) and inside(c['l1'], *l1win) and c['crossing'].re.b < 0,
       f'kinase clamped at {w}: Hopf point, stable complement, l1>0 (subcritical)')
    if w == 'H': ok(inside(c['omega'], '0.2367845620', '0.2367845621'), 'kinase clamped at H: frequency window')
    else: ok(inside(c['omega'], '0.2600163405', '0.2600163406'), 'kinase clamped at A: frequency window')
# both clamped: compartmental generator on the 3n+1 substrate species
for n in (1, 2, 3, 4):
    xs = sp.symbols(f'x0:{3*n+3}', positive=True); qs = sp.symbols(f'q0:{n}', positive=True)
    rr = sp.symbols(f'rho0:{2*n}', positive=True)
    m = Model(n, list(xs), list(qs), list(rr[:n]), list(rr[n:]), clampE=True, clampF=True)
    sub = list(range(n + 1)) + list(range(n + 3, 3*n + 3))
    Df = m.full_jacobian(); Q = Df.extract(sub, sub)
    colsum = all(sp.simplify(sum(Q[i, j] for i in range(len(sub)))) == 0 for j in range(len(sub)))
    offdiag = all((i == j) or Q[i, j] == 0 or Q[i, j].is_positive for i in range(len(sub)) for j in range(len(sub)))
    adj = [[bool(Q[i, j] != 0) and i != j for j in range(len(sub))] for i in range(len(sub))]
    reach = [[adj[i][j] or i == j for j in range(len(sub))] for i in range(len(sub))]
    for k in range(len(sub)):
        for i in range(len(sub)):
            for j in range(len(sub)):
                reach[i][j] = reach[i][j] or (reach[i][k] and reach[k][j])
    ok(colsum and offdiag and all(all(r_) for r_ in reach), f'both enzymes clamped, n={n}: irreducible compartmental generator (symbolic rates)')

# ------------------------------------------------------------------ 4. static elimination
for w, want in (('A', ['1074850767739/145194851031', '290975881448/145194851031', '3248745856/48398283677']),
                ('H', None)):
    L, M, A = witness(w, half).blocks(); Js = L*A.inv()*M
    L2, M2, A2 = witness(w, sp.Rational(7, 3)).blocks()
    ok(Js == L2*A2.inv()*M2, f'{w}: static Jacobian L A^-1 M independent of r')
    cp = Js.charpoly().all_coeffs()
    OUT[f'static_charpoly_{w}'] = [str(v) for v in cp]
    ok(all(v > 0 for v in cp) and cp[1]*cp[2] - cp[3] > 0, f'{w}: static elimination is Hurwitz (exact cubic test)')
    if want: ok([str(v) for v in cp[1:]] == want, 'A: static characteristic coefficients as printed')
# G positive definite, A = V G
for w in 'AH':
    m = witness(w, half); L, M, A = m.blocks()
    V = sp.diag(*[(1 + m.ratio[j])*m.q[m.site[j]] for j in range(6)])
    G = V.inv()*A
    ok(G == G.T and all(G[:k, :k].det() > 0 for k in range(1, 7)), f'{w}: A = V G with G symmetric positive definite (exact minors)')

# ------------------------------------------------------------------ 5. one-site Hurwitz lemma and added sites
z, cc, gg, u0, v0, AA, BB = sp.symbols('z c gamma u0 v0 A B', positive=True)
J1 = sp.Matrix([[0, cc, -gg], [-u0, -AA, 0], [v0, 0, -BB]])
cp1 = J1.charpoly(z).all_coeffs()
ok(sp.expand(cp1[1] - (AA + BB)) == 0 and sp.expand(cp1[2] - (AA*BB + cc*u0 + gg*v0)) == 0
   and sp.expand(cp1[3] - (BB*cc*u0 + AA*gg*v0)) == 0
   and sp.expand(cp1[1]*cp1[2] - cp1[3] - (AA*BB*(AA + BB) + AA*cc*u0 + BB*gg*v0)) == 0, 'one-site cubic and its Hurwitz identity')
# literal one-site Jacobian has that form
x1 = sp.symbols('s0 s1 e f c1 d1', positive=True); q1s = sp.symbols('q', positive=True); r1 = sp.symbols('rho sigma', positive=True)
m1 = Model(1, list(x1), [q1s], [r1[0]], [r1[1]]); Jone = m1.jacobian()
ok(Jone[0, 0] == 0 and Jone[1, 2] == 0 and Jone[2, 1] == 0 and sp.simplify(Jone[1, 0]).is_negative and sp.simplify(Jone[2, 0]).is_positive
   and sp.simplify(Jone[0, 1]).is_positive and sp.simplify(Jone[0, 2]).is_negative and sp.simplify(Jone[1, 1]).is_negative
   and sp.simplify(Jone[2, 2]).is_negative, 'one-site chart Jacobian has the sign pattern of the lemma')
K = sp.Matrix([[-2, 0, 0], [1, -1, 1], [0, 1, -2]])
ok(K.charpoly().all_coeffs() == [1, 5, 7, 2] and sp.expand((z + 2)*(z**2 + 3*z + 1) - (z**3 + 5*z**2 + 7*z + 2)) == 0, 'added-site block: det(zI-K)=(z+2)(z^2+3z+1)')
eps = sp.Symbol('epsilon', positive=True)
m4 = extended('A', rs, [eps]); J4 = m4.jacobian().applyfunc(sp.cancel)
J40 = J4.subs(eps, 0)
old = [0, 1, 2, 4, 5, 6, 8, 9, 10]; new = [7, 3, 11]            # (C_4, u_4 = S_4 + D_4, D_4) chart slots
ok(all(J40[i, j] == 0 for i in new for j in old), 'zero load: new rows have no dependence on old chart coordinates')
J3 = witness('A', rs).jacobian()
ok((J40.extract(old, old) - J3).applyfunc(sp.simplify) == sp.zeros(9, 9), 'zero load: old block equals the three-site Jacobian')
Tn = sp.Matrix([[1, 0, 0], [0, 1, -1], [0, 0, 1]])              # (C,u,D) -> (C,S,D)
ok(Tn*J40.extract(new, new)*Tn.inv() == K, 'zero load: new block is K in the coordinates (C,S,D)')
loads = [('1/100',), ('1/100', '1/100'), ('1/100', '1/100', '1/100')]
for ld in (loads[:1] if QUICK else loads):
    n = 3 + len(ld)
    build = (lambda l: (lambda r: extended('A', r, list(l))))(ld)
    ok(build(half).field() == sp.zeros(3*n + 3, 1), f'n={n}: exact equilibrium of the extended source')
    c = certify_hopf(build, norm_index=2*n + 2); OUT[f'hopf_A_n{n}'] = dump(c)
    OUT[f'totals_A_n{n}'] = [str(v) for v in build(half).totals()]
    ok(c['l1'].b < 0 and c['crossing'].re.b < 0, f'n={n}: certified supercritical Hopf point, r={mid(c["r"]):.12f}, omega={mid(c["omega"]):.12f}, l1={mid(c["l1"]):.10f}')
small = certify_hopf(lambda r: extended('A', r, ['1/100000']), norm_index=10)
ok(abs(mid(small['l1']) - mid(cA['l1'])) < 1e-4, f'load 1e-5: l1={mid(small["l1"]):.8f} approaches the three-site value (continuity check)')

# ------------------------------------------------------------------ 6. C_2 reduction
for w, wins in (('A', dict(r=('1.43082896554', '1.43082896555'), om=('0.234462267225', '0.234462267226'), l1=('-0.088880518178', '-0.088880518177'),
                         cr=('-0.051151099650', '-0.051151099649'), er=(0, '0.0024'), eo=(0, '0.000619'), el='0.000279')),
                ('H', dict(r=('0.265406066088', '0.265406066089'), om=('0.180342624794', '0.180342624795'), l1=('0.66925401509', '0.66925401510'),
                         cr=('-0.0464842889', '-0.0464842888'), er=(0, '0.000131'), eo=(0, '0.000043'), el='0.000357'))):
    build = (lambda ww: (lambda r: witness(ww, r)))(w)
    c = certify_reduced(build, fast=4, norm_index=8); OUT[f'reduced_C2_{w}'] = dump(c); full = certs[w]
    ok(inside(c['r'], *wins['r']) and inside(c['omega'], *wins['om']) and inside(c['l1'], *wins['l1']) and inside(c['crossing'].re, *wins['cr']),
       f'{w}: C2-eliminated Hopf point windows (six stable complementary roots: {all(v.a > 0 for v in c["routh"])})')
    dr = full['r'] - c['r']; do = full['omega'] - c['omega']; dl = full['l1'] - c['l1']
    ok(dr.a > 0 and dr.b < Fr(wins['er'][1]) and do.a > 0 and do.b < Fr(wins['eo'][1]) and max(abs(dl.a), abs(dl.b)) < Fr(wins['el']),
       f'{w}: threshold, frequency and cubic errors of the C2 reduction')

# ------------------------------------------------------------------ 7. resources and amplitudes
PI = I('3.1415926535897932384626433832795028', '3.1415926535897932384626433832795029')
T_H = 2*PI/omegaA
Q_H = I('77/10')*T_H
ok(witness('A', half).q[0] + witness('A', half).q[1] + witness('A', half).q[2] == sp.Rational(77, 10), 'A: steady forward throughput 77/10')
ok(inside(T_H, '26.7278372184', '26.7278372185') and inside(Q_H, '205.804346582', '205.804346583')
   and inside(Q_H/I('1106/25'), '4.65199698422', '4.65199698423'), 'A: limiting period, turnover and turnover per substrate')
OUT['A_limits'] = dict(period=bounds(T_H), turnover=bounds(Q_H))
rho_coeff = (a_cross/(-cR)).sqrt()                # rho = rho_coeff sqrt(mu)
sens = {'S3': [0, 0, 1, 0, 0, 0, 0, 0, -1], 'S3+D3': [0, 0, 1, 0, 0, 0, 0, 0, 0], 'D1': [0]*6 + [1, 0, 0]}
amp = {}
for name, cvec in sens.items():
    val = dot([C(I(v)) for v in cvec], cA['right'])
    amp[name] = 4*(val.re*val.re + val.im*val.im).sqrt()*rho_coeff
OUT['A_amplitude_constants'] = {k: bounds(v) for k, v in amp.items()}
ok(inside(amp['S3'], '2.68892171', '2.68892172') and inside(amp['S3+D3'], '7.99714705', '7.99714706') and inside(amp['D1'], '5.75472571', '5.75472572'),
   'A: peak-to-peak amplitude constants 2.6889217, 7.9971471, 5.7547257')
ok(inside(2*a_cross, '0.1026318201', '0.1026318202'), 'A: radial recovery rate constant 2a')
mhalf = witness('A', half)
ok(mhalf.totals()[0]/mhalf.totals()[2] == sp.Rational(119, 1106) and mhalf.totals()[1]/mhalf.totals()[2] == sp.Rational(1379, 2212)
   and sum(mhalf.x[9:12])/mhalf.totals()[1] == sp.Rational(1359, 1379), 'A: loading ratios 119/1106, 1379/2212, bound phosphatase 1359/1379')

# ------------------------------------------------------------------ 8. resonance constants and parameter gradient
for w in 'AH':
    build = (lambda ww: (lambda r: witness(ww, r)))(w)
    g, vRe = gain_constants(build, certs[w], {k: v for k, v in sens.items() if k != 'D1'})
    OUT[f'gain_constants_{w}'] = {k: bounds(v) for k, v in g.items()}
    one = vRe*C(certs[w]['r'])
    ok(abs(mid(one) - 1) < 1e-30, f'{w}: determinant-lemma identity r v^T R e = 1')
    certs[w]['gain'] = g
gA, gH = certs['A']['gain'], certs['H']['gain']
ok(inside(gA['S3'], '0.4836379', '0.4836380') and inside(gA['S3+D3'], '1.4383920', '1.4383921'), 'A: resonance constants K')
ok(inside(gH['S3'], '0.1260689', '0.1260690') and inside(gH['S3+D3'], '1.3029635', '1.3029636'), 'H: resonance constants K')
for w in 'AH':
    build = (lambda ww: (lambda r: witness(ww, r)))(w)
    pg = parameter_gradient(build, certs[w]); OUT[f'log_rate_gradient_{w}'] = {k: bounds(v.re) for k, v in pg.items()}
    certs[w]['pg'] = pg
    r_ = certs[w]['r']
    chain = (r_/(1 + r_))*pg['on3'].re + pg['off3'].re - r_*certs[w]['crossing'].re
    ok(chain.a < 0 < chain.b and width(chain) < 1e-30, f'{w}: chain-rule consistency of the rate gradient with lambda\'(r)')
    ok(all(v.re.a > 0 or v.re.b < 0 for v in pg.values()), f'{w}: every single rate constant and every total unfolds the Hopf point (nonzero derivative)')
pgA = certs['A']['pg']
ok(inside(pgA['cat2'].re, '0.172908', '0.172910') and inside(pgA['F_T'].re, '-0.013669', '-0.013667') and inside(pgA['E_T'].re, '0.039765', '0.039767')
   and inside(pgA['S_T'].re, '0.005985', '0.005987'), 'A: printed sensitivities (c3, totals)')

# ------------------------------------------------------------------ 9. validated pulse flow (workspace certificate)
if not QUICK:
    script = ROOT/'workspace_certificates'/'certify_measurement.py'
    if script.exists():
        run = subprocess.run([sys.executable, str(script), '--practical'], capture_output=True, text=True, cwd=script.parent)
        ok(run.returncode == 0, 'validated Taylor flow of the pulse experiment replays')
        data = json.loads((script.parent/'measurement_practical_certificate.json').read_text())
        ok(data['best']['time'] == '1/20' and Fr(data['best']['gap']) > Fr('0.0001764'), 'pulse discrimination gap > 0.0001764 at t=1/20')

# ------------------------------------------------------------------ 10. validated finite-amplitude orbits (certificates of validate_orbit.py)
ORBITS = {'7_5': dict(Y=1.06e-9, Z=3.66e-3, rho=4.24e-9, T=(27.8650146035, 27.8650146121), smin=0.1475, p2p=(0.5248, 0.5256),
                      lead=(0.905746, 0.0190), rest=0.39),
          '1': dict(Y=2.33e-10, Z=4.97e-4, rho=9.29e-10, T=(39.5906769046, 39.5906769066), smin=0.0705, p2p=(3.3486, 3.3499),
                    lead=(0.237083, 0.0556), rest=0.55)}
for tag, w in ORBITS.items():
    oc = ROOT/'certificates'/f'orbit_certificate_{tag}.json'
    if not oc.exists():
        print(f'SKIP  orbit certificate {tag} not present (run validate_orbit.py)'); continue
    data = json.loads(oc.read_text()); name = 'orbit r=' + tag.replace('_', '/')
    Yv, Zv, rhov = (float(data[k]) for k in ('Y', 'Z', 'rho'))
    ok(Zv < 1 and Yv + Zv*rhov <= rhov and Yv <= w['Y'] and Zv <= w['Z'] and rhov <= w['rho'], f'{name}: Newton-Kantorovich constants as printed')
    Tlo, Thi = (float(v) for v in data['T_interval'])
    ok(w['T'][0] <= Tlo and Thi <= w['T'][1], f'{name}: period window')
    ok(min(float(v) for v in data['species_min']) > w['smin'], f'{name}: all concentrations exceed {w["smin"]}')
    ok(float(data['p2p_lower'][3]) >= w['p2p'][0] and float(data['p2p_upper'][3]) <= w['p2p'][1], f'{name}: free S3 peak-to-peak window')
    ok(data.get('minimal_period_level') is not None, f'{name}: minimal period certified')
    g = data['gershgorin']; discs = sorted(g['nontrivial_discs'], key=lambda t: -abs(t[0]))
    ok(all(abs(c) + rr < 1 for c, rr in discs) and abs(discs[0][0] - w['lead'][0]) < 5e-7 and discs[0][1] <= w['lead'][1]
       and all(abs(c) + rr <= w['rest'] for c, rr in discs[1:]), f'{name}: Floquet multiplier discs as printed')
    ok(abs(g['trivial_disc'][0] - 1) < g['trivial_disc'][1] and all(abs(g['trivial_disc'][0] - c) > g['trivial_disc'][1] + rr for c, rr in discs),
       f'{name}: the disc containing 1 is isolated')
(ROOT/'certificates').mkdir(exist_ok=True)
(ROOT/'certificates'/'paper_certificates.json').write_text(json.dumps(OUT, indent=1))
print(f'\nall {NPASS[0]} checks passed in {time.time()-t0:.1f} s')
