"""Recompute the numbers printed in main.tex and compare them with the certificates.

    python check_paper.py            (about one minute; run after make_data.py etc.)

Sections 1-3 are independent of the workspace certificate code: the model is rebuilt from the
reaction list (phos.Model), the normal form by a separate recurrence (clock.normal_form), and the
Hopf certificates by the rational-interval code of the companion paper (phos.certify_hopf).
"""
import json, hashlib, sys, time
from pathlib import Path
from fractions import Fraction as Fr
import numpy as np
import sympy as sp
import mpmath as mpm
from clock import (patch_model, finite_model, rate_list, mp_JB, critical_pair, normal_form, GH_CENTER,
                   FINITE, RATE_NAMES, FloatSystem)
from phos import certify_hopf, mid, width

HERE = Path(__file__).resolve().parent
WC = HERE/'workspace_certificates'
N_OK = [0]; FAILED = []
t0 = time.time()


def check(name, cond, info=''):
    N_OK[0] += bool(cond)
    if not cond:
        FAILED.append(name)
    print(('  ok  ' if cond else 'FAIL  ') + name + (f'   [{info}]' if info else ''), flush=True)


def ivl(s):
    lo, hi = s.strip('[]() ').split(',')
    return mpm.mpf(lo), mpm.mpf(hi)


def inside(s, lo, hi):
    a, b = ivl(s) if isinstance(s, str) else s
    return mpm.mpf(lo) < a and b < mpm.mpf(hi)


mpm.mp.dps = 45
print('1. exact algebra')
s0, r0, om0 = [sp.Rational(v) for v in GH_CENTER]
mG = patch_model(s0, r0); mF = finite_model()
check('patch equilibrium is exact', all(v == 0 for v in mG.field()))
check('witness equilibrium is exact', all(v == 0 for v in mF.field()))
check('R P = I and P annihilates the totals', mF.Rm*mF.P == sp.eye(9) and
      all(sum(mF.P[i, j] for i in idx) == 0 for j in range(9)
          for idx in ([4, 6, 7, 8], [5, 9, 10, 11], [0, 1, 2, 3, 6, 7, 8, 9, 10, 11])))
check('chart input vectors: binding = e_Z, kinase catalysis = e_pi - e_C, phosphatase catalysis = -e_pi - e_D',
      all((mF.Rm*mF.N[:, 3*j]) == sp.eye(9)[:, 3 + j] for j in range(6)) and
      all((mF.Rm*mF.N[:, 3*j + 2]) == sp.eye(9)[:, j] - sp.eye(9)[:, 3 + j] for j in range(3)) and
      all((mF.Rm*mF.N[:, 3*j + 2]) == -sp.eye(9)[:, j - 3] - sp.eye(9)[:, 3 + j] for j in range(3, 6)))
check('alpha_1 equilibrium input column is (1+r) phi_1 e_D1',
      mF.kon[3]*mF.x[1]*mF.x[5] == (1 + sp.Rational(FINITE['r']))*mF.q[0])
rates = rate_list(mF)
check('eighteen exact rates agree with the workspace list',
      [str(v) for v in rates] == [str(sp.Rational(v)) for v in FINITE['rates_association_dissociation_catalysis_per_arm']])
tot = mF.totals()
check('totals', [str(v) for v in tot] == [str(sp.Rational(v)) for v in FINITE['totals']],
      ', '.join(f'{float(v):.6f}' for v in tot))
check('totals rounded as printed', [round(float(v), 4) for v in tot] == [4.5333, 21.6998, 40.3944])
assoc = [rates[3*j] for j in range(6)]; uni = [rates[3*j + k] for j in range(6) for k in (1, 2)]
check('association span 7.6e3, unimolecular span 2.2e4',
      7500 < max(assoc)/min(assoc) < 7650 and 21900 < max(uni)/min(uni) < 22100,
      f'{float(max(assoc)/min(assoc)):.0f}, {float(max(uni)/min(uni)):.0f}')
boundF = 1 - mF.x[5]/tot[1]
check('bound phosphatase fraction at rest 97.57%', abs(float(boundF) - 0.975735) < 1e-6, f'{float(boundF):.6f}')
check('physical totals and free enzymes', [round(float(v)/10, 5) for v in (tot[2], tot[0], tot[1])] == [4.03944, 0.45333, 2.16998]
      and round(float(mF.x[4])/10, 5) == 0.25631 and round(float(mF.x[5])/10, 6) == 0.052655)
check('path point: witness S0 is 30^0.3 2^0.7 to binary64', abs(float(mF.x[0]) - 30**0.3*2**0.7) < 1e-12)
check('path direction: v_S0 = x_S0 log(2/30)', abs(float(sp.Rational('-9.528787642804')) - 3.518689438964*np.log(2/30)) < 1e-9)

print('2. generalized Hopf point: independent normal form (mpmath, 45 digits)')
J, B = mp_JB(mG)
lam, q, ell, E = critical_pair(J, mpm.mpf(GH_CENTER[2]))
G, H = normal_form(J, B, lam, q, ell)
cert = json.loads((WC/'local_root_certificate.json').read_text())
check('critical eigenvalue is i*omega at the centre', abs(mpm.re(lam)) < 1e-30 and abs(mpm.im(lam) - mpm.mpf(GH_CENTER[2])) < 1e-30)
others = sorted([e for e in E if abs(mpm.im(e)) < 0.1], key=lambda z: mpm.re(z))
check('seven complementary eigenvalues negative', len(others) == 7 and all(mpm.re(e) < -0.02 for e in others),
      ', '.join(mpm.nstr(mpm.re(e), 5) for e in others))
check('Re G1 = 0 at the centre (to 1e-30)', abs(mpm.re(G[1])) < 1e-30, mpm.nstr(G[1], 10))
check('Re G2 inside the certified enclosure and inside the printed interval',
      inside((mpm.re(G[2]), mpm.re(G[2])), *ivl(cert['c2_real'])) and inside(cert['c2_real'], '-0.044427531', '-0.044427474'),
      mpm.nstr(G[2], 12))
check('l2 = -0.18373', abs(mpm.re(G[2])/mpm.im(lam) + mpm.mpf('0.18373')) < 1e-5)
# eigenvalue derivative with respect to r:  ell^T (dJ/dr) q
h = sp.Rational(1, 10**20)
Jp, _ = mp_JB(patch_model(s0, r0 + h)); Jm, _ = mp_JB(patch_model(s0, r0 - h))
dJ = (Jp - Jm)/(2*mpm.mpf(10)**-20)
ar = mpm.re(sum(ell[i]*sum(dJ[i, j]*q[j] for j in range(9)) for i in range(9)))
check('a_r inside the certified enclosure', inside((ar, ar), *ivl(cert['eigenvalue_r_derivative'])) and
      inside(cert['eigenvalue_r_derivative'], '-0.05308906', '-0.05308905'), mpm.nstr(ar, 12))
check('cubic slope and unfolding product as printed', inside(cert['cubic_Hopf_slope'], '-0.11964982', '-0.11964981') and
      inside(cert['unfolding_product'], '0.0063520958289', '0.0063520958316'))
check('Newton-Kantorovich numbers as printed', ivl(cert['Y_upper'])[1] < mpm.mpf('4.730e-47') and
      ivl(cert['eta_upper'])[1] < mpm.mpf('3.084e-10') and ivl(cert['image_radius_upper'])[1] < mpm.mpf('3.084e-30')
      and cert['strict_inclusion'] and cert['contraction'] and inside(cert['preconditioner_det'], '-0.12099', '-0.12098'))
check('Routh first column of the degree-seven quotient positive', all(ivl(v)[0] > 0 for v in cert['routh_first_column']))
# Kalman determinants
rk = json.loads((HERE/'data'/'rank_all_inputs.json').read_text())
check('all twelve input directions certified rank 9', rk['all_rank_9'] and len(rk['inputs']) == 12)
check('alpha_1 determinant on the full box as printed', inside(rk['alpha1_full_box_1e-20'], '-1.874031380e-46', '-1.874028367e-46'))
wsr = json.loads((WC/'single_input_rank_certificate.json').read_text())
check('... and agrees with the workspace certificate', ivl(wsr['scaled_determinant']) == ivl(rk['alpha1_full_box_1e-20']))
ok = True
for name, d in rk['inputs'].items():
    b = mpm.matrix(d['direction']); K = mpm.matrix(9, 9); v = b
    for k in range(9):
        for i in range(9):
            K[i, k] = v[i]
        v = J*v/100
    det = mpm.det(K); lo, hi = ivl(d['scaled_determinant'])
    ok &= bool(abs(det - (lo + hi)/2) < abs(det)*mpm.mpf('1e-6'))
check('independent mpmath determinants agree with all twelve enclosures', ok)

print('3. rigorous Hopf certificates with the companion interval code')
cm = certify_hopf(lambda r: patch_model(sp.Rational(-1, 10**9), r)); cp = certify_hopf(lambda r: patch_model(sp.Rational(1, 10**9), r))
check('l1 > 0 at s = -1e-9 and l1 < 0 at s = +1e-9', cm['l1'].a > 0 and cp['l1'].b < 0, f"{mid(cm['l1']):.5e}, {mid(cp['l1']):.5e}")
check('printed values of l1 and r_H on the two sides', abs(mid(cm['l1']) - 4.9477e-10) < 1e-14 and abs(mid(cp['l1']) + 4.9484e-10) < 1e-14
      and abs(mid(cm['r']) - 1.38378737669705) < 1e-14 and abs(mid(cp['r']) - 1.38378737740583) < 1e-14)
slope = (mid(cp['l1']) - mid(cm['l1']))/2e-9
check('difference quotient of l1 equals b_s/omega', abs(slope + 0.49481) < 1e-5 and abs(slope - (-0.11964981/0.24181139)) < 1e-5, f'{slope:.6f}')
cf = certify_hopf(lambda r: finite_model(r))
check('witness family: subcritical Hopf, printed r_H, omega_H, l1, crossing',
      cf['l1'].a > 0 and abs(mid(cf['r']) - 1.34467152419) < 1e-11 and abs(mid(cf['omega']) - 0.24255881) < 1e-8 and
      abs(mid(cf['l1']) - 0.04720617438) < 1e-11 and width(cf['l1']) < 1e-34 and
      abs(mid(cf['crossing']) - (-0.0532328 + 0.0490246j)) < 1e-6 and all(v.a > 0 for v in cf['routh']),
      f"r_H={mid(cf['r']):.12f}, l1={mid(cf['l1']):.11f}")
check('witness r exceeds r_H', float(sp.Rational(FINITE['r'])) > mid(cf['r']) and abs(float(sp.Rational(FINITE['r'])) - 1.3520137037) < 1e-9)

print('4. finite-witness certificates (workspace) against the printed statements')
fc = json.loads((WC/'finite_fourier_certificate.json').read_text())
Y, Z1, Z2, rho = mpm.mpf(fc['Y_upper']), mpm.mpf(fc['Z_upper']), mpm.mpf(fc['L_upper']), mpm.mpf(fc['radius'])
check('radii bounds as printed', Y < mpm.mpf('2.732e-13') and Z1 < mpm.mpf('0.706101') and Z2 < mpm.mpf('3.774607e8'))
check('radii polynomial inequalities', Y + Z1*rho + Z2*rho**2/2 < mpm.mpf('1.333e-12') < rho and Z1 + Z2*rho < mpm.mpf('0.706667'))
check('finite block defect, norm of A, dimension, Z parts', fc['A_D_inverse_error_upper'] < 0.0165 and fc['A_norm_upper'] < 6.55e5
      and fc['dimension'] == 3466 and fc['M_inverse'] == 192 and fc['N_center'] == 40 and
      abs(fc['Zfinite_upper'] - 0.3653) < 1e-4 and abs(fc['Ztail_upper'] - 0.7061) < 1e-4 and abs(fc['Zfar_upper'] - 0.6260) < 1e-4)
gc = json.loads((WC/'finite_geometry_certificate.json').read_text())
check('period interval as printed', inside(gc['period'], '28.69124274158', '28.69124274167'))
check('readout range lower bound', ivl(gc['S3_plus_D3_peak_to_peak_lower'])[0] > mpm.mpf('2.34560'))
printed = [4.5318, 10.763, 0.12716, 0.090787, 2.1393, 0.21352, 0.42530, 0.10747, 0.99339, 16.405, 0.12016, 2.7860]
check('species lower bounds as printed', all(ivl(v)[0] > p for v, p in zip(gc['species_global_lower_bounds'], printed)))
check('sink Routh column positive (ten entries)', len(gc['sink_routh_first_column']) == 10 and
      all(ivl(v)[0] > 0 for v in gc['sink_routh_first_column']))
ac = json.loads((WC/'attraction_certificate.json').read_text())
check('attraction certificate numbers', ac['transverse_attraction_pass'] and ac['steps'] == 8192 and ac['order'] == 20 and
      all(ivl(v)[0] > mpm.mpf('0.07') for v in ac['LDL_pivots']) and ac['local_cauchy_tail_upper'] < 1.39e-23 and
      ac['actual_J_perturbation_upper'] < 9.70e-10 and ac['monodromy_entry_radius_max'] < 2.4e-4)
nf = ac['phase_transversality'].split('+')[0].strip('( ')
check('section transversality n.f', inside(nf, '0.024935', '0.024936'))
a = np.load(WC/'fourier_N40.npz')
check('binary64 source equals the dyadic table; omega-bar as printed',
      all(Fr(float(v)) == Fr(str(w)) for v, w in zip(a['xstar'], FINITE['xstar'])) and float(a['omega']) == 0.21899313890868646)
check('first harmonic dominates the validation radius (minimal period)', np.abs(a['z'][41]).sum() > 1e-3, f"{np.abs(a['z'][41]).sum():.4f}")
sc = json.loads((WC/'sink_capture_certificate.json').read_text())
check('sink capture constants', sc['lambda'] > 1.2418e-5 and ivl(sc['K_upper'])[1] < mpm.mpf('1807.46') and
      ivl(sc['metric_decay_lower'])[0] > mpm.mpf('1.0610e-5'))
rp = json.loads((WC/'replay_results.json').read_text())
check('six-stage replay passed', rp['all_pass'] and len(rp['stages']) == 6)

print('5. numerics quoted in the text')
num = json.loads((HERE/'data'/'numerics.json').read_text())
st, un = num['stable_cycle'], num['unstable_cycle']
check('DOP853 period lies in the certified interval', 28.69124274158 < st['period'] < 28.69124274167, repr(st['period']))
check('multipliers 0.92986266, 0.57986749, 7.98e-4', abs(st['multipliers'][1][0] - 0.92986266) < 1e-8 and
      abs(st['multipliers'][2][0] - 0.57986749) < 1e-8 and abs(st['multipliers'][3][0] - 7.98e-4) < 1e-6)
check('unstable cycle: period 26.50998, range 1.0276, multiplier 1.01604', abs(un['period'] - 26.50998) < 1e-5 and
      abs(un['readout_range'] - 1.0276) < 1e-4 and abs(un['multipliers'][0][0] - 1.01604) < 1e-5)
check('fold at r = 1.35628; window 0.86%', abs(num['branch']['r_fold_estimate'] - 1.35628) < 1e-5 and
      abs((num['branch']['r_fold_estimate'] - 1.3446715)/1.35 - 0.0086) < 1e-4)
rc = num['recovery']
check('recovery: 13.75 and 89.19 periods; 10.96 h and 2.96 d', abs(rc['cycle_efold_periods'] - 13.75) < 0.01 and
      abs(rc['sink_efold_periods'] - 89.19) < 0.01 and abs(rc['cycle_efold']*100/3600 - 10.96) < 0.01 and
      abs(rc['sink_efold']*100/86400 - 2.96) < 0.01 and abs(rc['sink_abscissa'] + 0.00039080) < 1e-8)
check('period in minutes', abs(st['period']*100/60 - 47.8187) < 1e-4)
S = FloatSystem(mF); cy = np.load(HERE/'data'/'cycles.npz')
from scipy.integrate import solve_ivp
T = float(cy['stable_T'])
sol = solve_ivp(lambda t, y: S.f(t, y), (0, T), cy['stable_y0'], method='DOP853', rtol=1e-12, atol=1e-15, dense_output=True)
tt = np.linspace(0, T, 20001); X = S.x0[:, None] + S.P @ sol.sol(tt)
FT, ET = float(tot[1]), float(tot[0])
bF, bE = 1 - X[5]/FT, 1 - X[4]/ET
check('bound fractions along the cycle', abs(bF.min() - 0.955) < 1e-3 and abs(bF.max() - 0.989) < 1e-3 and
      abs(bE.min() - 0.37) < 5e-3 and abs(bE.max() - 0.53) < 6e-3, f'{bF.min():.4f}..{bF.max():.4f}, {bE.min():.4f}..{bE.max():.4f}')
dU3 = S.kcat[2]*X[8] - S.kcat[5]*X[11]
check('max |d(S3+D3)/dt| = 0.323', abs(np.abs(dU3).max() - 0.323) < 1e-3)
kin = sum(S.kcat[i]*X[6 + i] for i in range(3))
check('kinase turnover per period 222.7 (cycle) and 230.3 (rest)', abs(np.trapezoid(kin, tt) - 222.7) < 0.1 and
      abs(sum(S.kcat[i]*S.x0[6 + i] for i in range(3))*T - 230.3) < 0.1)
check('copy numbers of free phosphatase: 32 per fL', abs(float(mF.x[5])*0.1e-6*1e-15*6.02214076e23 - 31.7) < 0.1)
sw = json.loads((HERE/'data'/'switch_demo.json').read_text())
check('switching illustration numbers', sw['A'] == 0.1 and sw['periods'] == 3 and sw['amp_after_on'] > sw['amp_unstable_cycle'] and
      abs(sw['amp_after_off'] - 0.107) < 1e-3 and abs(sw['amp_unstable_cycle'] - 0.508) < 1e-3 and
      abs(sw['readout_range_400_periods_after_on'] - 2.34591) < 1e-5 and sw['readout_range_600_periods_after_off'] < 2.7e-4
      and sw['min_species'] > 0.106)
R_, a_, b_, d_ = sp.symbols('R a b d', positive=True)
Rp2 = (b_ + sp.sqrt(b_**2 + 4*d_*a_))/(2*d_)
expr = sp.diff(R_*(a_ + b_*R_**2 - d_*R_**4), R_).subs(R_, sp.sqrt(Rp2)) + 2*Rp2*sp.sqrt(b_**2 + 4*d_*a_)
check('radial derivative at R_+ equals -2 R_+^2 sqrt(b^2+4da)', sp.simplify(expr) == 0)

print('6. second computer-assisted proof of the witness orbit (multiple shooting, binary64 intervals)')
p = HERE/'certificates'/'orbit_certificate_witness.json'
if p.exists():
    oc = json.loads(p.read_text())
    lo, hi = float(oc['T_interval'][0]), float(oc['T_interval'][1])
    check('its period interval lies inside the printed intervals', 28.69124274158 < lo < hi < 28.69124274167 and
          28.6912427416038 <= lo and hi <= 28.6912427416451, f'[{lo!r}, {hi!r}]')
    check('Y, Z, rho as printed', float(oc['Y']) <= 5.16e-12 and float(oc['Z']) <= 6.15e-5 and abs(float(oc['rho']) - 2.062e-11) < 1e-14
          and float(oc['Y']) + float(oc['Z'])*float(oc['rho']) < float(oc['rho']) and oc['m'] == 256 and oc['q'] == 89 and oc['order'] == 12)
    smin = [float(v) for v in oc['species_min']]
    check('positivity and printed species bounds', min(smin) > 0.1046 and smin[3] >= 0.10463 and smin[7] >= 0.10864 and smin[10] >= 0.12168
          and smin[2] >= 0.12982 and smin[5] >= 0.22997 and sorted(smin)[5] > 0.23, f'min species {min(smin):.5f}')
    check('readout range two-sided', 2.345828 <= float(oc['readout_p2p'][0]) and float(oc['readout_p2p'][1]) <= 2.346074 and
          oc['minimal_period_level'] is not None)
    g = oc['gershgorin']; discs = g['nontrivial_discs']; tc, tr = g['trivial_disc']
    check('all nontrivial Gershgorin discs inside the unit disc', all(abs(c_) + r_ < 1 for c_, r_ in discs),
          ', '.join(f'{c_:.7f}+-{r_:.7f}' for c_, r_ in discs[:3]))
    (c1, r1), (c2, r2) = discs[0], discs[1]
    rest = max(abs(c_) + r_ for c_, r_ in discs[2:])
    check('discs isolated as claimed; printed enclosures', tc - tr > c1 + r1 and c1 - r1 > c2 + r2 and c2 - r2 > rest and
          rest < 1.7e-3 and tr < 0.0207 and 0.8881 <= c1 - r1 and c1 + r1 <= 0.9716 and 0.5219 <= c2 - r2 and c2 + r2 <= 0.6378
          and r1 < 0.0416740 and r2 < 0.0578983)
    check('certified e-folding bounds 8.4 .. 34.7 periods', 8.4 < -1/np.log(c1 - r1) < 8.5 and 34.6 < -1/np.log(c1 + r1) < 34.7,
          f'{-1/np.log(c1 - r1):.2f} .. {-1/np.log(c1 + r1):.2f}')
else:
    print('      (certificates/orbit_certificate_witness.json not present: run validate_orbit.py)')

print('7. Lean receipts')
ws = HERE.parents[2]/'problem_workspaces'/'RAF_switchable_phosphorylation_clock'
for mod, rec in (('SourceControlAlgebra', 'source_control.verify.json'), ('SingleInputColumn', 'single_input.verify.json'),
                 ('CaptureInequality', 'capture.verify.json')):
    f = ws/rec
    if f.exists():
        r = json.loads(f.read_text())
        check(f'{mod}: strict compile receipt matches the archived source', r['verified'] and r['exit_code'] == 0 and
              r['proof_sha256'] == hashlib.sha256((WC/f'{mod}.lean').read_bytes()).hexdigest())
    else:
        print(f'      (receipt {rec} not found)')

print(f'\n{N_OK[0]} checks passed, {len(FAILED)} failed   ({time.time()-t0:.0f}s)')
if FAILED:
    print('FAILED:', FAILED); sys.exit(1)
