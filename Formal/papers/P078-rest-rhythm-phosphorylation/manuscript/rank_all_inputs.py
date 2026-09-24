"""Directed-interval Kalman rank test for EVERY single-rate input at the certified
generalized-Hopf point (Proposition 6.2 of the paper).

Relative modulation of one rate constant k enters the chart field through the
equilibrium input column b_k = d f / d log k |_(x*).  With phi_i the catalytic
current and e_pi_i, e_C_i, e_D_i the chart unit vectors, the columns are

    a_i, b_i       :  +-(1+rho_i) phi_i e_C_i ,  -+ rho_i phi_i e_C_i   (direction e_C_i)
    alpha_i,beta_i :  direction e_D_i
    c_i            :  phi_i (e_pi_i - e_C_i)
    gamma_i        :  phi_i (-e_pi_i - e_D_i)

so twelve directions cover the eighteen rates.  The Jacobian is enclosed on the
ball of radius 3.1e-30 around the certified centre: the Newton--Kantorovich
certificate maps the radius-1e-20 box into the ball of radius < 3.084e-30, so the
exact root lies in that smaller ball.  The alpha_1 direction is also run on the
full 1e-20 box, reproducing the workspace certificate.
"""
import json, sys
from pathlib import Path
from mpmath import mp, iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'workspace_certificates'))
from local_certificate import Jet, source                      # noqa: E402

DPS = 90
mp.dps = DPS; iv.dps = DPS
Jet.ctx = iv
cert = json.loads((HERE/'workspace_certificates'/'local_root_certificate.json').read_text())
assert cert['strict_inclusion'] and iv.mpf(cert['image_radius_upper'].strip('[]').split(',')[1]).b < iv.mpf('3.1e-30').a


def jac(radius):
    box = [iv.mpf(x) + iv.mpf(['-' + radius, radius]) for x in cert['root_center']]
    jets, _ = source(Jet(box[0]), Jet(box[1]))
    return iv.matrix([[x.v.real for x in row] for row in jets])


def kalman(J, b):
    v = iv.matrix(b); cols = []
    for k in range(9):
        cols.append(v); v = J*v/100
    A = [[cols[j][i] for j in range(9)] for i in range(9)]
    piv, sign = [], 1
    for k in range(9):
        p = max(range(k, 9), key=lambda i: float(abs(A[i][k]).mid))
        if p != k:
            A[k], A[p] = A[p], A[k]; sign = -sign
        pv = A[k][k]
        if not (pv.a > 0 or pv.b < 0):
            return None, piv
        piv.append(pv)
        for i in range(k + 1, 9):
            mlt = A[i][k]/pv
            for j in range(k + 1, 9):
                A[i][j] -= mlt*A[k][j]
            A[i][k] = iv.mpf(0)
    det = iv.mpf(sign)
    for pv in piv:
        det *= pv
    return det, piv


def e(*idx_sign):
    v = [0]*9
    for i, s in idx_sign:
        v[i] = s
    return v


DIRS = {}
for i in range(3):
    DIRS[f'a{i+1}, b{i+1}'] = e((3 + i, 1))
    DIRS[f'c{i+1}'] = e((i, 1), (3 + i, -1))
    DIRS[f'alpha{i+1}, beta{i+1}'] = e((6 + i, 1))
    DIRS[f'gamma{i+1}'] = e((i, -1), (6 + i, -1))

out = {'arithmetic': f'mpmath.iv, {DPS} decimal digits, directed', 'scaled': 'column k divided by 100^k',
       'radius': '3.1e-30 (exact root lies in this ball by the Newton-Kantorovich image bound)', 'inputs': {}}
J = jac('3.1e-30')
ok = True
for name, b in DIRS.items():
    det, piv = kalman(J, b)
    good = det is not None and (det.a > 0 or det.b < 0)
    ok &= good
    out['inputs'][name] = dict(direction=b, rank9=bool(good), scaled_determinant=str(det),
                               pivots_found=len(piv))
    print(f'{name:16s} rank9={good}  det={mp.nstr(det.mid, 10) if det is not None else None}', flush=True)
det, _ = kalman(jac('1e-20'), DIRS['alpha1, beta1'])
out['alpha1_full_box_1e-20'] = str(det)
assert det.a > 0 or det.b < 0
print('alpha1 on the full 1e-20 box:', mp.nstr(det.a, 12), mp.nstr(det.b, 12))
out['all_rank_9'] = bool(ok)
(HERE/'data'/'rank_all_inputs.json').write_text(json.dumps(out, indent=1))
assert ok
print('ALL EIGHTEEN SINGLE-RATE INPUTS CONTROLLABLE AT THE GH POINT')
