"""Interval Kalman-rank test for alpha1-only relative modulation."""
import json
from pathlib import Path
from mpmath import mp, iv
from local_certificate import Jet, source

W = Path(__file__).resolve().parent
mp.dps = 80
iv.dps = 80
Jet.ctx = iv
cert = json.loads((W / 'local_root_certificate.json').read_text())
s, r, omega = [iv.mpf(x) + iv.mpf(['-1e-20', '1e-20'])
               for x in cert['root_center']]
jets, _ = source(Jet(s), Jet(r))
J = iv.matrix([[x.v.real for x in row] for row in jets])
v = iv.matrix([int(i == 6) for i in range(9)])
columns = []
for k in range(9):
    columns.append(v)
    v = J * v / 100
A = [[columns[j][i] for j in range(9)] for i in range(9)]
pivots, sign = [], 1
for k in range(9):
    p = max(range(k, 9), key=lambda i: float(abs(A[i][k]).mid))
    if p != k:
        A[k], A[p] = A[p], A[k]
        sign = -sign
    pivot = A[k][k]
    assert pivot.a > 0 or pivot.b < 0, (k, str(pivot))
    pivots.append(pivot)
    for i in range(k + 1, 9):
        mult = A[i][k] / pivot
        for j in range(k + 1, 9):
            A[i][j] -= mult * A[k][j]
        A[i][k] = iv.mpf(0)
det = iv.mpf(sign)
for pivot in pivots:
    det *= pivot
out = dict(root_center=cert['root_center'], radius='1e-20',
           precision_digits=80, scaled_determinant=str(det),
           pivots=[str(p) for p in pivots], rank=9,
           scope='alpha1-only rank at the certified GH box; no finite pulse')
(W / 'single_input_rank_certificate.json').write_text(
    json.dumps(out, indent=2))
print(json.dumps(out, indent=2))
