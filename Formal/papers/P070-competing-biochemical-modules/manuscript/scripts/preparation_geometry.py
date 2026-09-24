"""Exact preparation-geometry calculations for the correlated region R = B(R).

Membership test: |M^{-1}(u0-c)| <= R componentwise.  For an independent box
centred at p with halfwidths eps, a sufficient test is
    |M^{-1}(p-c)| + |M^{-1}| eps <= R.
"""
import json
from fractions import Fraction as F
from pathlib import Path
root = Path(__file__).resolve().parents[1]
d = json.loads((root / 'data/modal_box.json').read_text())
M = [[F(x) for x in r] for r in d['M']]; MI = [[F(x) for x in r] for r in d['inverse']]
c = [F(x[0]) for x in d['center']]
names = ['x', 'z', 'e1', 'e2', 'zT', 'h', 'w', 'v']
R = [F(9, 10), F(417, 500)] + [F(7, 10)] * 6
N = range(8)
out = {}
for label, a1 in (('p (a1=5/6)', F(5, 6)), ('p_D (a1=98/125)', F(98, 125))):
    p = [c[i] + a1 * M[i][1] for i in N]
    slack = [R[i] - (a1 if i == 1 else 0) for i in N]
    rows = [sum(abs(MI[i][j]) for j in N) for i in N]
    uni = min(slack[i] / rows[i] for i in N); bind = min(N, key=lambda i: slack[i] / rows[i])
    rel_rows = [sum(abs(MI[i][j]) * p[j] for j in N) for i in N]
    rel = min(slack[i] / rel_rows[i] for i in N); bindrel = min(N, key=lambda i: slack[i] / rel_rows[i])
    single = [min(slack[i] / abs(MI[i][j]) for i in N if MI[i][j] != 0) for j in N]
    sbind = [min((i for i in N if MI[i][j] != 0), key=lambda i: slack[i] / abs(MI[i][j])) for j in N]
    HT = F(21, 10) * (F(505, 1000) - p[4]) * p[7]
    out[label] = dict(center=[float(x) for x in p], HT_center=float(HT),
                      uniform_halfwidth_max=float(uni), uniform_binding_modal_coordinate=bind,
                      relative_halfwidth_max=float(rel), relative_binding_modal_coordinate=bindrel,
                      single_coordinate_halfwidth_max=dict(zip(names, [float(x) for x in single])),
                      single_coordinate_binding=dict(zip(names, sbind)),
                      single_coordinate_relative=dict(zip(names, [float(single[j] / p[j]) for j in N])))
proj = lambda q: [float(sum(abs(M[j][k]) * q[k] for k in N)) for j in N]
out['projection_halfwidths_R'] = dict(zip(names, proj(R)))
out['projection_halfwidths_D'] = dict(zip(names, proj([F(3, 4)] + [F(1, 20)] * 7)))
# D is a_0 in [-3/4,3/4], a_1 in [.734,.834], others 1/20; check P subset D subset R
eps = F(1, 2000000)
rad = [eps * sum(abs(MI[i][j]) for j in N) for i in N]
assert rad[0] <= F(3, 4) and F(5, 6) + rad[1] <= F(417, 500) and F(5, 6) - rad[1] >= F(98, 125) - F(1, 20)
assert all(rad[i] <= F(1, 20) for i in range(2, 8))
out['P_subset_D_subset_R'] = True
out['P_modal_radii'] = [float(x) for x in rad]
(root / 'data/preparation_geometry.json').write_text(json.dumps(out, indent=1) + '\n')
print(json.dumps(out, indent=1))
