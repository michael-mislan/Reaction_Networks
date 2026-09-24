"""Write the data tables of the paper from the exact sources (no hand transcription)."""
import json
from pathlib import Path
import sympy as sp
import mpmath as mpm
from clock import PATCH, FINITE, finite_model, rate_list, RATE_NAMES

HERE = Path(__file__).resolve().parent
OUT = HERE/'tables'; OUT.mkdir(exist_ok=True)
SP = [r'S_0', r'S_1', r'S_2', r'S_3', r'E', r'F', r'C_1', r'C_2', r'C_3', r'D_1', r'D_2', r'D_3']

# ---- Table: rational patch
rows = [r'\begin{tabular}{lrr@{\qquad}lrr}', r'\toprule',
        r'Species & $x_0$ & $v$ & Species & $x_0$ & $v$\\', r'\midrule']
for i in range(6):
    j = i + 6
    rows.append(f'${SP[i]}$ & {PATCH["x0"][i]} & ${PATCH["v"][i]}$ & ${SP[j]}$ & {PATCH["x0"][j]} & ${PATCH["v"][j]}$\\\\')
rows += [r'\midrule', r'Current & $\phi_0$ & $w$ &&&\\', r'\midrule']
for i in range(3):
    rows.append(f'$\\phi_{i+1}$ & {PATCH["q0"][i]} & ${PATCH["w"][i]}$ &&&\\\\')
rows += [r'\bottomrule', r'\end{tabular}']
(OUT/'patch.tex').write_text('\n'.join(rows) + '\n')

# ---- Table: dyadic finite source
rows = [r'\begin{tabular}{ll@{\qquad}ll}', r'\toprule',
        r'Quantity & exact value & Quantity & exact value\\', r'\midrule']
names = [f'${s}^*$' for s in SP] + [r'$\phi_1$', r'$\phi_2$', r'$\phi_3$', r'$r$']
vals = FINITE['xstar'] + FINITE['currents'] + [FINITE['r']]


def dy(v):
    f = sp.Rational(v); e = sp.log(f.q, 2); assert e == int(e)
    return f'${f.p}\\cdot2^{{-{int(e)}}}$'


for i in range(8):
    rows.append(f'{names[i]} & {dy(vals[i])} & {names[i+8]} & {dy(vals[i+8])}\\\\')
rows += [r'\bottomrule', r'\end{tabular}']
(OUT/'dyadic.tex').write_text('\n'.join(rows) + '\n')

# ---- Table: eighteen rates of the finite witness, model and an illustrative dimensional scale
m = finite_model(); rates = rate_list(m)
assert [str(v) for v in rates] == [str(sp.Rational(v)) for v in FINITE['rates_association_dissociation_catalysis_per_arm']]
tex = {'a': 'a', 'b': 'b', 'c': 'c', 'alpha': r'\alpha', 'beta': r'\beta', 'gamma': r'\gamma'}
rows = [r'\begin{tabular}{lllr@{\qquad}lllr}', r'\toprule',
        r'Rate & model value & physical value & & Rate & model value & physical value &\\', r'\midrule']


def fmt(x):
    v = mpm.mpf(x.p)/mpm.mpf(x.q)
    if mpm.mpf('1e-3') <= v < 10000:
        return '$' + mpm.nstr(v, 5, min_fixed=-10, max_fixed=10, strip_zeros=False) + '$'
    mant, ex = mpm.nstr(v, 5, min_fixed=0, max_fixed=0, strip_zeros=False).split('e')
    return f'${mant}\cdot10^{{{int(ex)}}}$'


def cell(k):
    nm, v = RATE_NAMES[k], rates[k]
    base, idx = nm[:-1], nm[-1]
    bim = base in ('a', 'alpha')
    phys = v/10 if bim else v/100
    unit = r'$\mu\mathrm{M}^{-1}\mathrm{s}^{-1}$' if bim else r'$\mathrm{s}^{-1}$'
    return f'${tex[base]}_{idx}$ & {fmt(v)} & {fmt(phys)} & {unit}'


for i in range(9):
    rows.append(cell(i) + ' & ' + cell(i + 9) + r'\\')
rows += [r'\bottomrule', r'\end{tabular}']
(OUT/'rates.tex').write_text('\n'.join(rows).replace('e-', r'e$-$') + '\n')

# ---- Table: single-rate Kalman determinants
R = json.loads((HERE/'data'/'rank_all_inputs.json').read_text())
lab = {'a': 'a', 'c': 'c', 'alpha': r'\alpha', 'gamma': r'\gamma', 'b': 'b', 'beta': r'\beta'}
vec = {'a': r'e_{C_%s}', 'c': r'e_{\pi_%s}-e_{C_%s}', 'alpha': r'e_{D_%s}', 'gamma': r'-e_{\pi_%s}-e_{D_%s}'}
rows = [r'\begin{tabular}{llr@{\qquad}llr}', r'\toprule',
        r'Rates & direction & scaled determinant & Rates & direction & scaled determinant\\', r'\midrule']
keys = list(R['inputs'].keys()); cells = []
for key in keys:
    first = key.split(',')[0].strip(); base, idx = first[:-1], first[-1]
    names_ = ', '.join(f'${lab[k.strip()[:-1]]}_{k.strip()[-1]}$' for k in key.split(','))
    d = R['inputs'][key]; assert d['rank9']
    lo, hi = d['scaled_determinant'].strip('[]').split(',')
    lo, hi = mpm.mpf(lo), mpm.mpf(hi); mid = (lo + hi)/2
    assert abs(hi - lo) < abs(mid)*mpm.mpf('1e-6')
    mant, ex = mpm.nstr(mid, 5, min_fixed=0, max_fixed=0, strip_zeros=False).split('e')
    direction = vec[base] % ((idx,)*vec[base].count('%s'))
    cells.append(f'{names_} & ${direction}$ & ${mant}\\cdot10^{{{int(ex)}}}$')
for i in range(6):
    rows.append(cells[2*i] + ' & ' + cells[2*i+1] + r'\\')
rows += [r'\bottomrule', r'\end{tabular}']
(OUT/'rank.tex').write_text('\n'.join(rows) + '\n')
print('tables written')
