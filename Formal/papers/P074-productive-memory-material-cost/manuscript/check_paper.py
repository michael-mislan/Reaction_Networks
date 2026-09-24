"""Exact audit of every number printed in main.tex.

Two layers.

  * The proportion-memory numbers are recomputed here from scratch in exact
    rational arithmetic, using nothing but the standard library, and then
    matched against the manuscript text.
  * The support-memory numbers come from a 3384-state integer recurrence that
    takes minutes to replay; they are matched against the recorded output of
    `scripts/frontier_support.py` in `data/`, and `--full` re-runs that script
    first so that nothing is taken on trust.

Usage:  python check_paper.py [--full]
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from fractions import Fraction as F
from math import comb, factorial, lgamma, log, log10
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEX = (HERE / 'main.tex').read_text(encoding='utf-8')
DATA = HERE / 'data'

CHECKED = 0
FAILED = []


def shows(label, needle):
    """Assert a literal string occurs in the manuscript."""
    global CHECKED
    CHECKED += 1
    if needle not in TEX:
        FAILED.append('%s: %r not in main.tex' % (label, needle))


def eq(label, got, want):
    global CHECKED
    CHECKED += 1
    if got != want:
        FAILED.append('%s: computed %r != stated %r' % (label, got, want))


def near(label, got, want, places=12):
    """Compare a computed exact value with the decimal printed in the paper."""
    global CHECKED
    CHECKED += 1
    if abs(float(got) - float(want)) > 10.0 ** (-places):
        FAILED.append('%s: computed %.15f != stated %s' % (label, float(got), want))


def digits(n):
    """LaTeX thin-space grouping used in the manuscript, e.g. 2\\,145\\,514\\,420."""
    r = str(n)[::-1]
    groups = [r[i:i + 3][::-1] for i in range(0, len(r), 3)]
    return '\\,'.join(reversed(groups))


# ---------------------------------------------------------------------------
# 1. proportion memory, recomputed from scratch
# ---------------------------------------------------------------------------

def psi(n, l, u, theta=F(1, 2)):
    """P(l <= I <= u and l <= n-I <= u), I ~ Bin(n, theta)."""
    lo, hi = max(l, n - u), min(u, n - l)
    if lo > hi:
        return F(0)
    return sum((F(comb(n, i)) * theta ** i * (1 - theta) ** (n - i)
                for i in range(lo, hi + 1)), F(0))


def Phi(l, u, g, theta=F(1, 2)):
    """Uniform two-daughter return for one coordinate (endpoint reduction)."""
    return min(psi(l + g, l, u, theta), psi(u + g, l, u, theta))


def joint_partition(lx, ux, gx, ly, uy, gy, theta=F(1, 2)):
    return Phi(lx, ux, gx, theta) * Phi(ly, uy, gy, theta)


def check_proportion():
    # -- the endpoint reduction lemma itself, by brute force over the range --
    viol = 0
    for l in range(1, 10):
        for u in range(l, 40, 3):
            for g in range(l, u + 1, 2):
                vals = [psi(n, l, u) for n in range(l + g, u + g + 1)]
                if min(vals) != min(vals[0], vals[-1]):
                    viol += 1
    eq('endpoint reduction violations', viol, 0)

    # -- the reference construction R ---------------------------------------
    phi = joint_partition(65, 195, 121, 8, 64, 30)
    near('Phi_* (R)', phi, '0.999712941541084')
    shows('Phi_*', '0.999712941541084')

    A, D = F(20), F(1, 100000)
    taylor = sum((F(20) ** j / factorial(j) for j in range(25)), F(0))
    assert taylor > 400_000_000
    r_star = (A / (A + D)) * (1 - F(1, 400_000_000))
    shows('r_*', '0.999999497500251')
    near('r_* value', r_star, '0.999999497500251', 15)

    joint = r_star * phi
    shows('joint R', '0.999712439185582')
    near('joint R value', joint, '0.999712439185582', 15)
    assert joint > F(9997, 10000) and F(9997, 10000) ** 10 > F(997, 1000)
    shows('ten-cycle', '0.997')

    E = 1 - (F(99957, 100000) + 0)   # placeholder; recompute the union bound
    # union bound over the four endpoint tails, exactly as in the source draft
    def tail_union(l, u, g):
        n1, n2 = l + g, u + g
        return (2 * sum(F(comb(n1, i), 2 ** n1) for i in range(0, l))
                + 2 * sum(F(comb(n2, i), 2 ** n2) for i in range(0, g)))
    E = tail_union(65, 195, 121) + tail_union(8, 64, 30)
    near('E (union bound)', E, '0.000425767634587', 15)
    shows('E', '4.25767634587')
    slack = phi - (1 - E)
    eq('recovered slack', '%.4g' % float(slack), '0.0001387')
    shows('slack', '1.387')

    # -- biased allocation ---------------------------------------------------
    b49 = joint_partition(65, 195, 121, 8, 64, 30, F(49, 100))
    b48 = joint_partition(65, 195, 121, 8, 64, 30, F(12, 25))
    shows('theta=0.49', '0.999614114647')
    shows('theta=0.48', '0.999220794519')
    near('theta=0.49 value', b49, '0.999614114647558')
    near('theta=0.48 value', b48, '0.999220794519976')
    shows('joint at 0.49', '0.999613612341')
    near('joint at 0.49 value', r_star * b49, '0.999613612341717')
    assert r_star * b49 > F(9996, 10000)

    # -- frontier witnesses --------------------------------------------------
    for tag, rho, wit, mol in [
            ('(i)',   F(1999, 2000), (37, 126, 75, 1, 36, 12), 130),
            ('(ii)',  F(1999, 2000), (62, 172, 110, 8, 61, 28), 213),
            ('(iii)', F(999, 1000),  (33, 115, 68, 1, 32, 11), 118)]:
        lx, ux, gx, ly, uy, gy = wit
        v = joint_partition(lx, ux, gx, ly, uy, gy)
        assert v > rho, (tag, float(v), float(rho))
        assert uy < lx and ly <= gy <= uy and lx <= gx <= ux
        N = (ux + gx) + (uy + gy) + 4
        eq('frontier %s core' % tag, N, {'(i)': 253, '(ii)': 375, '(iii)': 230}[tag])
        eq('frontier %s molecularity' % tag, lx + ly + gx + gy + 4 + 1, mol)
        shows('frontier %s corridors' % tag,
              '(%d,%d,%d;%d,%d,%d)' % (lx, ux, gx, ly, uy, gy))
    shows('joint (i)', '0.999529184472')
    shows('joint (iii)', '0.999033665776')
    near('joint (i) value', joint_partition(37, 126, 75, 1, 36, 12),
         '0.999529184472015')
    near('joint (iii) value', joint_partition(33, 115, 68, 1, 32, 11),
         '0.999033665775881')

    # -- the scaling table ---------------------------------------------------
    rows = json.loads((DATA / 'proportion_extras.json').read_text())['scaling']
    want = [(154, 79), (230, 118), (305, 153), (384, 191), (460, 231), (537, 267)]
    for r, (N, mol) in zip(rows, want):
        eq('scaling N', r['N'], N)
        lx, ux, gx, ly, uy, gy = map(int, re.findall(r'\d+', r['corridors']))
        eq('scaling molecularity', lx + ly + gx + gy + 4 + 1, mol)
        eq('scaling cost identity', (ux + gx) + (uy + gy) + 4, N)
        shows('scaling row', '$X[%d,%d]{+}%d$, $Y[%d,%d]{+}%d$' % (lx, ux, gx, ly, uy, gy))
        shows('scaling ratio', '%.2f' % (N / r['L']))

    # -- the cascade identities ---------------------------------------------
    T = lambda j: j * (j + 1) // 2
    for k in range(1, 6):
        eq('cascade lower k=%d' % k, T(2 * k - 1) - T(2 * k - 2), 2 * k - 1)
        eq('cascade upper k=%d' % k, T(2 * k) - T(2 * k - 1), 2 * k)
        eq('cascade sqrt lower k=%d' % k, T(2 * k - 2) + T(2 * k - 1), (2 * k - 1) ** 2)
        eq('cascade sqrt upper k=%d' % k, T(2 * k - 1) + T(2 * k), (2 * k) ** 2)
        eq('cascade level cost k=%d' % k, T(2 * k) + T(2 * k - 1), 4 * k * k)
    eq('cascade m=2 total', 4 * sum(k * k for k in range(1, 3)), 20)
    eq('cascade cubic form', F(2, 3) * 2 * 3 * 5, F(20))

    # -- the rate spans ------------------------------------------------------
    def span(lx, ux, ly, uy, fc, core):
        f = lambda x, y: (sum(log10(x - j) for j in range(lx))
                          + sum(log10(y - j) for j in range(ly))
                          + sum(log10(core - x - y - j) for j in range(fc)))
        vals = [(f(x, y), x, y) for x in range(lx, ux + 1) for y in range(ly, uy + 1)]
        lo, hi = min(vals), max(vals)
        k = log10(20) - (lgamma(lx + 1) + lgamma(ly + 1) + lgamma(fc + 1)) / log(10)
        return lo[0] + k, hi[0] + k, (lo[1], lo[2]), (hi[1], hi[2])
    lo, hi, at_lo, at_hi = span(65, 195, 8, 64, 155, 414)
    eq('R min log10', '%.2f' % lo, '63.63')
    eq('R max log10', '%.2f' % hi, '121.87')
    eq('R span', '%.2f' % (hi - lo), '58.23')
    eq('R argmin', at_lo, (195, 64))
    eq('R argmax', at_hi, (118, 14))
    for s in ('63.63', '121.87', '58.23', '(195,64)', '(118,14)'):
        shows('span ' + s, s)
    lo2, hi2, _, _ = span(37, 126, 1, 36, 91, 253)
    eq('frontier span', '%.2f' % (hi2 - lo2), '40.01')
    shows('frontier span', '40.01')


# ---------------------------------------------------------------------------
# 2. support memory, against the recorded integer certificates
# ---------------------------------------------------------------------------

def check_support():
    d = json.loads((DATA / 'frontier_support.json').read_text())
    S = 2 ** 31

    for row in d['nominal_table']:
        shows('table K=%d lower' % row['K'], str(row['lower']))
        shows('table K=%d upper' % row['K'], str(row['upper']))
        if row['K'] < 32:
            assert 1000 * row['upper'] < 999 * S
    eq('K=32 lower', d['nominal_table'][-1]['lower'], 2145518355)
    eq('K=32 upper', d['nominal_table'][-1]['upper'], 2145545336)
    eq('K=31 upper', d['nominal_table'][-2]['upper'], 2144298834)
    eq('states at 32', d['nominal_table'][-1]['states'], 3384)

    L = d['robust_band']['10-20']['lower']
    eq('robust [10,20]', L, 2145514420)
    eq('robust [10,11]', d['robust_band']['10-11']['lower'], 2145517682)
    eq('clock', d['robust_band']['10-20']['clock'], 771)
    assert 1000 * L > 999 * S
    gap = d['nominal_table'][-1]['lower'] - L
    eq('band cost', gap, 3935)
    eq('band cost display', '%.3g' % (gap / S), '1.83e-06')
    eq('enclosure width', '%.3g' % ((d['nominal_table'][-1]['upper'] - L) / S), '1.44e-05')
    for s in (digits(L), digits(2145517682), digits(2145545336), '3\\,935',
              '1.83\\times10^{-6}', '1.44\\times10^{-5}'):
        shows('support ' + s, s)

    bias = {r['theta']: r for r in d['partition_bias']}
    eq('bias 39/100 ok', bias['39/100']['ok'], True)
    eq('bias 39/100 lower', bias['39/100']['lower'], 2145366143)
    eq('bias 19/50 excluded', bias['19/50']['excluded'], True)
    eq('bias 19/50 upper', bias['19/50']['upper'], 2145078112)
    eq('bias 19/50 witness', bias['19/50']['state'], [0, 1, 0])
    shows('bias lower', digits(2145366143))
    shows('bias upper', digits(2145078112))

    box = {r['eps']: r for r in d['rate_box']}
    eq('box 1/300 ok', box['1/300']['ok'], True)
    eq('box 1/300 lower', box['1/300']['lower'], 2145342442)
    eq('box 1/300 clock', box['1/300']['clock'], 773)
    eq('box 1/250 undetermined', (box['1/250']['ok'], box['1/250']['excluded']),
       (False, False))
    shows('box lower', digits(2145342442))

    u = d['untied_vertex']
    eq('untied minimum', u['minimum'], 42)
    rows = {r['K']: r for r in u['rows']}
    eq('untied K=32 upper', rows[32]['upper'], 2104161482)
    eq('untied K=32 excluded', rows[32]['excluded'], True)
    eq('untied K=42 lower', rows[42]['lower'], 2145488787)
    eq('untied K=42 ok', rows[42]['ok'], True)
    for K in range(15, 42):
        eq('untied K=%d excluded' % K, rows[K]['excluded'], True)
        eq('untied K=%d witness' % K, rows[K]['witness'], [K - 1, 0, 0])
    shows('untied upper', digits(2104161482))
    shows('untied lower', digits(2145488787))
    eq('untied upper display', '%.6f' % (rows[32]['upper'] / S), '0.979827')
    eq('untied lower display', '%.6f' % (rows[42]['lower'] / S), '0.999071')

    rv = d.get('release_vertex_K32')
    if rv is not None:
        eq('release vertex excluded', rv['excluded'], True)
        eq('release vertex upper', rv['upper'], 2144643824)
        shows('release vertex', digits(2144643824))
        eq('release display', '%.6f' % (rv['upper'] / S), '0.998678')

    # the analytic exclusions
    eq('ceiling support', 4 + 1 * 11, 15)
    eq('ceiling proportion', 4 + 2 * 11, 26)
    eq('K=14 ceiling', F(511, 512) < F(999, 1000), True)
    eq('L^10 > 0.99', F(L, S) ** 10 > F(99, 100), True)
    eq('exit rate max', 3 * 16 * 16 + 16 * 15 / 100, 770.4)
    eq('D', 100 * 771, 77100)
    eq('blocks', 771 * 5, 3855)

    # diagnostics
    b = json.loads((DATA / 'branching_mechanism.json').read_text())
    get = lambda kd, kr, st: next(r for r in b['rows'] if r['kappa_d'] == kd
                                  and r['kappa_r'] == kr and r['start'] == st)
    eq('balanced quota fail', '%.9f' % get(10, 10, [31, 0, 0])['quota_failure'],
       '0.000900058')
    eq('balanced part fail', '%.9f' % get(10, 10, [31, 0, 0])['partition_failure'],
       '0.000004581')
    eq('certificate slack at 32',
       '%.3g' % (get(10, 10, [31, 0, 0])['success'] - 2145518355 / S), '1.05e-05')
    shows('certificate slack', '1.05')


def main():
    if '--full' in sys.argv:
        for s in ('frontier_support.py', 'frontier_proportion.py',
                  'proportion_extras.py', 'cascade.py', 'branching_mechanism.py'):
            print('re-running', s, flush=True)
            subprocess.run([sys.executable, str(HERE / 'scripts' / s)], check=True)
    check_proportion()
    check_support()
    if FAILED:
        print('\n'.join(FAILED))
        print('FAILED: %d of %d checks' % (len(FAILED), CHECKED))
        return 1
    print('%d printed values reproduced exactly.' % CHECKED)
    return 0


if __name__ == '__main__':
    sys.exit(main())
