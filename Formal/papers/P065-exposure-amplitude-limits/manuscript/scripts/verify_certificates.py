"""Replay, in exact rational arithmetic, every certificate quoted in the paper.

Reads ../data/site_certificates.json, reconstructs each source matrix from the
chemistry, the binomial allocation law and the death rule, and re-checks every
inequality.  Nothing floating enters a verdict.

    python verify_certificates.py
"""
from fractions import Fraction as F
import json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from site_source import (states_of, chem_generator, mean_matrix, phi, mv,
                         subcritical)

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data',
                    'site_certificates.json')
ELO = F(1, 100)
fails = []


def check(name, ok, detail=''):
    print(f'  [{"PASS" if ok else "FAIL"}] {name}{"  " + detail if detail else ""}')
    if not ok:
        fails.append(name)


def deriv_R(N):
    n = len(states_of(N))
    _, _, Q1 = chem_generator(N, ELO)
    _, _, Q2 = chem_generator(N, ELO + 1)
    return [[Q2[i][j] - Q1[i][j] for j in range(n)] for i in range(n)]


def main():
    d = json.load(open(DATA))

    print('\n--- Table 2: critical erasure brackets and contraction weights ---')
    for k, row in d['sites'].items():
        N = int(k)
        lo, hi = F(row['ec_lower']), F(row['ec_upper'])
        check(f'N={N} supercritical at e={lo}', not subcritical(N, lo))
        check(f'N={N} subcritical   at e={hi}', subcritical(N, hi))
        check(f'N={N} bracket width 1e-6', hi - lo == F(1, 10 ** 6))
        w = [F(x) for x in row['w_half']]
        g = F(row['gamma_half'])
        _, A = mean_matrix(N, F(1, 2))
        Aw = mv(A, w)
        check(f'N={N} A_(1/2) w <= -{g} w',
              all(Aw[i] <= -g * w[i] for i in range(len(w))) and min(w) > 0)
        st = states_of(N)
        check(f'N={N} C = w_(N,0)/w_min = {row["C_half"]}',
              w[st.index((N, 0))] / min(w) == F(row['C_half']))

    print('\n--- spectral brackets at e = 3/10 (Collatz-Wielandt) ---')
    for k, row in d['spectral_at_three_tenths'].items():
        N = int(k)
        w = [F(x) for x in row['witness']]
        _, A = mean_matrix(N, F(3, 10))
        Aw = mv(A, w)
        lo = min(Aw[i] / w[i] for i in range(len(w)))
        hi = max(Aw[i] / w[i] for i in range(len(w)))
        ok = lo == F(row['lower']) and hi == F(row['upper'])
        if row.get('rounded_display'):
            rl, rh = (F(x) for x in row['rounded_display'])
            ok = ok and rl <= lo and hi <= rh
        check(f'N={N} s(A_.3) in [{float(lo):+.6f},{float(hi):+.6f}]', ok,
              'supercritical' if lo > 0 else ('subcritical' if hi < 0 else ''))

    print('\n--- Table 4: baseline exposure certificates ---')
    for k, row in d['exposure'].items():
        N = int(k)
        q = [F(x) for x in row['q']]
        c = F(row['c'])
        st = states_of(N)
        check(f'N={N} Phi_base(q) <= 0',
              max(phi(N, ELO, q)) <= 0 and min(q) > 0 and max(q) < 1)
        Rq = mv(deriv_R(N), q)
        check(f'N={N} Rq <= c(1-q), c={float(c):.6f}',
              all(Rq[i] <= c * (1 - q[i]) for i in range(len(q))))
        check(f'N={N} eta_(N,0) = {row["eta_top"]}',
              1 - q[st.index((N, 0))] == F(row['eta_top']))

    print('\n--- Table 3: amplitude floors (no policy eradicates) ---')
    for k, row in d['amplitude'].items():
        N = row['N']
        ehi = F(row['e_hi'])
        q = [F(x) for x in row['q']]
        st = states_of(N)
        check(f'{k}: Phi_base(q) <= 0', max(phi(N, ELO, q)) <= 0)
        check(f'{k}: Phi_vmax(q) <= 0', max(phi(N, ehi, q)) <= 0)
        check(f'{k}: 0 < q < 1', min(q) > 0 and max(q) < 1)
        check(f'{k}: eta_(N,0) = {row["eta_top"]}',
              1 - q[st.index((N, 0))] == F(row['eta_top']))
        check(f'{k}: 1-max q = {row["one_minus_max_q"]}',
              1 - max(q) == F(row['one_minus_max_q']))

    print('\n--- added-death actuator thresholds ---')
    for k, (lo, hi) in d['added_death'].items():
        N = int(k.split('_')[0][1:])
        e = ELO if k.endswith('no_eraser') else F(3, 10)
        lo, hi = F(lo), F(hi)
        check(f'{k}: supercritical at kappa={lo}',
              not subcritical(N, e, kappa=lo))
        check(f'{k}: subcritical at kappa={hi}', subcritical(N, e, kappa=hi))
        check(f'{k}: below the proved uniform bound 9/100', hi <= F(9, 100))

    print('\n--- Proposition 7.5: uniform total-count argument ---')
    for N in range(2, 9):
        st = states_of(N)
        b, kap = F(1, 10), F(29, 100)
        rates = [b - (F(1, 100) + kap if a > r else F(3, 10)) for a, r in st]
        check(f'N={N} b - d - kappa <= -1/5 in every state at kappa=.29',
              max(rates) <= F(-1, 5))

    print('\n' + ('ALL CHECKS PASSED' if not fails
                  else f'{len(fails)} FAILURES: {fails}'))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
