"""Generate every exact certificate reported in Section 7 of the paper.

Candidate vectors are proposed in floating arithmetic; every inequality that
enters a proof is then verified with `fractions.Fraction` against a source
matrix reconstructed from the chemistry, the binomial allocation law and the
death rule (see site_source.py).  Output: ../data/site_certificates.json.

    python make_certificates.py
"""
from fractions import Fraction as F
import json, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from site_source import (states_of, chem_generator, pair_law, death_vector,
                         mean_matrix, phi, mv, subcritical)

ELO = F(1, 100)           # baseline intrinsic erasure
NMAX = 8
DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')

_CACHE = {}


def pieces(N, e):
    """Float views of the field at erasure e, for candidate search only."""
    key = (N, e)
    if key not in _CACHE:
        st, idx, Q = chem_generator(N, e)
        n = len(st)
        Qf = np.array([[float(x) for x in row] for row in Q])
        df = np.array([float(x) for x in death_vector(N)])
        I, J, K, P = [], [], [], []
        for i, terms in enumerate(pair_law(N)):
            for j, k, p in terms:
                I.append(i); J.append(j); K.append(k); P.append(float(p))
        _CACHE[key] = (st, Qf, df, n,
                       (np.array(I), np.array(J), np.array(K), np.array(P)))
    return _CACHE[key]


def phi_f(x, Qf, df, n, arrs, b=0.1):
    I, J, K, P = arrs
    dx = np.zeros(n)
    np.add.at(dx, I, P * x[J] * x[K])
    return Qf @ x + df * (1 - x) + b * (dx - x)


def jac_f(x, Qf, df, n, arrs, b=0.1):
    I, J, K, P = arrs
    Jm = Qf.copy()
    Jm[np.arange(n), np.arange(n)] -= df + b
    G = np.zeros((n, n))
    np.add.at(G, (I, J), P * x[K])
    np.add.at(G, (I, K), P * x[J])
    return Jm + b * G


# ------------------------------------------------ critical erasure brackets
def threshold_bracket(N, den=10 ** 6):
    lo, hi = 0, 2 * den
    assert not subcritical(N, F(lo, den)) and subcritical(N, F(hi, den))
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if subcritical(N, F(mid, den)):
            hi = mid
        else:
            lo = mid
    return F(lo, den), F(hi, den)


# ------------------------------------------------- Perron weight utilities
def perron(N, e, **kw):
    st, A = mean_matrix(N, e, **kw)
    n = len(st)
    Af = np.array([[float(v) for v in row] for row in A])
    w = np.ones(n)
    shift = 1.0 + np.abs(np.diag(Af)).max()
    for _ in range(200000):
        w = (Af + shift * np.eye(n)) @ w
        w /= w.sum()
    return st, A, w


def cw_bracket(N, e, den=10 ** 6, **kw):
    """Two-sided Collatz-Wielandt bracket for s(A_e) from a rational witness."""
    st, A, w = perron(N, e, **kw)
    wq = [F(max(int(round(v / w.min() * den)), 1), den) for v in w]
    Aw = mv(A, wq)
    lo = min(Aw[i] / wq[i] for i in range(len(wq)))
    hi = max(Aw[i] / wq[i] for i in range(len(wq)))
    return wq, lo, hi


def contraction(N, e, dens=(10 ** 6, 10 ** 8, 10 ** 10)):
    st, A, w = perron(N, e)
    for den in dens:
        wq = [F(max(int(round(v / w.min() * den)), 1), den) for v in w]
        Aw = mv(A, wq)
        g = min(-Aw[i] / wq[i] for i in range(len(wq)))
        if g <= 0:
            continue
        gamma = F(int(np.floor(float(g) * 10 ** 6)), 10 ** 6)
        if gamma <= 0:
            continue
        assert all(Aw[i] <= -gamma * wq[i] for i in range(len(wq)))
        return st, wq, gamma, wq[st.index((N, 0))] / min(wq)
    return None


# ----------------------------------------------------- amplitude floors
def hjb(N, ehi, iters=200000, h=0.04):
    """Least fixed point of the componentwise max of the two fields."""
    plo, phh = pieces(N, ELO), pieces(N, ehi)
    x = np.zeros(plo[3])
    for _ in range(iters):
        x = np.clip(x + h * np.maximum(phi_f(x, *plo[1:]), phi_f(x, *phh[1:])), 0, 1)
    act = phi_f(x, *phh[1:]) >= phi_f(x, *plo[1:])
    for _ in range(60):
        r = np.where(act, phi_f(x, *phh[1:]), phi_f(x, *plo[1:]))
        Jm = np.where(act[:, None], jac_f(x, *phh[1:]), jac_f(x, *plo[1:]))
        try:
            x = np.clip(x - np.linalg.solve(Jm, r), 0.0, 1.0)
        except np.linalg.LinAlgError:
            break
    return plo[0], x


def amplitude_floor(N, ehi, shrink=0.99, dens=(10 ** 8, 10 ** 10, 10 ** 12)):
    st, x = hjb(N, ehi)
    if x.max() >= 1 - 1e-12:
        return None
    h = 1.0 - x
    for den in dens:
        q = [1 - F(int(np.floor(v * shrink * den)), den) for v in h]
        if max(q) >= 1 or min(q) <= 0:
            continue
        hi, lo = phi(N, ehi, q), phi(N, ELO, q)
        if max(hi) <= 0 and max(lo) <= 0:
            return st, q, max(hi), max(lo)
    return None


# ------------------------------------------------ baseline exposure floors
def baseline_extinction(N):
    p = pieces(N, ELO)
    x = np.zeros(p[3])
    for _ in range(20000):
        x = np.clip(x + 0.05 * phi_f(x, *p[1:]), 0, 1)
    for _ in range(80):
        try:
            x = np.clip(x - np.linalg.solve(jac_f(x, *p[1:]), phi_f(x, *p[1:])), 0, 1)
        except np.linalg.LinAlgError:
            break
    return p[0], x


def exposure_floor(N, shrink=0.999, dens=(10 ** 10, 10 ** 12, 10 ** 14)):
    st, x = baseline_extinction(N)
    n = len(st)
    _, _, Q1 = chem_generator(N, ELO)
    _, _, Q2 = chem_generator(N, ELO + 1)
    R = [[Q2[i][j] - Q1[i][j] for j in range(n)] for i in range(n)]
    h = 1.0 - x
    for den in dens:
        q = [1 - F(int(np.floor(v * shrink * den)), den) for v in h]
        if max(q) >= 1 or min(q) <= 0 or max(phi(N, ELO, q)) > 0:
            continue
        Rq = mv(R, q)
        cmin = max(Rq[i] / (1 - q[i]) for i in range(n))
        c = F(int(np.ceil(float(cmin) * 10 ** 6)), 10 ** 6)
        assert all(Rq[i] <= c * (1 - q[i]) for i in range(n))
        return st, q, c, max(phi(N, ELO, q))
    return None


# ------------------------------------------- added-death actuator threshold
def kappa_bracket(N, e, den=10 ** 6):
    lo, hi = 0, 2 * den
    if subcritical(N, e, kappa=F(lo, den)):
        return None
    assert subcritical(N, e, kappa=F(hi, den))
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if subcritical(N, e, kappa=F(mid, den)):
            hi = mid
        else:
            lo = mid
    return F(lo, den), F(hi, den)


def main():
    t0 = time.time()
    data = {'source': 'inherited-mark N-site branching source: b=1/10, '
                      'd=1/100 on a>r and 3/10 otherwise, e=1/100+v',
            'baseline_erasure': str(ELO)}

    sites = {}
    print('N  states  e_c bracket                gamma(e=1/2)  C(e=1/2)')
    for N in range(2, NMAX + 1):
        lo, hi = threshold_bracket(N)
        wlo, l1, u1 = cw_bracket(N, lo)
        whi, l2, u2 = cw_bracket(N, hi)
        st, wq, gamma, Ccap = contraction(N, F(1, 2))
        sites[N] = {
            'states': len(states_of(N)),
            'ec_lower': str(lo), 'ec_upper': str(hi),
            'cw_at_lower': [str(l1), str(u1)], 'cw_at_upper': [str(l2), str(u2)],
            'witness_lower': [str(v) for v in wlo],
            'witness_upper': [str(v) for v in whi],
            'gamma_half': str(gamma), 'C_half': str(Ccap),
            'w_half': [str(v) for v in wq]}
        print(f'{N}  {len(states_of(N)):5d}  ({float(lo):.6f},{float(hi):.6f})   '
              f'{float(gamma):.6f}      {float(Ccap):.4f}', flush=True)
    data['sites'] = sites

    print('\nspectral brackets at e = 3/10')
    sp = {}
    ROUND = {4: (F(-7, 500), F(-139, 10000)), 6: (F(239, 10000), F(3, 125))}
    for N in range(2, NMAX + 1):
        w, lo, hi = cw_bracket(N, F(3, 10), den=10 ** 6)
        if N in ROUND:                       # brackets displayed in the paper
            assert ROUND[N][0] <= lo and hi <= ROUND[N][1], N
        sp[N] = {'lower': str(lo), 'upper': str(hi),
                 'rounded_display': [str(x) for x in ROUND[N]] if N in ROUND else None,
                 'witness': [str(v) for v in w]}
        print(f' N={N}: s(A_.3) in [{float(lo):+.6f},{float(hi):+.6f}]', flush=True)
    data['spectral_at_three_tenths'] = sp

    print('\nbaseline exposure certificates')
    exp = {}
    for N in range(2, NMAX + 1):
        st, q, c, slack = exposure_floor(N)
        top = st.index((N, 0))
        eta = 1 - q[top]
        import math
        Bnec = math.log(float(eta) / 0.01) / float(c)
        exp[N] = {'q': [str(v) for v in q], 'c': str(c), 'eta_top': str(eta),
                  'max_phi_slack': str(slack),
                  'B_nec_1_0.01': f'{Bnec:.6f}',
                  'states': [list(s) for s in st]}
        print(f' N={N}  eta={float(eta):.8f}  c={float(c):.6f}  '
              f'B_nec(1,.01)={Bnec:.6f}', flush=True)
    data['exposure'] = exp

    print('\namplitude floors')
    amp = {}
    for N, ehi in [(2, F(3, 100)), (2, F(6, 100)), (2, F(9, 100)),
                   (5, F(3, 10)), (6, F(3, 10)), (7, F(3, 10)), (8, F(3, 10)),
                   (6, F(35, 100))]:
        res = amplitude_floor(N, ehi)
        if res is None:
            print(f' N={N} e={ehi}: none'); continue
        st, q, shi, slo = res
        top = st.index((N, 0))
        amp[f'N{N}_vmax{ehi - ELO}'] = {
            'N': N, 'e_hi': str(ehi), 'v_max': str(ehi - ELO),
            'q': [str(v) for v in q], 'eta_top': str(1 - q[top]),
            'one_minus_max_q': str(1 - max(q)),
            'max_slack_baseline': str(slo), 'max_slack_vmax': str(shi),
            'states': [list(s) for s in st]}
        print(f' N={N} v={float(ehi - ELO):.2f}  eta={float(1 - q[top]):.8f}  '
              f'1-max q={float(1 - max(q)):.8f}  slacks '
              f'{float(slo):.2e}/{float(shi):.2e}', flush=True)
    data['amplitude'] = amp

    print('\nadded-death thresholds')
    kap = {}
    for N in range(2, NMAX + 1):
        for e, tag in [(ELO, 'no_eraser'), (F(3, 10), 'eraser_at_.3')]:
            br = kappa_bracket(N, e)
            if br is None:
                print(f' N={N} {tag}: already subcritical'); continue
            kap[f'N{N}_{tag}'] = [str(br[0]), str(br[1])]
            print(f' N={N} {tag}: kappa_c in '
                  f'({float(br[0]):.6f},{float(br[1]):.6f})', flush=True)
    data['added_death'] = kap

    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, 'site_certificates.json'), 'w') as f:
        json.dump(data, f, indent=1)
    print(f'\nwrote data/site_certificates.json in {time.time() - t0:.1f}s')


if __name__ == '__main__':
    main()
