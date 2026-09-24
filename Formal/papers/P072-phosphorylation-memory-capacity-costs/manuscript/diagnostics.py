"""High-precision floating-point DIAGNOSTICS for the final three-site source.

These numbers illustrate the discussion in Section 8; they are not certificates and
no theorem depends on them.  Output: data/diagnostics.json.
Dependencies: sympy, mpmath.
"""
import json
from fractions import Fraction as Fr
from pathlib import Path
import mpmath as mp
import sympy as sy
import check_paper as cp

mp.mp.dps = 90
HERE = Path(__file__).resolve().parent


def mpf(fr):
    return mp.mpf(fr.numerator) / fr.denominator


def main():
    _, tt = cp.tree_weights()
    iface = cp.load('postproof_candidate_interface.json')
    p, q = [Fr(x) for x in iface['p']], [Fr(x) for x in iface['q']]
    src = cp.Source(p, q, tt)
    op = cp.load('postproof_candidate_operating.json')
    clock = Fr(op['clock_rescaling'])
    assoc = max(max(r[0], r[3]) for r in src.rates)
    uni = max(max(r[1], r[2], r[4], r[5]) for r in src.rates)
    slow = max(Fr(1), assoc * cp.ST, uni / 100)
    u = cp.u
    roots = [r for r in sy.Poly(src.elim, u).nroots(n=80, maxsteps=500) if abs(sy.im(r)) < 1e-60 and sy.re(r) > 0]
    roots = sorted(mp.mpf(str(sy.re(r))) for r in roots)
    tcoef = src.tcoef
    out = []
    for z in roots:
        lv = mp.mpf(1)
        for j in range(1, 7):
            lv *= (z - j)
        tau = [mp.polyval(c, z) for c in tcoef]
        dv = sum(mpf(q[i]) * tau[b] / z for i, (a, b) in enumerate(cp.EDGES))
        ss = (10 - z) / (z * lv)
        if ss <= 0:
            continue
        f = 1 / (1 + ss * z * dv)
        e = z * f
        s = [ss * t for t in tau]
        c = [mpf(p[i]) * e * s[a] for i, (a, b) in enumerate(cp.EDGES)]
        y = [mpf(q[i]) * f * s[b] for i, (a, b) in enumerate(cp.EDGES)]
        X = s + [e, f] + c + y
        J = mp.zeros(34, 34)
        for rate, rea, nu in src.reactions():
            for k in rea:
                g = mpf(rate)
                for h in rea:
                    if h != k:
                        g *= X[h]
                for h in range(34):
                    if nu[h]:
                        J[h, k] += nu[h] * g
        Tm = mp.matrix(cp.T)
        Jc = mp.matrix(31, 31)
        full = J * Tm
        for a_, k in enumerate(cp.IX):
            for j in range(31):
                Jc[a_, j] = full[k, j]
        eig = mp.eig(Jc, left=False, right=False)
        re = sorted(mp.re(v) for v in eig)
        npos = sum(1 for v in re if v > 0)
        weakest = max(v for v in re if v < 0) if npos == 0 else None
        read = (X[7] + sum(y[i] for i, (a, b) in enumerate(cp.EDGES) if b == 7)) / cp.ST
        out.append(dict(u=mp.nstr(z, 12), unstable_eigenvalues=npos, max_real_part_raw_clock=mp.nstr(re[-1], 8),
                        weakest_decay_physical_per_s=(mp.nstr(-weakest / mpf(slow), 6) if weakest is not None else None),
                        normalized_readout=mp.nstr(read, 8), free_substrate_fraction=mp.nstr(sum(s) / cp.ST, 8),
                        free_kinase_fraction=mp.nstr(e / 10, 6), free_phosphatase_fraction=mp.nstr(f, 6)))
    labels = op['labels']
    cert = []
    for lab in labels:
        lam = Fr(lab['lambda_'])                      # in the scaled clock (raw rates / clock)
        lam_phys = lam * clock / slow
        cert.append(dict(index=lab['index'], certified_rate_physical_per_s=float(lam_phys),
                         log10_metric_condition_bound=float(mp.log10(mpf(Fr(lab['pmax']) / Fr(lab['pmin'])))),
                         log10_radius=float(mp.log10(mpf(Fr(lab['radius']))))))
    sinks = [o for o in out if o['unstable_eigenvalues'] == 0]
    for o, c_ in zip(sinks, cert):
        c_['intrinsic_over_certified_rate'] = float(mp.mpf(o['weakest_decay_physical_per_s']) / c_['certified_rate_physical_per_s'])
    res = dict(note='floating-point diagnostics at 90 digits; not certificates', slowdown=float(slow), equilibria=out, certificates=cert)
    (HERE / 'data' / 'diagnostics.json').write_text(json.dumps(res, indent=1))
    print(json.dumps(res, indent=1))


if __name__ == '__main__':
    main()
