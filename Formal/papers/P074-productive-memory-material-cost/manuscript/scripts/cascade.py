"""The corridor cascade: how material scales with the number of ordered levels.

A memory with m ordered types needs m stacked corridors
    1 <= l_1 <= u_1 < l_2 <= u_2 < ... < l_m <= u_m,
each with its own growth increment g_k, and the core mass is
    N = q + sum_k (u_k + g_k).

Balancing the four Gaussian corridor constraints level by level gives the exact
recursion l -> g -> u with l_k = T_{2k-2}, g_k = T_{2k-1}, u_k = T_{2k} in units
of z^2, where T_j = j(j+1)/2 is the j-th triangular number, because

    T_{2k-1} - T_{2k-2} = 2k-1 = sqrt(T_{2k-2} + T_{2k-1}),
    T_{2k}   - T_{2k-1} = 2k   = sqrt(T_{2k-1} + T_{2k}).

Hence per-level cost 4k^2 z^2 and total  (2/3) m(m+1)(2m+1) z^2:  cubic in m.
Relative to m = 1 the predicted totals are 1 : 5 : 14 : 30 for m = 1,2,3,4.

This script tests that prediction against exact computation.  Levels are
allocated an equal failure budget delta/m, which makes the design sufficient
(so the totals reported are exact upper bounds on the m-level frontier) and lets
each level be optimized independently by a greedy that minimizes cost first and
breaks ties towards the smallest upper endpoint.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

from frontier_proportion import coordinate_value

OUT = Path(__file__).resolve().parent.parent / 'data'


def level_min_cost(l: int, target: F, cap: int = 4000):
    """Smallest c with max_g F(l,g,c) >= target; ties broken to smallest u."""
    for c in range(2 * l, cap):
        best = None
        for g in range(l, c // 2 + 1):
            if coordinate_value(l, g, c) >= target:
                if best is None or c - g < best[1]:
                    best = (g, c - g)
        if best is not None:
            return dict(c=c, g=best[0], u=best[1], l=l)
    raise RuntimeError('cap')


def cascade(m: int, delta: F, q: int = 4):
    target = 1 - delta / m
    l, total, levels = 1, q, []
    for k in range(m):
        lev = level_min_cost(l, target)
        levels.append(lev)
        total += lev['c']
        l = lev['u'] + 1
    return dict(m=m, delta=str(delta), q=q, N=total, levels=levels)


def main():
    res = {'note': 'equal per-level budget delta/m: sufficient design, so each N '
                   'is an exact upper bound on the m-level frontier',
           'predicted_ratio': {str(m): 4 * sum(k * k for k in range(1, m + 1)) / 4
                               for m in range(1, 5)},
           'runs': []}
    for dexp in (3, 5, 7):
        delta = F(1, 10 ** dexp)
        base = None
        for m in range(1, 5):
            r = cascade(m, delta)
            if base is None:
                base = r['N'] - r['q']
            r['ratio_to_m1'] = round((r['N'] - r['q']) / base, 3)
            res['runs'].append(r)
            print('delta=1e-%d m=%d  N=%-5d ratio=%-6.3f  %s'
                  % (dexp, m, r['N'], r['ratio_to_m1'],
                     ' '.join('[%d,%d]+%d' % (x['l'], x['u'], x['g']) for x in r['levels'])),
                  flush=True)
    print('predicted ratios 1 : 5 : 14 : 30')
    OUT.mkdir(exist_ok=True)
    (OUT / 'cascade.json').write_text(json.dumps(res, indent=2))


if __name__ == '__main__':
    main()
