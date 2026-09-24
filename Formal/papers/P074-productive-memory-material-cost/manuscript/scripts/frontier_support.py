"""Exact frontier experiments for the elementary support-memory source.

Outputs (all exact integers over the denominator 2^31):

  1. the published nominal table (K = 15..32 at kappa = 10), two-sided;
  2. the robust band [10,20] certificate at K = 32;
  3. the largest certified symmetric partition-bias interval [theta, 1-theta]
     that preserves the 0.999 guarantee at K = 32 over the whole band;
  4. the largest certified simultaneous multiplicative rate-constant box;
  5. the untied-branching vertex (kappa_d, kappa_r) = (20,10): exclusion of
     K = 32 and the exact minimum budget at that vertex.

Every "fail" is backed by an exact UPPER certificate at an admitted start, so
it is a genuine failure of the specification and not certificate conservatism.
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

from ctmc_certificate import SCALE, certify, nominal_groups, payoff_biased

TARGET = F(999, 1000)
OUT = Path(__file__).resolve().parent.parent / 'data'


def passes(r):
    return 1000 * r['lower'] >= 999 * SCALE


def fails(r):
    return 1000 * r['upper'] < 999 * SCALE


def vertex_groups(kd, kr):
    return [([0], [F(1)], F(1), F(1)),
            ([1], [F(1)], F(1, 100), F(1, 100)),
            ([2], [F(1)], F(2), F(2)),
            ([5], [F(1)], F(1, 50), F(1, 50)),
            ([3], [F(1)], F(kd), F(kd)),
            ([4], [F(1)], F(kr), F(kr))]


def main():
    res = {}
    t0 = time.monotonic()

    # 1. nominal table ------------------------------------------------------
    table = []
    for K in range(15, 33):
        r = certify(K, nominal_groups(10, 10))
        table.append(dict(K=K, states=r['states'], lower=r['lower'], upper=r['upper'],
                          witness=r['upper_state']))
        print('nominal', K, r['states'], r['lower'], r['upper'], flush=True)
    res['nominal_table'] = table
    assert table[-1]['lower'] == 2145518355 and table[-1]['upper'] == 2145545336
    assert table[-2]['upper'] == 2144298834
    assert all(1000 * row['upper'] < 999 * SCALE for row in table[:-1])
    assert 1000 * table[-1]['lower'] > 999 * SCALE

    # 2. robust band --------------------------------------------------------
    rb = {}
    for lo, hi in [(10, 11), (10, 20)]:
        r = certify(32, nominal_groups(lo, hi))
        rb[f'{lo}-{hi}'] = dict(lower=r['lower'], state=r['lower_state'], clock=r['clock'])
        print('band', lo, hi, r['lower'], flush=True)
    res['robust_band'] = rb
    assert rb['10-20']['lower'] == 2145514420
    assert rb['10-11']['lower'] == 2145517682

    # 3. partition bias -----------------------------------------------------
    bias = []
    for th in ['2/5', '39/100', '19/50', '187/500', '93/250', '37/100', '7/20']:
        t = F(th)
        r = certify(32, nominal_groups(10, 20), split=payoff_biased(t))
        row = dict(theta=str(t), lower=r['lower'], upper=r['upper'],
                   ok=passes(r), excluded=fails(r), state=r['lower_state'])
        bias.append(row)
        print('bias', th, r['lower'], row['ok'], flush=True)
    res['partition_bias'] = bias

    # 4. multiplicative rate box -------------------------------------------
    box = []
    for e in ['1/1000', '1/500', '1/400', '1/300', '1/250', '1/200']:
        eps = F(e)
        r = certify(32, nominal_groups(10, 20, eps=eps))
        row = dict(eps=str(eps), lower=r['lower'], upper=r['upper'], clock=r['clock'],
                   ok=passes(r), excluded=fails(r))
        box.append(row)
        print('box', e, r['lower'], row['ok'], row['excluded'], flush=True)
    res['rate_box'] = box

    # 4b. the release-favoured vertex is also excluded at K = 32 ------------
    r = certify(32, vertex_groups(10, 20))
    res['release_vertex_K32'] = dict(kappa_d=10, kappa_r=20, lower=r['lower'],
                                     upper=r['upper'], excluded=fails(r),
                                     witness=r['upper_state'])
    print('release vertex K=32', r['lower'], r['upper'], fails(r), r['upper_state'],
          flush=True)
    assert fails(r)

    # 5. untied branching vertex -------------------------------------------
    untied = []
    K = 15
    first_pass = None
    while K <= 70:
        r = certify(K, vertex_groups(20, 10))
        row = dict(K=K, states=r['states'], lower=r['lower'], upper=r['upper'],
                   ok=passes(r), excluded=fails(r), witness=r['upper_state'],
                   seconds=r['seconds'])
        untied.append(row)
        print('untied', K, r['states'], r['lower'], r['upper'], row['ok'], row['excluded'],
              r['seconds'], flush=True)
        if row['ok'] and first_pass is None:
            first_pass = K
            break
        assert row['excluded'], f'K={K} neither certified nor excluded'
        K += 1
    res['untied_vertex'] = dict(kappa_d=20, kappa_r=10, rows=untied, minimum=first_pass)

    res['seconds'] = round(time.monotonic() - t0, 1)
    OUT.mkdir(exist_ok=True)
    (OUT / 'frontier_support.json').write_text(json.dumps(res, indent=2))
    print('TOTAL', res['seconds'], 'untied minimum', first_pass)


if __name__ == '__main__':
    sys.exit(main())
