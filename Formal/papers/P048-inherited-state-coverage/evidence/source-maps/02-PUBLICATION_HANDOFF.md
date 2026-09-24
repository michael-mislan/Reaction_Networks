# Publication handoff: current result and verification boundary

## Deliverable

`inherited_state_prediction.pdf` is the maintained research manuscript in the
project subfolder root. Its LaTeX source is adjacent. It contains only the final
comparison argument and the requested immediate consequences: repaired endpoint,
variance gap, independent-founder limit, worked example and bounded applicability
checks. The polynomial integral certificate is necessary to the analytic box;
historical discovery lemmas and unrelated finite-assay results are excluded.

The PDF is a conventional mathematical proof with **partial Lean verification**.
It is not a fully compiled resolution of the original goal. IC-50 remains open.
This distinction is stated on the first page and in the formal-status appendix.
The user's latest request authorized resuming the work after the earlier PI pause.

## What was completed

1. Read the attached follow-up brief in full and checked current repository state.
2. Repaired `PositiveScalarRates.lean`; strict compilation passed in 19.719 seconds.
   Removed the unnecessary tactic focus and redundant final tactic after the
   denominator identity closed. No new assumptions or dependency changes.
3. Repaired the explicit scalar distribution: generic denominator algebra,
   geometric-series normalization and coverage. The first successful strict
   receipt included declaration probes for normalization and coverage.
   The sharper `scalar_coverage_sharp` theorem also passed strict verification:
   explicit weight coverage is at least 332/343. The final audit binds both
   declaration probes and the complete source closure to the current files.
4. Supplied conventional proofs of the actual first-moment identity using a
   Yule embedding and dominated localization, and of the scalar process law
   using a bounded backward test and stopped finite-state identities.
5. Proved in the manuscript the exact no-switch-history repair, minimality among
   [0,k] intervals, variance gap and independent-founder quantile limit.
6. Independently evaluated the two-type law and backward PGFs, checked two
   population caps, reproduced exact rational constants, tested a bounded set of
   perturbations and retained a successful source-linked reference control.
7. Built a ten-page LaTeX manuscript with three vector figures and reproducible
   source, data and build commands. Layout checks and final audit are recorded
   separately; no PDF package or Lean dependency changes were made.

## Results and what they mean

- Exact scalar tail bound: 11/343; therefore scalar coverage >=332/343.
- Exact actual-tail lower bound from seven histories: 0.050441409293... .
- Exact actual coverage repair: 467880212635/481696324816 >0.9713 for [0,3].
- Actual variance lower bound >4/5; scalar variance upper bound 11/16.
- Independent-founder central scalar-interval coverage has an asymptotic upper
  bound approximately 0.930773. This is not a finite-founder uniform bound.
- Numerical one-founder actual coverage: 0.947597718 for [0,2] and 0.973827122
  for [0,3]; scalar [0,2] coverage 0.976760615.
- Numerical many-founder limit: 0.848799756; at 100 founders, 0.851145704.
- Reference preparation: actual coverage 0.953216498 for scalar interval [3,24].

The witness is a synthetic persistent-state preparation. Its switching waiting
times are 1,000 and 100,000 days, not an empirical calibration. Adding sensitive
birth and resistant death at 0.001/day retains undercoverage numerically; at
0.01/day this particular undercoverage disappears. Increasing switching changes
the interval endpoints and also removes this particular failure in the sampled
settings. These are applicability boundaries, not discarded counterexamples.

## Numerical verification and resource use

Canonical Python entry check and `smoke_numerics.py` passed. Native numerical
threads were capped at one. The complete small campaign took about 1.3 seconds
of script runtime on its first run, under a 120-second process guard. Rebuilds
were separately guarded. No brute-force population sweep was launched.

At cap32 the baseline overflow was 4.8429e-11; cap48 reduced it to 7.3778e-16.
The selected coverages changed by less than 3e-15. Independent backward-PGF
comparisons at three arguments had discrepancies below 3.7e-13. The capped
first-moment gap fell from 1.65e-9 to 6.34e-14; the second-moment gap fell from
5.61e-8 to 1.75e-12. These diagnostics support the proposed moment bridge but
are not a formal substitute for localization and integrability.

The numerical evaluator preserves overflow and checks normalization. It does
not certify floating-point roundoff. Source-linked control calculations are
explicitly narrower than reproducing the full source paper or external simulator.

## Attempt ledger and lessons

- Initial scalar-law errors were rational normalization failures, not mathematical
  counterexamples. `field_simp only` is not valid syntax in this pinned version;
  that attempted edit was rejected and removed.
- Generic algebra still needed an explicit name for the denominator before
  clearing it; normalization otherwise left inverses of rearranged expressions.
- Rewriting the concrete HasSum expression using a large closed ODE/integral
  constant caused repeated 120-second timeouts. Reducing the heartbeat limit
  did not cure it. Substituting an explicit equality with `Eq.rec` notation
  (`equality ▸ proof`) avoided the expensive rewrite traversal.
- Direct geometric-tail algebra replaced the unnecessary three-PGF specialization
  route for the explicit distribution. The public coverage theorem was retained.
- An early scratch Python read failed under Windows CP1252; repository text is
  UTF-8, and subsequent file operations used explicit UTF-8 or apply_patch.
- PDF layout initially had long-path overfull boxes and delayed figures. Path
  wrapping and an explicit float boundary before Discussion fixed these.
- Rounded lower bounds must round downward: the repair table uses >=0.971317,
  not the invalid upward-rounded >=0.971318.

## Remaining exact obligations

1. In Lean, identify the actual chronological source law's coordinate expectations
   with `constructedMoments`. The written Yule/localization proof is in Section
   3.1. A mere nonexplosion theorem or another ODE solution does not imply this.
2. In Lean, construct/dock the actual time-inhomogeneous scalar birth-death law
   and prove the bounded-backward-test expectation identity from Section 3.2.
   Compiled rate derivatives and a normalized explicit distribution do not imply
   process identity by themselves.
3. Assemble the source-level mean-matched comparison, then transport the repair
   and second-moment history inequalities to that same process in Lean. The CLT
   consequence has a written proof and is not a prerequisite for formal root closure.

No named open conjecture was identified; no novelty priority or empirical
validation is claimed. No graph node is closed from this manuscript or numerical
audit. No generated evidence was staged or committed.

## AGC assessment

Required read-only checkpoints were run on entry, after failure/structure changes
and at handoff. They consistently reported CURRENT content with an unbound
authored route. Their selected next step referred to already closed trajectory
projection. AGC helped with freshness/scope discipline but did not help choose
the missing mathematical bridge. No AGC interface repair campaign was started.

Next mathematical action: prove actual chronological trajectory coordinate
expectations equal `constructedMoments` through dominated localization, then
identify the scalar process by the bounded backward test. Do not reopen the
compiled killed-history transport or treat another explicit-law certificate as
closing either process-identification obligation.
