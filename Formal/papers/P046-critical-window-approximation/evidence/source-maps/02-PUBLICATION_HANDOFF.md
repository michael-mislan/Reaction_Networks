# Research and publication handoff

## Delivered result

The 11-page paper **Effective approximation, low-intensity bounds, and
finite-size effects for autocatalytic emergence in reversible polymer networks**
is saved as `Effective_Approximation_and_Finite_Size_RAF_Emergence.pdf` in the
workspace root, with the same PDF in `publication/`. The LaTeX source,
bibliography, vector figures, data, build instructions, and claim map are
retained. Every page was rendered and visually inspected. Discovery logs and
nonessential companion results are outside the paper.

The original fully compiled core theorem remains unchanged. Five added modules
strictly compile: settled-channel structure, ordered actual-source histories,
the generic deterministic-support probability step, exact example arithmetic,
and the assembled publication history/arithmetic endpoints. The complete
sharper polymer counting theorem, singleton law, their finite-source composition,
and the companion regularity results have conventional proofs; their complete
Lean formalization is **not** claimed. See `CLAIM_SOURCE_MAP.md` for each boundary.

## What the final proof establishes

1. **Certified approximation.** For a computably selected seed length L,
   D_0=2, D_(r+1)=2D_r+L, the escape error is at most
   1/m+(2^(L+1)-2)(1-a^(L+1))^r. Exact rational searches select L and r;
   finite Boolean weighted sums yield sound intervals of any positive width.
   The construction is total but often computationally impractical.
2. **Sharpened low-openness behavior.** Previously used channels are settled,
   so a new productive channel cannot trigger a further cascade through them.
   This permits direct type-sum budgets T_j<=2^(j+2)+6 and Q_j<=4*2^j-j.
   The next-choice count is at most (6+2j)^2+4*2^j-j. Distinct-coordinate
   histories give S(a)<=C_r a^r<=(36a)^r 2^(r(r-1)/2). Optimizing this
   upper bound yields the coefficient 1/(2 log 2) in its negative log-square
   exponent. This is a one-sided bound, not exact asymptotics.
3. **Finite-size behavior.** Food-only channels have six singleton catalyst
   opportunities and growth gateways have seven, including their products.
   Disjoint molecule/channel witness coordinates give exactly
   1-(1-p)^248 or 1-(1-p)^234. All RAFs without these witnesses require at
   least two positive catalytic coordinates; hence the fixed-size first-order
   coefficient is exactly 248 or 234 in p. This differs from the all-powers
   flatness of the limiting profile. Both unscaled iterated limits are zero;
   their rates, rather than their values, differ.
4. **Useful finite predictions.** Combining the actual source comparison with
   history counting gives singleton lower <=P_n(p)<=C_r(M_n p)^r+G M_B p,
   B=2^(r+1), under the stated cap hypotheses. Food-only RAFs require G=36/34,
   not the growth-only counts 32/30. Each model retains its own reaction count.

## Numerical hypotheses, tests and conclusions

The complete data are in `results/postproof_checks.json`. These finite tests
guided and audited the proofs; they are not substituted for universal arguments.

| Hypothesis/test | Scale and observed result | What was learned |
|---|---|---|
| Single productive steps leave all old channels settled | Exhaustive reachable state sets at depths 0,1,2: 1,24,546 for each model; checked every next transition | No cascade counterexample; the structural closure-minimality proof is the right mechanism. |
| Total-length and cleavage-slot budgets | Max T=10,14,22 and max Q=4,7,14; split transition counts 32,1080,33462; quotient 30,1022,31970 | The type-sum bound stays small; counting every channel in the exponentially larger cap is unnecessarily loose. |
| Next-channel census | Maximum choices at these depths: split 32,46,66; quotient 30,44,63 | The proposed upper census survives the pilot; its slack is not an actual counterexample or a sharp-count claim. |
| Exact singleton witness counts | Literal n=4 model: 248 split, 234 quotient; 36/34 total and 32/30 growth gateways | Product-as-catalyst and food-only reactions materially affect finite probabilities. |
| Quotient normalization | Primitive-word formula agrees with literal channel enumeration at n=4..8; n=16 deletion contributions 112,24,24,24,30 total 214 | Quotient R_16=1,834,798, distinct from split 1,835,012. |
| Low-openness coefficient products | (a,r,upper)=(10^-3,8,10^-5), (10^-4,12,10^-15), (10^-6,18,10^-45), (10^-20,65,10^-629) | All four strict integer/rational comparisons passed Python exact arithmetic and Lean; probability implications additionally use the conventional census proof. |
| Full/retained-pool drift | Rational normalization checks n=4..100; independent conventional all-future envelope derived in companion notes | Isolated cap checks alone would not justify a tail bound; the monotone analytic envelopes do. |
| Rational parameter conversion | Ten zero/interior/near-endpoint interval pilots and three exact inverse round trips | Rational exp/log routines terminate on these inputs; the series remainder proofs establish general termination and containment. |

Both numerical scripts ran in less than one second under 90-second process
leases, using the canonical Python runtime. The figure renderer used the
same environment. No large simulation, broad certificate campaign, unleased
long search, or competing-worker interruption was used.

### Fully specified finite examples

Both use n=16, lambda=10^-4, r=2, B=8, M_n=131070 and M_B=510, with
p=16/(10000 R_16) separately in each model. The exact lower is the singleton
probability; the displayed convenient lower is its two-term Bonferroni bound.

| Quantity | Split | Quotient |
|---|---:|---:|
| R_16 | 1,835,012 | 1,834,798 |
| C_2 | 2,272 | 2,130 |
| Bonferroni lower (rounded display) | 2.1623834464e-7 | 2.0405513957e-7 |
| History upper term (rounded display) | 2.9674067067e-5 | 2.7825927643e-5 |
| Short-catalyst correction (rounded display) | 1.6008614658e-5 | 1.5121010596e-5 |
| Strict certified outer interval | (2.16e-7,4.57e-5) | (2.04e-7,4.31e-5) |

At the same lambda, the limiting profile is below 10^-15. Thus the finite
lower bound already greatly exceeds the limiting profile. This comparison
has no sampling error and makes no assertion that cap sixteen is a close
approximation to the limit. The separate finite correction remains visible.

## Failures and route changes

- The old sparse-support coefficient is valid but numerically weak. The new
  route tracks total type length; no larger exhaustive campaign was launched.
- Initial settled-history Lean edits failed through binder substitution and
  rewriting the wrong power occurrence. Explicit endpoint equalities fixed
  these elaboration issues; they were not mathematical counterexamples.
- Ordered-list distinctness initially left a disjointness goal. An explicit
  membership contradiction completed the proof and removed the warning.
- The largest arithmetic certificate initially stalled while reducing a
  large power of ten. Rational reformulation alone did not fix it. Inspection
  identified Lean's exponentiation threshold 256; a local threshold 2000
  allows the 671-exponent exact integer comparison. It now passes without
  warnings, native computation shortcuts, or new axioms.
- The support union bound first used a deprecated lemma, rejected under
  warning-as-error. The replacement `gcongr` solved the goal completely;
  removing an unnecessary following tactic resolved the second failure.
- TeX rejected `bottomrule` after the generated row-file input boundary.
  Embedding the two exact-data rows resolved it. A long appendix identifier
  overflowed until given its own two-line display. Bibliography URLs are
  printed and use ragged-right layout; the final log has no layout warnings.

These failures, their fixes and evidence are recorded in C016 onward in
`CYCLE_LEDGER.jsonl`. They do not warrant repeating the numerical pilots.

## Companion follow-ups completed outside the main paper

`COMPANION_PROOFS.md` proves strict increase by a source-valid finite forcing
event; global continuity modulus including zero; rational exponential and
logarithmic error searches; terminating inverse brackets for computable
targets; nonanalyticity without an unsupported smoothness claim; explicit
pool drift; and all-future canonical normalization for both models.
The independent-heterogeneity upper bound and the fully correlated Bernoulli
counterexample are in the main paper because they specify the history bound's
scope. No arbitrary dependent-model conclusion is inferred.

## Scores and remaining work

Final historical checklist: **48/48 PASS**. Final postproof checklist:
**24/24 PASS**. These are mixed-evidence completion scores, as labeled in
the registers. They include conventional mathematical proofs. They are not
counts of fully formalized theorems. No failed or blocked mathematical item
is hidden behind these scores.

Remaining formalization: the full actual-source T/Q census and H3, the
singleton semantics F2, their probability composition F5, and companion
parameter results. The generic history probability lemma retains its count
and coverage premises. Remaining research questions: matching small-openness
lower bounds, cheaper acquired seeds, efficient interior evaluation, and
justified dependence models. None is needed for this paper's stated results.

AGC was useful for content freshness and scope checks. New strict receipts
required proof-neutral same-cut reconciliation; no authority graph mutation,
new theorem status, or mathematical proof was supplied by that reconciliation.
The final checkpoint output is `results/agc_publication_final.txt`. The
legacy authority graph remains preserved; the local diagnostic dependency
record is `POSTPROOF_DEPENDENCIES.md`. No files were staged or committed.

## Evidence and reproduction

- `BUILD.md`: exact numerical, Lean and typesetting commands.
- `CLAIM_SOURCE_MAP.md`: claim-level formal/conventional boundaries.
- `EVIDENCE_MANIFEST.json`: hashes of new sources, receipts, manuscript and data.
- `PDF_QA.json`: final PDF identity and page inspection record.
- `verification/PublicationResolution.verify.json`: strict assembled exports.
- `verification/Resolution.verify.json`: preserved original root receipt.

The root source SHA-256 remains
`33564f5d95f46b88d547b9602d8a1c7d2db5932778208083812f50662af0a6b2`.
The unchanged mathlib manifest SHA-256 is
`a8df0b606ec258561c226df89856884be433c19b49fb0a27335d69bb2b6e9fac`.
No authorship identity or external publication status has been invented.
