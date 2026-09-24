# Publication handoff: timing information and capacity

## Delivered result

The paper is **Assay_Timing_Information_and_Capacity.pdf**, saved directly in this
problem-workspace root. Its title is *When Timing Is Insufficient: Information
Limits and Measurement Design in Stochastic Amplification Assays*. The 13-page
manuscript includes the final proofs, three vector figures, six tables, a technical
appendix, an evidence map, and verified bibliographic metadata. Author names and
affiliations were not invented. Nothing was submitted to an external publisher.

The predecessor remains **54/54 complete at its conditional mathematical scope**.
The successor is **24/24 PASS**, with a separate register in PUBLICATION_TASKS.json. The
register counts deliverables, not theorem truth or percentage formalization.

The final argument is deliberately narrower than a universal assay theory. It
establishes a concrete all-crossing-time obstruction, an assumed source-preserving
measurement repair, and distinct capacity-identification results. It does not
claim measured clinical performance, full Blackwell dominance, an optimal timing
constant, or identification of a biochemical resource.

## What the follow-up work established

1. **A quantitative decision gap.** The already verified timing miss lower bound
   0.0555 and joint miss upper bound 0.0422443 imply an advantage greater than
   0.0132557, or 1.32557 percentage points. The new DecisionGap module compiles
   this direct consequence. No optimizer or additional likelihood-ratio theorem
   is needed.
2. **A discrepancy budget.** The existing dual is stronger than its single
   operating-point corollary: miss > 0.1055 - 5 FP. The layer-cake proof for bounded
   expectations transfers it under total variation to miss > 0.0555 - 5 delta0 -
   delta1. Thus 5 delta0 + delta1 <= 0.0055 preserves exclusion. Joint margins
   tolerate eta0 <= 0.0097 and eta1 <= 0.0077557. The measure argument is printed
   as an ordinary proof; its scalar consequence is compiled. These are sufficient
   model-error budgets, not calibrated discrepancies.
3. **Source-connected fixed-rate rescue.** Each fixed state rate can vary by
   +/-2%, loading can be any lambda >= 3.99, and actual time can lie in
   [6.99,7.01]. Common-innovation holding-time comparison, connected to the
   uniformized source through finite-ODE uniqueness, reduces the errors to two
   endpoints. Exact rational uniformization establishes F < .032, M < .035,
   exp(-3.99) < .019. With the same hit-conditioned channel requirements, joint
   blank error is < .00032 and miss < .04525192. The full source comparison and
   certificates are ordinary proof plus exact computation, not a new complete
   Lean robustness theorem. The terminal scalar implication is compiled.
4. **Threshold twenty.** At R=h=20, lambda=4, the initial hit probability is about
   1.0200522e-8. Exact bounds at time eight exclude every deadline, and bounds at
   time ten certify the same conditional channel rescue as the nominal example.
   This resolves the conspicuous large initial atom of the small example without
   claiming an all-classifier obstruction at threshold twenty.
5. **Censoring-safe inference.** Genuine interval bounds imply certain-positive,
   certain-negative, and unknown categories. Event inclusion gives population
   bounds; independent category indicators and one-sided Hoeffding give finite
   sample coverage, even with nonidentical censoring. Independence of censoring
   from latent waits is unnecessary. Independence across reaction observations
   remains essential. The implementation returns finite intervals, lower bounds,
   unresolved information, or model incompatibility after physical-domain
   intersection. It also propagates an interval for the known-shape parameter.
6. **Coarse blocks.** For calibrated ordered blocks, later-state holding-time
   multipliers decrease faster as capacity increases. Expanding a cross product
   gives a sum of positive terms and proves pathwise strict ratio ordering.
   Event inclusion supplies nonstrict probability monotonicity. A full ordinary
   source-connected proof is included; BlockRatio compiles its positive-term and
   ratio algebra. Unique probabilistic inversion is not asserted.
7. **Large-capacity interpretation.** Exact formulas show a 1/R departure from
   the unlimited-capacity limit and 1/R^2 local sensitivity to absolute capacity.
   Reporting depletion strength 1/R remains useful when upper capacity is
   unbounded. Exact endpoint differences give sufficient sample sizes; these
   are not minimax lower bounds. The paper carefully distinguishes placing an
   inverted point estimate in a target bracket from containing an entire
   confidence interval in that bracket (the latter sufficient construction
   needs half the tolerance and four times the sample bound).

## Tests, assumptions, and outcomes

The canonical Python entry check and numerical smoke suite passed. No dependency
updates, unbounded numerical search, large certificate replay, or Monte Carlo
rare-event campaign was used. Numerical reproduction used a 180-second process
lease and completed comfortably within it, with native thread counts capped at
one in the main numerical script.

| Test | Assumptions/settings | Outcome and lesson |
|---|---|---|
| Source adoption | Main source hash and all 34 imported source hashes compared to strict receipt | Exact matches; unchanged compiled root adopted without claiming a new root rebuild |
| Robust rescue | Exact fractions; L=200; fast and slow endpoint times; load 3.99 | All assertions pass; source uncertainty leaves a useful margin |
| Threshold twenty | Exact fractions; L=300; times 8 and 10 | All-deadline exclusion and conditional measurement rescue pass |
| Published sign certificate | Spectral coefficients reconstructed from rational source rates, exp(-4) enclosed, five outward coefficient intervals | One right-tail and four early-region checks pass exactly; figures are not relied on for signs |
| Nominal source margins | Exact uniformization at times 4,5,7 | F(4)>.0073, M(5)>.069 and all three rescue bounds pass |
| Completed-only regression | Retained original cohort D2+D4<=1; clocks .4,1,3 | Full p=.45516304; selected .49108751,.47980287,.45986432; deletion restores clock dependence |
| Block probability | Four-dimensional rational phase-type solves, R=6,7,10,20,100 | Decreasing values agree with theorem; R=7 exactly 111503293/331058412 |
| Confidence-set illustration | Seed 20260916; 4000 independent reactions per case; known a=.01; separate dwell horizons and frame brackets | R=7 resolved: [6.745,8.715]; short follow-up: [4.175,infinity); R=100: [15.167,infinity) |
| Physical-domain behavior | Explicit finite, unbounded, whole-domain and impossible probability inputs | All four output classes pass; no hidden clamping |
| Decision bands | Explicit usable, excluded, unresolved enclosures | All three labels pass with their proper inequalities |
| Sample design | Exact p(R) endpoint differences, 10% relative brackets, delta=.05 | Sufficient point-estimate n=4883,225627,9911503 for R=7,20,100 |
| Zero-error calibration | Prespecified independent Bernoulli rule, one-sided tail .025 | Counts 368,72,12295 reproduced for limits .01,.05,.0003 |
| Lean extensions | Warnings treated as errors | DecisionGap and BlockRatio verified, zero stdout/stderr; standard axioms only |
| PDF production | Full build command, bibliography passes, text extraction, all-page overview and dense-page inspection | 13 pages; no undefined references/citations or overfull/underfull layout warnings in final log |

All counts and intervals above are mathematical or simulated. None is biological
validation. The simulation's separate dwell horizons are deliberately distinguished
from the completed-only sum-of-waits regression.

## Failures and corrections retained outside the paper

- The first DecisionGap strict compile rejected an unused `he0` hypothesis. Removing
  it fixed the implementation; the statement and proof route were not refuted.
  The failed receipt remains available. Successful compilation took about 65 seconds.
- The first manuscript patch was rejected because it attempted both deletion and
  addition of the same path in one patch. No manuscript content was changed by that
  rejected operation; an ordinary update succeeded.
- The optional PyMuPDF renderer was absent from the canonical environment. Rendering
  used installed Poppler and Pillow instead, without changing the locked runtime.
- The review's unsuccessful guessed F20(12)<.045 bound remains a recorded failed
  sufficient bound. It was not rerun: time ten already closes the required example.
- Predecessor failed single-tail and coarse polynomial bounds remain in the old
  ledger. They are not included as scientific results in the paper.

## Literature and formal scope

The Rolando primary paper was accessed through the laboratory's PDF. Publisher/
primary records and Crossref registration metadata verify the four bibliography
entries (saved in publication/data/bibliography_metadata.json). A focused search
also found the 2016 Bokkasam--Ott information-limited oligonucleotide assay paper;
its affinity/sequence-information setting is distinct from this finite-source
crossing-time certificate. It is not used to support a mathematical claim or a
claim of priority. The paper makes a scoped contribution statement rather than
claiming no related literature exists.

General MLR formalization, a general holding-time/uniformization equivalence in
Lean, arbitrary drifting clocks, unknown-shape identification, Fisher/minimax
extensions, sharper optimum certificates, and full threshold-twenty timing
classification were not activated. They are unnecessary to the delivered critical
path. CONTRACT.md and PILOT_RESULTS.md were corrected to distinguish the already
finished concrete formal obligations from these broader conventional/open ones.

## AGC and final handoff

AGC was used at entry, after the new structure/verification attempt, after the
strict compile failure, and at the stopping gate. It required proof-neutral
same-frontier reconciliation when new receipts appeared; that was serviced using
the exact named command. AGC was useful for freshness and receipt binding, but
provided no new mathematical theorem or shortcut. Its legacy unbound advisory
cut is not treated as evidence against the completed root, nor is CURRENT treated
as proof. The final checkpoint is saved under publication/data/final_agc.yaml.

The most consequential remaining empirical question is whether a physical
identity readout has the required hit-conditioned sensitivity and false-positive
rate without invalidating the total-count source. State calibration, acquisition
duration, and the relationship of effective capacity to a consumed resource are
also unvalidated. None is silently included in the conditional theorem.

## Reproduction and deliverable paths

- `Assay_Timing_Information_and_Capacity.pdf` — delivered paper in workspace root.
- `publication/main.tex`, `supplement.tex`, `references.bib` — complete sources.
- `publication/build.ps1` — full reproduction/build entry point.
- `publication/README.md` — commands and scope.
- `publication/data/results.json`, `sign_checks.json`, `source_audit.json` — results.
- `publication/render/` — final page renders, extracted text and inspection record.
- `verification/DecisionGap.verify.json`, `BlockRatio.verify.json` — strict receipts.
- `PUBLICATION_TASKS.json`, `PUBLICATION_GRAPH.json`, `PUBLICATION_STATUS.md` — final register and graph.

No generated evidence was staged or committed by this agent. No repository-wide
build, toolchain update, or change to mathlib packages was performed.
