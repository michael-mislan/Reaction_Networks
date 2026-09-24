# Research and proof-completion handoff

**Campaign: 72/72 PASS. Root: GREEN-C/E with compiled finite subset L.
Open required mathematical nodes: none (D1–D7 closed in the stated scope).**
Score history: 0 → 55 → 64 → 68 → 72; no denominator changes. Final four
items closed after the current-hash audit, completed ledger, pre-stopping
AGC checkpoint and this standalone delivery.

## Deliverable and scope

The completed mathematical argument is MANUSCRIPT.md, **Hidden sister concordance
can reverse a treatment schedule**. It answers the attached guide's bounded
question with conventional source-level proofs, exact certificates and a strictly
compiled finite-algebra subset. It does not claim a fully formalized stochastic
theorem, a named literature conjecture solved, or an empirically calibrated
cancer treatment result. The guide itself described a new scoped research problem.

The final task register and status are TASKS.md and STATUS.md; the denominator
is unchanged at 72. Evidence types are C (conventional), E (exact), L (Lean),
N (exploratory numerical). Scientific closure and AGC publication status are
separate. This report records the mathematics; final audit metadata appears
in evidence/final_audit.json and the daily Sprint 3 entry.

## Exact result

One P divides at rate one into a symmetric S/T pair with probabilities
(1/4+c,1/4−c,1/4−c,1/4+c). Every later S/T division uses the same correlated
law, at rate ε. A kills S/T at rates (2,4), B at (3,3); both have equal declared
actuator cost. The endpoint is population survival at a finite deadline.

The complete time/event/one-daughter record from an exponentially stopped P
is identical for all c and ε. At T=log(8/7), c=−1/5 prefers B and c=1/5
prefers A, uniformly for 0≤ε≤1/1000. The certified minimum risk gap is
344660293489/2114810019840000, approximately 0.000162975.

For chronological AB versus BA with equal pulse lengths h, the extinction
difference is −4c h³ with remainder bounded by 64000h⁴, uniformly over
0≤ε≤1. Therefore at c=±1/5 and 0<h≤10⁻⁶, preferences are opposite even
though the retained observation laws are identical. This is actual sequencing
with repeated correlated inheritance. The certified short pulse is extremely
small; no larger-horizon sequencing guarantee is claimed.

Any selector using only the aliased records has worst-case error at least 1/2.
The sister-agreement bit has probability 1/2+2c(1−2η)² under a known independent
symmetric marker channel. For η=.1, α=.05, ε≤.001 and |c−c_*|≥.1, 2000
observed divisions suffice for a confidence rule to resolve and choose correctly
with probability ≥.95. At λ=1 this means 4000 roots in expectation. The
calibration-uncertain version uses 20000 divisions plus 20000 labelled reads.
The same bit also resolves the short-pulse sign on separated c classes without
identifying ε. Exact alias and nearby KL bounds quantify information limits.

## What changed our understanding

1. **Hidden correlation matters through continuation products.** The invisible
   direction is exactly (1,−1,−1,1); its offspring contraction is (v_S−v_T)².
   The schedule contrast depends on the difference of those responses, rather
   than on whether each extinction probability increases individually.
2. **Horizon changes the decision fibre.** The supplied log(8/7) seed crosses
   inside the valid kernel interval; log2 has crossing 1623/2468>1/4 and is
   uniformly B-favoring. Nonidentification can coexist with a known ranking.
3. **Integrated occupancy sharpens the repeated-source certificate.** Coupling
   until the first added division gives error 4ε(T−1+exp(−T)), substantially
   smaller than the crude 4εT. Later unlimited branching does not invalidate
   a first-disagreement argument.
4. **The sequencing mechanism appears at cubic order.** Parent division followed
   by two deaths gives the first nonzero term. The quadratic commutator vanishes
   at the extinction terminal state. The cubic difference is independent of ε;
   fourth-order terms contain the repeated-division dependence. This led directly
   to a uniform small-time theorem instead of a parameter-box search.
5. **Conservation can eliminate the apparent ambiguity.** With the full mother
   state and one inherited-count daughter observed, the other is the deterministic
   complement. The phenotype counterexample cannot be promoted to that molecular
   class. This branch is settled by a positive reconstruction result.
6. **Information about the decision can suffice.** Exact fibre endpoints give
   a sharp randomized regret rule even with no new measurements. A sister bit
   learns the one relevant covariance coordinate; demographic ε can remain
   unidentified inside the proved uniform classes.
7. **Calibration and sample units are real boundaries.** Infinite uncalibrated
   bits can still alias opposite decisions. Divisions are accepted marks; root
   count is random. A cap changes yield but preserves the conditional bit law
   when its flag is retained.

## Experiments and failed routes

The guide's exact fractions were imported and independently checked. The original
source was derived before its ODE was used. A small PGF grid used c=−.2,0,.2
and ε=0,.001,.1,1. The ε=0 solve matched exact values to below 10⁻¹²; stronger
ε results remain N. Exact symbolic Lie polynomials identified the pulse cubic;
a floating phase-order check confirmed its orientation. Two one-dimensional
tie searches on the exact fibre checked the sensitivity implementation against
centered differences; these diagnostics are not the sign certificates.

The log2 reversal hypothesis was refuted by exact feasibility, not solver failure.
Free covariance in the resolved conservative model was refuted by complement
reconstruction. Uncalibrated repair was refuted by the pair (.05,0),(.2,.25),
both giving observed agreement .6 but opposite seed preferences. A global
short-horizon fibre ordering is refuted by the two exact witnesses. These
routes are archived in HYPOTHESIS_LEDGER.md and should not be retried unchanged.

The public COLO858 candidate was inspected through the primary paper and the
reproduction README. It does not establish our stopped sister records, calibrated
birth states, source preparation or action response. APPLICATION.md gives the
precise non-applicability decision. No dataset was fitted and no bulk-likelihood
equivalence is claimed.

Every numerical/symbolic job used repository Python, one numerical thread and
a process lease. Complete replay takes about seven seconds. No expensive
population simulation, full optimization, generated-case campaign, dependency
update or large parallel workload was required.

## Formal evidence and its boundary

`proofs/CellTreatmentDecision/Resolution.lean` imports three useful modules:

- `FiniteSource.lean`: kernel validity, one-sister marginal, covariance square,
  noisy agreement identity and integer complement reconstruction.
- `SeedThreshold.lean`: exact affine threshold, both rational signs, ranking
  equivalence and certified fibre endpoint inequalities.
- `RiskComparison.lean`: error-to-sign implication, repeated-source rational
  margin, pulse cubic algebra and remainder-to-margin inequality, regret balance.

Strict compilation succeeded with exit zero, no warnings, no compiler output,
and frozen Lean 4.30.0/Mathlib. The aggregate's final run took 32.171 seconds,
reusing already verified dependencies where hashes matched. Receipt:
`evidence/lean.json`. No `sorry`, custom axiom or native unchecked computation
occurs in these sources. Earlier failed receipts are preserved.

The chronological branching construction, source-to-PGF equality, time-ordered
remainder, sensitivity/adjoint calculus, concentration and testing theorems
are conventional proofs in the manuscript. The Lean package does not pretend
to discharge those premises. Completing a general branching-process formalization
would be a separate stronger project, not an unreported red dependency of this
guide's explicitly permitted conventional-root outcome.

Compiler issues were repaired in place: local import prefix, noncomputable real
division, an unnamed-section terminator, and one unnecessary tactic-focus linter.
The linter was obeyed, not disabled. The replay wrapper required explicit UTF-8
for Lean source reads on Windows. None was a mathematical counterexample.

## AGC assessment

Initial checkpoint failed AGC-LAUNCH-E005 because the new directory had no
specification. After inspecting supported initialization and a local example,
we created a specification for this actual theorem. The returned lifecycle
`start` command was executed, then checkpoint returned CURRENT. Structure,
formal-failure, assembly and pre-stopping outputs are retained in evidence/.

AGC was useful as an evidence-boundary reminder, especially that mean equality
does not prove complete-law equality. It supplied no new mathematical argument.
Its authority is unbound, and its authored open cut is not automatically updated
by our conventional proofs. CURRENT means publication freshness, not theorem
verification. The local graph records earned C/E closure; no protected authority
was rewritten to manufacture a green status. No generated evidence was staged
or committed.

## Remaining limits and next action

No optional claim is silently included: large pulse horizons, fixed-horizon
ε=1 certification, unrestricted schedule optimization, arbitrary hidden environments,
biological calibration, response extrapolation and the full stochastic Lean
bridge remain outside the bounded theorem. The tiny certified pulse effect and
loose sample constants limit practical interpretation. No exhaustive novelty
claim is made.

The package's next action is to read the standalone theorem and replay its fixed
certificates using README.md. If a stronger project is explicitly opened later,
the most informative next calculation is a sharper phase-specific remainder or
validated PGF enclosure for a larger pulse horizon, rather than repeating the
already successful small-time searches. That work is not required for this root.
