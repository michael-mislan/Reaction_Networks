# Postproof mathematical and publication handoff

Date: 21 September 2026 UTC. This supplements the original `HANDOFF.md`; the original 64/64 task register and original six Lean sources are preserved. The postproof brief has 32 items. Completion includes the brief's explicitly permitted bounded negative/deferred outcomes, not a claim to have proved those stronger statements.

## Delivered result and critical proof path

The publication is `selective_eradication_finite_regenerative_reserve.pdf` in this workspace root, titled **Reserve capacity and reliable eradication in inherited-state populations**. It has 14 pages, three figures, an exact certificate appendix and five primary references. Modular LaTeX, bibliography and reproduction instructions are in `publication/`; `publication/reproduction_sources.zip` contains the actual nine Lean source files, their local dependencies, numerical producers, exact data and environment pins. No journal submission was performed.

The final path is: reconstruct the literal six-state chemistry and complementary daughter allocation; prove weighted source drift and its one-percent relative-error envelope; verify that the actual finite administration course enters the contraction band; prove an anchored healthy excursion bound; insert the exact finite reserve product; and combine the two marginal events by the union bound. The capacity theorem and initial-reserve corollary explain the certificate's resource dependence. Discovery-only asymptotic and control-search branches are excluded from the paper.

The strengthened witness has K=400, threshold 200, initial healthy count at least 278, effective renewal in [1,2], selectivity in [2,3], extra healthy mortality in [0,.005], clearance in [.99,1.01], and four AA target founders. One administration, .29 until time 112 and then zero, is used throughout the uncertainty box. Target-rate factors vary independently within one percent. At deadline 120, target survival is below .00856 and any healthy crossing below threshold has probability below .000007. Joint success is therefore greater than .991433. Amount is 32.48, and effect exposure is below 33 including washout. The paper distinguishes the joint probability from extinction probability alone.

The improvement changes capacity, filling and selectivity; it is not a faster-renewal theorem at identical preparation. A comparison table retains the original K=20, fully filled, renewal>=12 witness and the same-capacity renewal>=9 variant with their narrower cancer box. The new result does not claim clinical calibration, a global optimal therapeutic frontier, or a named historical conjecture solution.

## What was proved and learned

**Anchored reserve.** At any chosen return level M, scale-function increments have ratio Km/[r_eff(K-h)]. Their normalized final increment is the probability of hitting the failure boundary before returning. Departures from M occur with expected count at most MmT; counting their eventual failed excursions bounds finite-time path failure. Unit-jump order coupling transfers this to adapted sources without assuming the logistic birth rate is monotone in population. Choosing M near the operating reserve avoids forcing every excursion to return to the hard ceiling. The new simple bound is 6.9381403704212035e-6; retaining the scale denominator gives about 2.67047637e-6. The theorem uses the simpler compiled value.

**Initial filling.** Starting below M adds the exact scale probability of hitting the lower boundary before M. A random preparation can be averaged directly; a probability eta of starting below M costs at most eta. This is a source condition, not a cosmetic change to a population label.

**Source uncertainty.** Endpoint rational checks improve nominal growth/contraction coefficients to .134 and -.099. The weighted relative-error coefficient is at most 1.35, so one-percent independent rate errors cost at most .0135. After the four-unit ramp, the net decay exponent through time 112 is 8.644. Positive Taylor sums certify the exponential margins. Changes to chemistry diagonals are included, and the daughter law is not independently resampled.

**Capacity.** For threshold ceil(K theta), anchor floor(K(1-m/r_eff)), and 1-m/r_eff>theta, a decreasing Riemann sum yields a finite bound KmT exp(-K I+2 f_theta). The explicit factor controls integer rounding. This is an upper-bound rate, not an exact fixed-time large-deviation theorem. Capacity, renewal and initial filling are distinct resources. Founder burden increases the sufficient contraction duration logarithmically, but any extra duration also requires additional amount and horizon allowances.

**Interpretive limits.** The old low-renewal exclusion already fails from baseline mortality: terminal survival above threshold is less than 1e-7. It is not evidence for a treatment-induced exclusion in an otherwise safe baseline. Renewal inhibition is handled by a retained lower rate r_eff=r chi_min. No completed replenishment before an initial latency, with an unloaded pipeline, creates a binomial lower-tail risk floor that later recovery cannot undo. Those distinctions are included in the paper.

## Bounded investigations and negative outcomes

1. Eighteen small joint-subsolution LPs at K=20 and renewal 4, 4.5 and 5 found no positive separating objective. These points have exactly certified safe untreated healthy bounds and poor untreated target eradication. The normalized ansatz f(K)=1 is infeasible already at the ceiling row: it needs eta>=67(.3)/73+.1, whereas the tested eta is at most .08. Thus raising the failure penalty cannot repair this tested ansatz. No all-policy safe-baseline converse was proved. The missing implication is a source/control/budget-sensitive subsolution whose lower bound exceeds .01+.01 lambda; expanding the same blind parameter sweep is not justified.
2. The homogeneous high-renewal leading coefficient was proved conventionally in `POSTPROOF_THEORY.md`: the conditional failed-excursion duration is O(1/r), and the departure compensator gives the coefficient (Km)^(d+1)T/d!. A K=4 pilot approaches the predicted coefficient 8. This branch is complete as a note but omitted from the paper's critical argument.
3. The proposed time-varying coefficient needs uniform inhomogeneous excursion and terminal-boundary error estimates. The homogeneous proof does not provide them, particularly for r-dependent oscillation. This branch is explicitly deferred under P18; no Jensen scheduling conclusion is used.
4. A matched inherited-kernel diagnostic preserves first moments while changing extinction probability (approximately .3217 versus .27298 survival in its separate diagnostic setting). It is labelled floating numerical evidence, retained in data and omitted from the main proof.

These outcomes satisfy the brief's bounded-investigation items without turning missing stronger theorems into proved claims. No required mathematical implication remains for the published sufficient result.

## Verification, performance and production

The canonical Python runtime check and native numerical smoke suite passed. Exact finite computations use rational arithmetic. All longer numerical commands ran through `process_guard.py` with explicit timeouts and one numerical-library thread. No large brute-force search, new package version, Mathlib update, or new agent was needed.

`verification/publication.json` records successful strict verification of `TherapeuticWindows.publication_certificate`; `AnchoredReserve.lean`, `WideBox.lean`, and `Publication.lean` are the three additions. The original six modules remain unchanged. The end-to-end reproduction driver also verified both Root and Publication, with successful receipts `verification/reproduced_root.json` and `verification/reproduced_publication.json`. Cached dependencies are authenticated by the repository bridge. All accepted Lean runs have exit zero and no warnings. Probability construction, stopping, coupling and asymptotic arguments remain conventional proofs; the paper states this boundary explicitly.

The reproduction run regenerated saved rational tables, three figures and the PDF. The numerical killed-chain curve is illustrative, while its dashed envelope is a theorem bound. The design map leaves unclassified points unclassified. The final LaTeX build has no unresolved citation/reference or overfull-box warning. All 14 pages were rendered and visually inspected; the reproduction render was compared to the inspected pages. The QA record is `publication/qa/QA.md`.

AGC entry, post-structure/converse and stopping checkpoints returned actual `AGC-LAUNCH-E005`: no authoritative specification exists for this workspace. AGC was therefore **not helpful for mathematical guidance** in this pass. The diagnostic outputs are saved; no authority file, publication status, or proof evidence was invented to bypass it. This does not block the local scope completion expressly authorized by the brief.

## Final scope and handoff

Postproof: **32/32 PASS** when the package and stopping record are saved; cumulative **96/96** including the original guide. P18 is PASS for the permitted documented deferral, and P19 for the completed bounded investigation with its exact obstruction. Neither is labelled a proved extension. Publication production closes PP-PUBLICATION; there is no required red node left on the selected proof path.

For future work, the safe-baseline converse and uniform time-varying excursion asymptotics are separate research questions. Neither is needed to reproduce or assess this paper. Do not launch bulk searches from this handoff. The attached publication brief is fully addressed at its stated evidence scope, and the final paper contains the source-connected finite-mission proof rather than a discovery diary.
