# Claim-to-proof concordance

Current scope, 20 September 2026. This document supersedes historical red status in predecessor notes without altering those records. Main theorem: paper.tex Theorem 1.1, exact strict compatibility on every finite oriented simple source graph with positive rational fixed factors and independent rational boxes in (0,1], rational output, and XP bit bound `(n+2)^{O(h+1)}(B+log(n+2)+1)^{O(1)}`. Here h is undirected longest simple-path length. Neither general polynomial time nor FPT is asserted.

All Lean paths below have prefix `proofs/ThermoCoreCompatibility/`. Compiled means a strict receipt exists for the current file hash, not that every surrounding conventional claim is formalized. The baseline matched nineteen existing receipts; new Inventory and RobustExample receipts have exit code zero, empty stdout/stderr and warning-as-error enabled.

| Main claim | Conventional proof | Compiled interface and limitation |
|---|---|---|
| Source residuals and increasing bands | Equations 1--3; source algebra | MultiInterface/WeightedPair.lean: productive_iff, residual_lower, residual_upper; WeightedSource.lean source equivalence |
| Nonnegative inverse and boxed implications | Section 2 and quadratic graph equations | GeneralCompatibility/SourceImplications.lean: upper_inverseUpper, inverseUpper_le_iff, boxed_margin_iff_implications. Source analyticity composition is conventional. |
| Forced least-root update | Lemma 3.1 | CycleJump.lean: lifted_cycle_violation, fixed_between_violation_and_prefixed, least_cycle_root_preserves_bound, no_cycle_root_rejects_prefixed. Simple-path extraction and full enumeration are conventional. |
| Finite cycle roots and finite updates | Lemma 3.2 | CycleBranches.lean finite_cycle_roots_of_violation / finite_cycle_roots under explicit analyticity premises; FiniteProgress.lean no_infinite_anchor_updates and cycle_jump_count_bound under finite token data. Constructing graph cycles and discharging analytic premises are conventional. |
| Candidate coverage and transport | Lemmas 4.1--4.3 and Proposition 4.4 | CandidateTransport.lean feasible_of_candidate_transport handles transport of all original tests. Complete enumeration, retained-seed QE, CAD and branch ranks are conventional. |
| Strictness threshold | Proposition 5.1 | StrictDecision.lean strict_iff_positive_margin, margin_downward, strict_decision_of_stable_margin. Root.lean source_decision_at_stable_threshold and no_productive_source_of_no_threshold_state require stability. The effective H and t0 are supplied by this paper, not constructed in Lean. |
| Rational reconstruction | Lemma 5.2 | BeyondJunction/MarginTransfer.lean checks Lipschitz/error-transfer interfaces. Binary floor search and global rational output implementation are conventional. |
| Sharper local and total bit costs | Lemma 6.1 and final proof of Theorem 1.1; ARITHMETIC.md | Conventional only. Uses one-block QE and complete CAD in at most three free variables. No claim of an executed generic projected-QE implementation. |

The final root receipt is `../verification/GeneralRoot.json`. Other relevant receipts are named after their modules. `../paper_campaign/baseline.json` records hash freshness. Lean 4.30.0 and the checked-in mathlib manifest are unchanged. Reported ordinary logical axioms in the prior root are Classical.choice, Quot.sound and propext. Absence of sorry does not prove unformalized hypotheses or convert a conditional bridge to an end-to-end verified algorithm.

## Follow-up claims outside the critical-path paper

| Claim | Evidence / boundary |
|---|---|
| Least inventory | FOLLOWUPS.md section 1; ClosedMargin.margin_has_least; new Inventory.least_minimizes_monotone and least_minimizes_inventory compiled. |
| Capacity bound and unit optimum | FOLLOWUPS.md section 1; certificates.py exact 1/48 witness and symbolic maximum. Conventional global bound; no general rational maximizer claim. |
| Positive weighted demands | FOLLOWUPS.md section 2; positive shifted unique transports, explicit rounding coefficient. Conventional extension. |
| Robust ratios and rectangular rate uncertainty | FOLLOWUPS.md section 3; endpoint derivative proof and affine corner reduction; parallel-map counting. Conventional extension. |
| Nominal triangle and activity/factor box | certificates.json exact arithmetic; RobustExample.triangle_nominal and triangle_box_corners_positive compiled. Universal corner reduction is conventional, not asserted by a rational-corner theorem alone. |
| All-size windmills, food and hub scaling | FOLLOWUPS.md section 4; edgewise transfer and graph proof; RobustExample.residual_sum compiled. |
| Minimal incompatible directed cycle | FOLLOWUPS.md section 6; strict decrease proof and rational path witness. Conventional. |

## Literature comparison by assumptions

* Basu's survey (arXiv:1409.1534, Theorem 2.27) and Basu--Pollack--Roy, second edition (2006): arbitrary polynomial formulas, effective elimination; supply arithmetic primitives, not this graph-local ancestry theorem. The sharper bound is our deduction, with no claim that generic decidability was open.
* Dadush--Koh--Natura--Vegh (arXiv:2004.08634): linear two-variable-per-inequality systems, strongly polynomial methods; does not directly cover inverse quadratics and parametric seed branches.
* Cooper--Jeavons--Salamon (Artificial Intelligence 174, 2010, 570--584): finite-domain hybrid constraint tractability and elimination; illustrates that graph structure and closure are established themes. It does not by itself furnish these continuous root/bit bounds. No exhaustive priority claim is made.
* Noor et al. (PLoS Computational Biology 10, 2014, e1003483): thermodynamic pathway driving force; objective and physical assumptions differ from fixed-factor kinetic residual margins. No biological validation is inferred.

Primary references and links appear in the paper. No named literature conjecture is claimed resolved without an authenticated statement matching this source contract. Optional targets left open are practical solver engineering, FPT/unrestricted polynomial bounds, and general structural capacity optimization.

## Second-sprint additions (20 September 2026, final paper in key_results/RAFs)

| Claim | Evidence / boundary |
|---|---|
| Vertex elimination with next-maps (paper Lemma 7.1, core of the FPT algorithm) | GeneralCompatibility/MonotoneElimination.lean: IsNextMap, IsNextMap.mono, IsNextMap.fixed_of_mem, eliminate_vertex_iff, eliminated_value_least, generated_map_mono. Strict receipt verification/MonotoneElimination.json. Forest induction, tameness, Davenport-Schinzel piece bound and arithmetic are conventional. |
| One-sided rounding, capacity ceiling, ratio monotonicity, robustness obstruction, order-d band | GeneralCompatibility/Consequences.lean: round_down_margin, min_residual_le_capacity, ratio_factor_le, lower_mono_ratio, upper_mono_ratio, robust_band_empty, order_d_band. Strict receipt verification/Consequences.json. |
| FPT theorem f(h) n^2 poly(B); label-correcting Algorithm 1; infinitesimal-margin trace invariance; path barrier | Conventional proofs in the final paper (Sections 3, 5, 7, 8). |
