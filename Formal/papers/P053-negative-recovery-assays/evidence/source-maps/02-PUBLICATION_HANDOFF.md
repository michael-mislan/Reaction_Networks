# Postproof refinement and publication handoff

**Follow-up: 30/30 PASS.** Original 50/50 retained as historical progress. The
conditional robust mathematical root is complete; empirical validation remains open.

## Delivered paper

`E:/Erdos Problems/problem_workspaces/RAF_AssaySept17_antimicrobial-tolerance_and_functional_viability/Functional_Viability_Paired_Recovery.pdf`

Title: *When can a negative recovery assay exclude a recoverable subpopulation?
Sharp coverage and stage-mismatch bounds for paired observations*.

Nine pages, two vector figures, four tables, four primary references. The paper
contains the final source, sharp bound, decision proof, synthetic worked example,
calibration requirements and explicit formal scope. Discovery attempts, task scores,
AGC details and optional profile/moment/switching results are outside the paper.

Editable source:
`E:/Erdos Problems/problem_workspaces/RAF_AssaySept17_antimicrobial-tolerance_and_functional_viability/publication/manuscript.tex`

Reproduction package:
`E:/Erdos Problems/problem_workspaces/RAF_AssaySept17_antimicrobial-tolerance_and_functional_viability/Functional_Viability_Publication_Sources.zip`

It contains all six actual Lean sources, both successful root receipts, the pinned
toolchain/manifest, the paper, TeX/BibTeX sources, numerical and figure scripts,
retained inputs/results, README and QA record. It is intended for the existing
repository's frozen environment. No remote commit or public submission was performed.

## Main result and consequence

Exact complementarity is no longer required. For four conditional stage probabilities
in [0,1], cross-protocol coverage x+a>=c,y+b>=c and within-protocol mismatch
abs(x-y)<=d give the sharp equal-allocation response floor

    R(c,d) = max(0,c²-d²)/4.

Recording at least kappa on covered types and exceptional recoverable mass at most
eta give g=(1-eta)*kappa*R. For n independent units in two fixed equal groups and
p>=theta, the sharp worst-case all-negative error is (1-theta*g)^n. A conditional
calibration-failure allowance delta yields delta+(1-delta)*(1-theta*g)^n.

The synthetic planning example c=.95,d=.5,kappa=.90,eta=.05,delta=.01 requires
2,300 units to exclude p>=.01 with error at most .05. Its exact worst-case error is
approximately .049949362294132. The adjacent power at 2,299 fails the budget;
all four table rows and their balanced neighbors were checked using exact rational
arithmetic. No biological parameter estimate or efficacy claim is made.

## Compiled boundary

New root: `FunctionalViability.Robust.calibrated_robust_certificate` in
`proofs/FunctionalViability/RobustCertificate.lean`.

Strict receipt: `verification/RobustCertificate.verify.json`, verified=true,
exit 0, warnings as errors, empty compiler stdout/stderr. Total verification
112.375 seconds. Source SHA-256:
`c29773c75fc4b03da6bb07b6cb6f6344fbcbd92ff9df372c7f7c72007d9306c6`.
Four source-bound dependencies cover clipping and sharp witnesses, finite source
paths, recorded population bounds and fixed balanced sampling. Original root and
source hashes were checked and remain unchanged.

Compiled: coverage lower bound and sharp source witnesses, coverage maximin and
positive-floor condition, approximate-complementarity lower bound, source path
normalization, balanced likelihood identity/inequality, recorded covered-mass floor,
sharper finite-environment calibration composition, and final source certificate.

Conventional proofs: full attaining exceptional mixture/environment construction,
logarithmic sample sizes, confidence inversion, all-factor feasibility boundary,
and optional follow-up consequences. Numerical: rational benchmark powers and
small diagnostic/profile checks. These levels are explicitly separated in the paper.

## Follow-ups completed outside the paper

POSTPROOF_NOTES.md gives the exact continuum allocation profile, its explicit
witnesses and uniqueness domain; finite-mixture mismatch-moment relaxation and
equal-marginal counterexample; safe sample bound and coverage-margin asymptotic;
and the optional switching identity with its missing transport premise. The
original 100-unit example is retained as a verified regression, with minimum
random sample 79 and balanced sample 80 checked separately. These refinements are
not used to inflate the paper's proof chain.

## Quality and AGC

All pages were rendered and visually inspected. Fixed an overfull source path,
figure seams/labels and a split operational example; affected pages were checked
again. Final TeX log has no overfull/underfull boxes, missing references or LaTeX
warnings. Fonts are embedded, DOI references are clickable and the workspace-root
PDF matches the build copy. The final source/receipt/PDF audit and ZIP integrity
check are retained in publication/publication_audit.json.

Entry, structural, proof-failure and final AGC checkpoints were run. New strict
proof inputs required the exact proof-neutral reconcile-frontier action; the
final checkpoint is CURRENT. AGC remained useful for freshness and input tracking,
not as a mathematical solver or canonical declaration of proof closure. No protected
theorem graph or generated-evidence commit was changed.

## Stopping argument and remaining empirical uncertainty

All required mathematical dependencies have complete proofs at their labeled
scope, the central new chain compiles, calculations reproduce, the PDF is built
and readable, and all actual source files are packaged. There is no remaining
required publication or formalization task.

The most important unresolved empirical issue is whether a real exposed population
and paired recovery design justify the claimed joint coverage, mismatch and hidden-type
bounds. Independent units, conditional recording and calibration transport must
also hold. The paper supplies a conditional measurement guarantee, not validation
of those premises or proof of irreversible death.
