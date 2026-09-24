# Publication handoff — 20 September 2026

**60/60 complete:** original 36-item core preserved, all 24 selected follow-ups
completed. The attached brief is saved as POSTPROOF_BRIEF.md. The paper contains
the final critical argument, not the discovery diary or superseded converse.

## Deliverables

- Root PDF: `exposure_limits_persister_eradication.pdf`.
- Editable source/bibliography: `publication/paper.tex`, `publication/references.bib`.
- Reproduction entry: `publication/README.md` and `experiments/reproduce_publication.py`.
- Actual proof sources/data/scripts: `publication/reproduction_sources.zip`.
- Current score/graph: `campaign/POSTPROOF_TASKS.md`, `campaign/HYPOTHESIS_GRAPH.md`.
- Complete history: `campaign/daily/2026-09-20.md`, continuing Sprints 5–7.

## New results

1. General remaining-budget theorem: arbitrary bounded predictable feedback,
   finite inherited state, correlated bounded offspring, heterogeneous preparation,
   and a continuation with qoff<=q imply survival at least
   `1-product_i[1-exp(-cB)(1-q_i)]^z_i`. The product is a population test function,
   not a factorization of feedback-dependent founder outcomes.
2. Correct population-size law: necessary and achievable exposure both have order
   log(n/delta), at a fixed admissible amplitude and with a sufficiently long finite
   horizon. A separate finite-time floor follows from the maximum death hazard.
3. Sharper policy: the improved rational weight gives decay .105 and prefactor
   10.765. The 40-unit .3-erasure pulse followed by baseline to time 100 is rigorously
   certified to have AA survival < .009818264214475, at exposure 11.6.
4. Meaningful source variation: rational certificates hold for protected division
   [.08,.1] and for N=4 (15 states). The latter's weaker decay shows why no uniform
   site-count control constant has been established.
5. Explicit application conditions: eraser-only and full withdrawal are distinct;
   the stated full-off source has qoff=.1. Conditional saturation/PK assumptions
   convert the exposure floor to concentration and administered-amount lower bounds.

All theorem probability arguments are conventional (C); source/enclosure checks
are exact (E); named local algebra is compiled (K); illustrative schedule curves
and full-withdrawal comparisons are numerical (N). No full stochastic Lean claim.

## Validation and lessons

The smallest validated-ODE pilot succeeded before the full computation. The full
2000-step outward dyadic run took about 8 seconds and bounded total error below
2.497e-15. The certificate uses exact integer/fraction arithmetic; floating output
is only a display. Source-extension search was tiny and followed by saved-vector
rational replay. No large population simulation or Bellman truncation was used.

Strict publication.json verifies PublicationAlgebra and seven dependencies, with
warnings as errors and current source hashes. It includes the segment identity,
improved weight, budget/product algebra, dose rearrangement and Taylor comparison.
The source archive contains the locally present BudgetBarrier.lean that the
reviewer could not access remotely. The pinned mathlib environment was unchanged.

The complete reproduction entry point passed under a 180-second process lease in
about 21 seconds, rebuilding exact checks, the enclosure, saved source certificates,
figures, tables, PDF and archive. The PDF log has no undefined references or overfull
boxes. All pages were rendered and visually inspected; bibliography and table
placement were adjusted during layout QA. MiKTeX latexmk lacked Perl, so the
existing pdflatex/bibtex chain was used successfully without installing anything.

AGC checkpoints continued to return E005 (missing authoritative specification).
The lifecycle documentation was inspected; no authority was fabricated. The
final result is saved in verification/agc_publication_final.json. AGC was useful
for diagnosing missing authority but provided no mathematical guidance.

## Scope still open

The optimal constants and schedules remain unresolved. At n=1, target .01,
T=100, the necessary exposure is about 4.7257 and certified sufficient exposure
is 11.6. The log-order theorem does not close that constant gap. No empirical
birth/death calibration, clinical dose, uniform-in-N law, hidden-carrier theorem,
or full stochastic Lean formalization is asserted. These are explicit future
scopes, not hidden unfinished items in this publication brief.
