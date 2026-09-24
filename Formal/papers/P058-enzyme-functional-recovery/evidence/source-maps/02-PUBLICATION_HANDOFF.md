# Publication handoff

Completed publication and implications register: **20/20 PASS**. Original primary campaign remains **28/28** at its recorded evidence levels. The primary mathematical root is verified and unchanged. The separate whole-cell application remains open at inherited 19/24.

## Deliverable

Final paper, saved in the project workspace root exactly as requested:

`E:/Erdos Problems/problem_workspaces/Medical_Sept16Plan_11_G6PD_activity_and_redox_reserve/Project_11_Research_Paper.pdf`

Title: *From bulk enzyme activity to cellular recovery: sharp population bounds and measurement requirements*.

10 pages, two vector figures, three tables, five primary references. The main proof and useful selected consequences have complete conventional arguments. The manuscript excludes the discovery ledger, failed proof attempts, carrier pairing/concavity, optional asymptotics, contamination extensions and unrelated green results. It distinguishes uncoupled dynamics from statistical independence and restricts the assay interpretation to the physical nonnegative domain.

SHA256: `bdcd53de8ad35814fe556142ae605942abb875eccae90c49486c11b30b0e6794`.

Source/build package: `publication/main.tex`, `publication/references.bib`, `publication/calculate.py`, `publication/build.ps1`, `publication/README.md`, `publication/figures/`. The full hash/evidence inventory is `publication/final_artifacts.json`. The local build copy `publication/main.pdf` is byte-identical to the root deliverable.

## Follow-ups completed

One bounded current-definition and receipt check confirmed the original root and all eight dependency source hashes. The primary receipt was not regenerated for unchanged prose.

New file: `proofs/G6PDReserve/PopulationConsequences.lean`. Strict verification receipt: `verification/PopulationConsequences.verify.json`. Authenticated exported declarations:

- `G6PDReserve.Population.bulk_minimax`: exact bulk midpoint/error radius 61/82 and 21/82, using sharp realizability.
- `G6PDReserve.Population.repaired_minimax`: exact repaired midpoint/error radius 361/490 and 31/490.
- `G6PDReserve.Population.extra_error_budget`: additional readout uncertainty at most 1/150 preserves the two-thirds guarantee under the stated assumptions.
- `G6PDReserve.Population.weight_conversion`: derives the number/weighted fraction enclosure from explicit successful and failing mass bounds.
- `G6PDReserve.Population.normalization_boundary`: the converted lower endpoint is at least two-thirds exactly for ratio at most 33/32.

The module also contains the generic interval/decision lemmas and exact numerical substitutions. Verification returned true, exit code zero, warnings as errors, only Classical.choice, Quot.sound and propext. One initial build failure was a deprecated tactic; it was repaired without changing the mathematics.

The small reproducer validates all new exact constants, the 33702 one-sided Hoeffding count and four numerical horizon values. All displayed rational rectangle decimals were checked to enclose the saved exact fractions outward. No broad search or statistical package was introduced.

## Explicit assurance boundary

Ordinary-only claims are the arbitrary-horizon adapter argument, connected-support cutoff and nonattainment, eventual threshold/attainment, averaged tail enclosure and concentration-inequality application. The paper supplies their arguments and labels them. Optional general Lean cutoff or all-time formalization was not needed to deliver the primary result. Empirical G6PD calibration and joint whole-cell service/peroxide/restart remain unproved and are not described as solved.

## Build and visual QA

Used the existing repository LaTeX article template. Installed latexmk lacked Perl, so build.ps1 runs installed pdflatex and BibTeX directly. No Python, Lean, mathlib or TeX dependency update was made. Final LaTeX log has no warnings, undefined references, missing glyph reports or overfull boxes.

All ten pages were rendered with Poppler and visually inspected. Pages 8–10 were re-rendered and rechecked after final text/bibliography adjustments. Equations, plot axes, endpoint labels, captions, page numbers, tables and bibliography are legible and unclipped. No external publication or submission occurred; no authorship or institutional affiliation was invented.

## AGC

Entry checkpoint was CURRENT. The corollary failure gate was recorded; new evidence triggered same-cut reconciliation. Final checkpoint is saved as `verification/publication_terminal_agc.json`. The known `NO_OPEN_FRONTIER` automatic proof-publication limitation was not retried or concealed. Same-cut reconciliation is proof-neutral; the strict receipts establish mathematical evidence, and the built/rendered PDF establishes publication-task completion.

No mathematical or artifact-production work remains for this requested publication. Reproduction commands and checked reference records are in publication/README.md; ongoing empirical work remains a separate question.
