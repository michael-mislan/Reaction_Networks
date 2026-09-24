# Publication follow-up handoff

Original guide: **72/72 PASS**, preserved. Follow-up brief: **32/32 PASS**.
The bounded publication scope is complete. No whole stochastic Lean theorem,
clinical fit, optimal-control solution or journal submission is claimed.

## Deliverables relative to the project root

- `single_lineage_measurements_treatment_order.pdf`: final 13-page paper.
- `publication/paper.tex`, `publication/references.bib`, `publication/paper.pdf`:
  editable source, references and identical compiled copy.
- `publication/README.md`: build, exact replay and strict Lean commands.
- `treatment_order_source_package.zip`: actual five Lean modules, TeX, vector
  figures, scripts, fixed evidence and dependency pins.
- `POSTPROOF_PROOFS.md`, `POSTPROOF_TASKS.md`, `HYPOTHESIS_LEDGER.md`,
  `daily/2026-09-21.md`: comprehensive derivations, task mapping and research log.

## Principal results and lessons

Complete retained-branch observation laws, including timestamps, event labels,
death and censoring, coincide under uniform independent daughter retention
and shared history-measurable policies. Exact founder-time integration gives
the finite-duration covariance boundary. At h=log(8/7), opposite preferences
at covariance -1/5 and +1/5 persist under recurring division. Live-daughter
occupation strengthens the supplied epsilon <= .001 certificate to <= .002;
the weaker witness's reserve expires near .002153, which is not evidence of
a true crossing. The same coupling proves a controlled persistent source with
mother-dependent marginal probabilities .6/.4.

Exact binomial tails prove the 40-division separated constant-treatment theorem.
Full-class procedures allow abstention: 200 divisions for constant treatments
and 1600 for pulses give more than .95 resolution at c=.2, while controlling
false declarations over the stated source class. Calibration-free covariance
sign information does not identify a shifted threshold. The direct endpoint
benchmark now uses the same separated decision task; its 7,814,272-root
Bernstein bound is sufficient, not optimal.

The first exact-tail implementation timed out at the 120-second guard. A
shared-denominator integer recurrence reduced replay to about two seconds
without relaxing exactness or increasing the resource budget. A 400-division
pulse pilot had valid coverage but only about .453 resolution, so it did not
meet the .95 resolution target. The 1600-division result was checked exactly.
These computational and statistical failures are recorded separately.

The paper includes the final proof chain, measurement repair and quantitative
scope. Discovery logs and rejected pilots stay outside it. Supplied seeds and
standard inference tools are credited. No new empirical measurements are used.

## Evidence and limits

`evidence/postproof.json` contains rational/symbolic replay of formulas, margins,
binomial tails, threshold brackets, refinement feasibility and effect sizes.
`evidence/postproof_lean.json` has verified=true, exit zero and empty output,
with warnings treated as errors, for FinitePulse.lean importing four earlier
modules. Lean verifies specified algebraic identities and rational margins.
Branching construction, integration, retained-record equality, coupling and
statistical guarantees have conventional proofs in the paper, not full Lean
formalizations. Current hashes of all five sources match the strict receipt.

`evidence/publication_qa.json` records the PDF hash, clean TeX checks and visual
review of all 13 final pages. The source archive contains all actual Lean files,
removing reliance on the previously inaccessible advertised URL. TeX/BibTeX and
Poppler are existing tools; missing pypdf was avoided with pdfinfo/pdftotext.
No dependency updates or environment replacement were needed.

The source is synthetic: immortal predivision founder, specified rates,
instantaneous nonperturbing readout, independent families and conditional error
assumptions are explicit. Rate ratios and multiple-founder dilution restrict
interpretation. Finite-time survival is not clinical cure or relapse. There is
no unresolved obligation within the brief's bounded publication scope.

## AGC assessment

Entry, post-structure and pre-stopping checkpoints were used. AGC helped check
freshness and avoid authority drift. Its current but unbound authored frontier
partly reflects older completed work; it does not certify these new mathematical
claims or automatically advance theorem status. Explicit derivations and scoped
compiler evidence establish the results reported here.
