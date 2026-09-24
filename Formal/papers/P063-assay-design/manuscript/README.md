# How to design an assay that answers the biological question

A perspective with worked mathematical examples, primarily for practicing assay designers and quantitative biologists. Authorship and affiliation are intentionally blank.

## Contents

- `main.tex`: main article, five figures (including a practical design workflow), and two main tables.
- `appendix.tex`: selected derivations and a claim-to-proof-scope map; included in the same PDF.
- `references.bib` and `main.bbl`: editable bibliography and submission-ready rendered bibliography.
- `figures/*.pdf`: vector figures embedded in the paper.
- `reproduce.py`: reproducible quantitative figures and exact rational checks, with no random sampling.
- `make_workflow.py`: editable vector workflow diagram.
- `calculations.json`: exact and labeled floating-point outputs.
- `source_provenance.json`: hashes of the eight supplied PDFs, current manuscripts, and 13 selected Lean modules, with matching strict receipt pointers.
- `build.ps1`: reproducible MiKTeX build with error checks and final PDF copy.

The final PDF is `../ASSAYS_How_to_Design_an_Assay.pdf`. The ZIP alongside it contains the LaTeX submission files, vector figures, and editable reproduction material. It excludes logs, page renders, and repository-specific verification receipts.

## Rebuild

From this directory:

```powershell
powershell -NoProfile -File build.ps1
```

To regenerate figures and calculations as well:

```powershell
powershell -NoProfile -File build.ps1 -RegenerateFigures
```

The latter uses the repository's `.venv/Scripts/python.exe` (Python 3.11) with its locked NumPy/Matplotlib stack. A standalone source archive can be compiled with conventional `pdflatex main`, `bibtex main`, `pdflatex main`, `pdflatex main`; the vector figures are already included, so Python is unnecessary for LaTeX compilation. The reproduction script itself needs Python 3.11, NumPy, and Matplotlib, and uses only standard-library rational arithmetic for exact checks.

## Evidence and review

- Repository Python check and numerical smoke suite passed.
- All eight supplied PDF hashes match the proposed guide's versions, including the immunoassay PDF whose guide filename had a `(1)` suffix.
- The manuscript uses the current full-range viability coverage result.
- Arithmetic checks reproduce the exact population intervals, specimen joint-event risk, blank reporting availability, count cutoffs, matched wash bounds, reserve threshold, reporter constants, and equilibrium source balance. A 144-case rational grid checks the implementation of the equivalent material formulas; this is QA, not a continuum proof.
- Existing warning-as-error Lean receipts were audited against current source hashes, Lean 4.30.0, and the frozen manifest. Direct receipts and verified dependency receipts are distinguished in `source_provenance.json`. No Lean sources were edited and no fresh Lean compilation is claimed.
- All 22 revised pages were rendered for layout review. The final LaTeX build has no unresolved citations/references, overfull/underfull boxes, or layout warnings. MiKTeX emits its installation-level update reminder; no package or toolchain update was performed.
- External references were checked against primary publisher, guideline, or author sources. The eight companion titles were reconciled with their actual title pages rather than their filenames.

## What remains for submission

The requested author and affiliation fields are blank. Fill those and choose the submission category, license, and other depositor metadata at submission. The eight companion assay references are explicitly marked unpublished. Their supplied title pages do not assign authorship or public identifiers; none was invented. Provide the actual author lists and deposit identifiers when released, or make the companions available with the submission. No claim of arXiv acceptance, peer review, clinical validation, or public release is made.

The article is a perspective with worked examples. It does not treat the agent guide as scientific authority, transfer unrelated phosphorylation/RAF results into an assay theorem, or propose clinical use of the synthetic thresholds. Conventional ODE arguments, formal algebra, numerical illustration, and empirical premises remain distinct. No additional numerical campaign or biological experiment was needed to write the supported synthesis.

Repository audit materials and extracted source text are under `problem_workspaces/RAF_assay_canonical_synthesis/`. The source audit command is:

```powershell
.venv/Scripts/python.exe scripts/process_guard.py run --timeout 180 --owner-label assay-synthesis-source-audit -- .venv/Scripts/python.exe problem_workspaces/RAF_assay_canonical_synthesis/audit_sources.py
```

## Editorial revision

The revision defines its primary audience, replaces study-letter labels in the main text with biological case names, moves exact arithmetic and formal details into the appendix, removes the separate RAF discussion, adds published validation/digital-PCR/persistence context, explains the washing mechanism, and adds a five-figure practical workflow. The derivations and conditional scope are retained.

`../ASSAYS_How_to_Design_an_Assay_Review_Materials.zip` contains the revised paper and all eight companion PDFs for local review. This package provides inspectable source material; it is not a public archive deposit. Public identifiers and author metadata still require the authors’ submission decisions.

## Prose pass

The 18 September prose pass shortened the main source text by approximately 14%, smoothed transitions, consolidated repeated scope statements, and replaced the closing checklist with a worked application of the existing microbial example. The title, author blanks, bibliography, quantitative figures, equations, and appendix derivations are preserved. The final PDF is 22 pages. The previous PDF and sources are saved in the audit workspace under `before_prose_pass/`; `prose_changes.diff` records the main-text edits. The source and review archives both contain the latest version.
