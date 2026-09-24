# Reproduce the exposure-limits paper

The final PDF is at the project root:
`../exposure_limits_persister_eradication.pdf`.
The editable manuscript, bibliography, vector figures and data are here.
No journal submission or public upload has been performed.

## Environment

Run from `E:/Erdos Problems` in the existing frozen repository. Use only
`.venv/Scripts/python.exe` (Python 3.11, requirements.lock). Lean is pinned to
`leanprover/lean4:v4.30.0`; the current lake-manifest hash is recorded in receipts.
Do not run lake update. MiKTeX pdflatex and bibtex build the paper. latexmk
is installed but cannot run on this host because Perl is absent; no update is needed.

## One entry point

```powershell
.\.venv\Scripts\python.exe scripts/check_python.py --quiet
.\.venv\Scripts\python.exe scripts/smoke_numerics.py
.\.venv\Scripts\python.exe scripts/process_guard.py run --timeout 600 --owner-label PersisterPaper -- 'E:\Erdos Problems\.venv\Scripts\python.exe' problem_workspaces/RAF_memory_disruption_and_persister_eradication/experiments/reproduce_publication.py
```

This rechecks the exact source, reconstructs the validated PGF enclosure, checks
the saved rational source-extension certificates without repeating candidate
search, generates figures/data, builds the PDF, and creates the source archive.
`--build-only` rebuilds from saved data. `--lean` additionally replays strict
verification of PublicationAlgebra before building (allow a 900-second outer lease).
The usual run does not claim to rerun Lean; the saved current receipts are checked.

## Individual checks and source map

All paths below are relative to the project workspace unless stated otherwise.

- `experiments/exact_source_checks.py`: exact inherited six-state algebra.
- `experiments/validated_pgf.py --pilot`: one-unit small enclosure check.
- `experiments/validated_pgf.py`: rigorous early-pulse certificate, 2000 steps,
  dyadic precision 110 bits, degree 11 plus order-12 remainder, no floating arithmetic
  in the certificate. Its final decimal is only a display of the stored fraction.
- `experiments/source_extensions.py --check-only`: independent rational replay of
  every saved q, c, w and gamma for N=2, slower protected division, and N=4.
- `experiments/source_extensions.py`: optional regeneration of numerical candidates
  followed by exact checks; deterministic saved vectors suffice for the paper.
- `experiments/publication_figures.py`: theorem curves, table, numerical policy and
  withdrawal comparisons; no new optimization. Figure lines are labeled N.
- `publication/validated_policy.json`: exact enclosure and phase/error record.
- `publication/source_certificates.json`: exact fractions, state order and residuals.
- `publication/figure_data.json`: all numerical plotted values and budget table.

Strict verification command from repository root:

```powershell
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/PersisterMemory/PublicationAlgebra.lean --timeout 180 --declaration PersisterMemory.publication_algebra --output problem_workspaces/RAF_memory_disruption_and_persister_eradication/verification/publication.json
```

The receipt compiles/checks ControlSource, BudgetBarrier, SupersolutionSegment,
ImprovedPulseCertificate, RemainingBudgetAlgebra, DoseExposureBounds and
ShortTimeComparison. It does **not** formalize the stochastic process or the
validated integrator. The paper's proofs supply those conventional arguments.
The archive includes the actual `.lean` files, including BudgetBarrier, rather
than only interface receipts. Standard logical axioms are distinguished from
`sorry` or target assumptions; no such placeholders are accepted.

## Build and view

Within this publication directory:

```powershell
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
bibtex paper
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
pdftoppm -r 110 -png paper.pdf qa/page
```

The builder copies `paper.pdf` to the requested project root after checking the
log for unresolved references and overfull boxes. The final pages were rendered
and visually inspected. Numerical residual checks and receipts are evidence;
hashes only establish which sources were checked.

## Scope and data provenance

All case-study chemistry and demography are synthetic assumptions inherited from
the supplied molecular source. `parameter_provenance.csv` records the units and
missing calibration. The public primary references were checked on 20 September
2026. The companion manuscript is identified by `../provenance.json`; it is not
represented as a peer-reviewed publication. No rates were calibrated from another
paper's net-growth curve. No claim is made for a dense tumour or a drug-specific dose.

The required AGC checkpoints remain E005 (missing authoritative specification),
recorded under verification. AGC publication status is separate from mathematical
proof status. The original 36-item core and the new 24-item extension have separate
registers in campaign/. Failed compiler/build attempts stay in the daily ledger,
not in the scientific paper's critical argument.
