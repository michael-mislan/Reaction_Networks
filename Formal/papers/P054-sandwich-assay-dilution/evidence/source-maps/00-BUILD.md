# When dilution resolves a low sandwich-immunoassay signal — arXiv package

Built 2026-09-17. Deliverable: `../Sandwich_Immunoassay_Dilution_Certificates.pdf`
(identical to `main.pdf` here, 23 pages). Author/affiliation block is intentionally blank
(`\author{}`); fill it in `main.tex` before submission. Suggested arXiv categories:
primary `q-bio.QM`, cross-list `q-bio.BM` (and `cs.LO` only if the formal side is to be advertised).
The abstract is 1.9k characters, inside arXiv's 1920-character metadata limit.

## Rebuild

```powershell
powershell -ExecutionPolicy Bypass -File key_results\RAFs\Sandwich_Immunoassay_Dilution_Certificates_arxiv\build.ps1
```

This runs `check_paper.py` (replays every printed number), `make_tables.py`
(Appendix A from the replayed coefficients), `make_figures.py`, three `pdflatex`
passes (MiKTeX, user scope) and asserts a clean log. For arXiv upload: `main.tex`,
`bib_body.tex`, `coeff_tables.tex`, `figures/*.pdf`; optionally `anc/` as ancillary files.
No BibTeX run is needed (the bibliography is a verified `thebibliography`).

| File | Role |
|---|---|
| `main.tex`, `bib_body.tex`, `coeff_tables.tex` | manuscript, references, generated Appendix-A table |
| `check_paper.py` → `check_paper_report.json` | exact-rational and numerical replay of all printed numbers |
| `make_figures.py` → `figures/` | six synthetic figures (validated colour-blind-safe palette, distinct line styles) |
| `make_tables.py` | emits `coeff_tables.tex` from the replay report |
| `anc/enclosure.py` | exact-rational outer-enclosure program (workspace `decision.py` with the verified 199/5000 cut) |
| `anc/lean/` | copies of the 13 Lean modules; canonical location is `proofs/SandwichImmunoassay/` |
| (not copied) | strict verification receipts live in `problem_workspaces/RAF_AssaySept17_SandwichImmunoassays/verification/` (`GeneralBox`, `Sequential`, `Structure`, `Preparation`, `Main`, `Publication` `.verify.json`; up to 9 MB each, so they are not duplicated here) |

## Evidence split (keep accurate if the paper is edited)

**Lean 4.30.0 + mathlib, strict (warnings as errors, no sorry, standard axioms only).**
Lemma 2.1; Prop. 3.2 (occupancy involution and `B(S²/u)=B(u)`); Thm 4.1; Thm 4.2 (general box);
Table 2 rows; Prop. 4.3 (7371/8000 law); Examples 4.4–4.5 including the wide low classes
(u ≤ 0.4, 15 nM, 20 nM); Prop. 5.1 for equal allowances; Cor. 5.2; Prop. 5.4 (relative error);
Props. 6.1–6.3; Props. 7.1–7.2; Thm 8.1 and Prop. 8.2 (sequential model).
New modules written for this paper: `GeneralBox.lean`, `Sequential.lean`, `Structure.lean`
(receipts in the workspace `verification/` folder; the stale failed `Preparation.verify.json`
was refreshed and now reports success).

**Conventional proofs in the paper (not Lean).** Thm 3.1 (elasticity, unimodality, two
preimages, monotone ratio, crossover); the consequences of the involution (peak at S,
u₋u₊=S², u†=S√d); Thm 7.3 and Cor. 7.4 (kinetic bridge, sufficient incubation time);
soundness of the outer-enclosure program; attainment of the endpoints in (6.1);
unequal-allowance and direct-contrast variants of Prop. 5.1.

**Numerical only (labelled as such).** Remark 4.6 (tightness 0.0486/0.610/1.218 and the
crossover ranges), all tables of floating-point illustrations, all figures.

## What was added relative to the 11-page workspace report

General-box theorem and the asymmetric regimes moved from "ordinary proof" to Lean; wide
low classes; the hook involution and the structure theorem (new); kinetic bridge with explicit
rate λ = k_on·sqrt((u−C)²+2K(u+C)+K²) ≥ k_on·max(K, 2√(CK)) (new; resolves the "unproved
kinetic bridge" caveat for well-mixed mass action); sequential-assay theorems with the
plateau-gap bound KC/(u−C) and carry-over tail CD/(λ(u−C)) (new, Lean); precision-profile
bridge; relative-error reduction (Lean); verified 35-item bibliography.

## Pitfalls met

* Bash heredocs eat backslashes: write Python patch scripts with a file tool, never via heredoc.
* `\outer` is a TeX primitive; the macro is `\outerset`.
* Floats with `[t]` can split a theorem statement; Figure 1 is placed before Theorem 3.1 in the source.
* `verify_proof.py` probe extraction fails if a requested declaration name is a prefix of an
  earlier requested name; list the shorter name first.
* SI material deliberately left out: the 12-item integration register, the review-response table,
  and the AGC process notes.
