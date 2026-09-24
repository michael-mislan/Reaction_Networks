# Conservative molecular inheritance and population risk — source bundle

Paper: `main.tex` + `refs.bib` + `figures/` → `main.pdf` (22 pages).
Delivered copy: `key_results/RAFs/Conservative_Molecular_Inheritance_Population_Risk.pdf`.
Author/affiliation block is intentionally blank (`\author{}`).

## Build (MiKTeX)

```powershell
$env:PATH="$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64;$env:PATH"
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

Only relative paths are used. For arXiv upload: `main.tex`, `main.bbl`, `figures/*.pdf`.
Do not pipe `2>&1` from pdflatex in PowerShell 5.1 (the MiKTeX update nag goes to stderr).

## Regenerate numbers (repository Python 3.11 venv: `E:\Erdos Problems\.venv`)

Run from `scripts/`, in this order:

| Script | Output | Role | Time |
|---|---|---|---|
| `slope_certificate.py 7.999 8.001 1` | `data/slope_certificate_7.999_8.001_1.json` | Prop. 11(a): exact rational N=16 boxes | ~2 s |
| `slope_certificate.py 7 9 40` | `data/slope_certificate_7_9_40.json` | Prop. 11(b): 40 slope cells on [7,9] | ~100 s |
| `deadline_validated.py` | `data/deadline_validated.json` | Appendix A: interval Taylor PGF enclosures | ~80 s |
| `check_paper.py` | `data/paper_checks.json` | Exact replay of every printed certified constant; must end with `ALL CHECKS PASSED` | ~30 s |
| `diagnostics.py` | `data/diagnostics.json` | Floating-point diagnostics N=2..128, variances, clocks, slope sweep | ~13 min (N=128 dominates) |
| `make_figures.py` | `figures/fig_summary.*`, `figures/fig_robustness.*` | Renders saved data only | seconds |
| `sanity_boundary.py` | stdout | Floating check of inequality (20) and of the generator bound | seconds |
| `search_reversal.py`, `search_reversal2.py [seed]` | stdout | Diagnostic search for an extinction reversal under state-dependent division (none found) | minutes |

`deadline_validated.py` is a copy of the workspace producer
(`problem_workspaces/RAF_intracellular_memory_to_heritable_phenotype/experiments/`)
with only the output path changed. Lean sources: `proofs/PhenotypeMemory/` (root
declaration `PhenotypeMemory.continuation_finite_certificate`); they were not recompiled
for this paper and cover only the items listed in Section 9 of the paper.

## What is new relative to the 12-page workspace manuscript (20 Sept 2026)

* Full proofs of the direction theorem (three lemmas), construction lemma.
* Corollary 6: second factorial moment equation and variance ordering.
* Proposition 7: strictness dichotomy (irreducible Q, nonconstant d).
* Proposition 8: exact cone obstruction for state-dependent division; negative reversal search.
* Proposition 11(b): certified gap > 0.0128 uniformly on the slope interval [7,9].
* Theorem 12: balanced founders die out as N→∞ under a smooth readout, rate N^(-γ), via
  Feynman–Kac/first moments (replaces the supplement's coupling sketch; quantitative).
* Theorem 15 sharpened with the tight rational boxes: eventual hit-300 gap 0.059 → 0.098,
  hit-300-by-300 gap 0.054 → 0.084 (coarse Lean-checked constants retained in the proof).
* Corollary 16: binomial capture / barcode observation; Hoeffding sampling radius.
* Notation: matrix 𝓗 vs deadline H; gap g; weight ν; Taylor step Δ.
