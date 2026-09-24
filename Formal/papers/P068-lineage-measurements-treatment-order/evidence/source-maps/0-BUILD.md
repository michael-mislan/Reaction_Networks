# Build and verification

Paper: *When single-lineage measurements fail to determine treatment order:
sister dependence, branching extinction, and decision-focused assays* (26 pp).
Compiled output is copied to
`key_results/RAFs/Single_Lineage_Measurements_Treatment_Order.pdf`.
The author/affiliation block is intentionally blank.

## Files

| Path | Role |
|---|---|
| `main.tex` | the manuscript |
| `refs.bib`, `main.bbl` | bibliography source and the compiled `.bbl` (arXiv needs the `.bbl`) |
| `figures/protocol.pdf`, `figures/boundary.pdf`, `figures/epsilon.pdf` | the three vector figures |
| `scripts/exact_engine.py` | exact phase-wise exponential integrals; computes both reserves |
| `scripts/check_paper.py` | replays every constant in the paper; **must print `ALL CHECKS PASSED`** |
| `scripts/figures.py` | regenerates the three figures |
| `certificates.json` | written by `check_paper.py`; labelled dump of every constant |

## Build

```bash
pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex
```

MiKTeX binaries on this machine are under
`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`. A clean build reports zero
errors and zero warnings; assert that before shipping, because a full disk
silently makes `pdflatex` drop `main.aux` and produce a plausible-looking PDF
with broken cross-references.

## Verification

```bash
python scripts/check_paper.py
python scripts/figures.py
```

`check_paper.py` performs 82 assertions in exact rational or symbolic
arithmetic and prints them individually. Rerun it after **any** edit that
touches a number. It needs `sympy`; `figures.py` additionally needs `numpy` and
`matplotlib`. The numerical ODE cross-check quoted in Appendix B (the true
linear response `≈ .0035` against the reserve `≈ .0057`) used `scipy`
`solve_ivp` with `DOP853`; it is a diagnostic only and no proof depends on it.

## arXiv submission

Include `main.tex`, `refs.bib`, `main.bbl` and `figures/`. Exclude `*.aux`,
`*.log`, `*.out`, `*.blg`. `scripts/` and `certificates.json` are ancillary
material: either drop them or move them to an `anc/` directory, which arXiv
carries alongside the paper without feeding it to TeX.

## What changed relative to the earlier 13-page version

New mathematics, all in §5 unless noted:

- **Lemma 5** (monotonicity in `ε`) and **Lemma 6** (two criteria for the
  supersolution condition). Criterion (b) is sharp at
  `x_flat = ((√5−1)/2)^(1/2) = .7861513…`, and `x_flat < x_0 ≈ .80120`, so it
  covers *every* pulse length at which the reversal exists — which is what
  makes Corollary 23 hold for an arbitrary descendant offspring law rather
  than only for the specific persistent kernel.
- **Proposition 9** (sensitivity reserve `W_a`), replacing the occupation
  reserve `V_a`. `V_a/W_a` is 8.4–8.9 for the pulse schedules and 25–31 for the
  constant ones. The `V_a` column of Table 3 reproduces the previously
  published constants exactly, which is the check that the new quantity is a
  refinement of the old one and not a different object.
- Combined with the one-sided band from Lemma 5, this gives `ε ≤ 1/30` at
  `c = ∓1/5` (was `1/500`), `ε ≤ 1/16` at `c = ∓1/4`, and **Theorem 14**:
  the whole range `0 ≤ ε ≤ 1` at `h = log(50/49)`, against `h ≤ 10⁻⁶` before.
- **Corollary 13** (uniform decision band), half-width `≈ 11 h ε`, replacing
  the legacy `16000 h`.
- `ε ≤ 1/4` for the separated 40-division theorem (was `.001`);
  `ε ≤ 1/100` for the full-class rules, with `m = 800` now clearing the .95
  resolution target that previously needed `m = 1600`.
- **Proposition 21** (calibration-free declarations at finite pulse length) and
  **Proposition 22** (additive reserve for correlated read errors).

Editorial: plain-language synopsis, explicit sign conventions, a decision-task
map, a table of what the new certificates change, a protocol-correspondence
checklist, and a reproducibility appendix. The two unciteable references of the
earlier version ("Companion manuscript", "Project briefs") are replaced by an
explicit provenance paragraph in Appendix D. Note that
Gunnarsson–Magnússon–Foo is no longer a preprint: it appeared as *npj Syst.
Biol. Appl.* **11**(1):98 (2025), doi:10.1038/s41540-025-00571-5.
