# Functional viability and paired recovery — arXiv source package

Manuscript: *When can a negative recovery assay exclude a recoverable
subpopulation? Sharp coverage, stage mismatch and allocation bounds for paired
observations*, 17 September 2026, 19 pages, 3 vector figures, 4 tables,
14 references. The author and affiliation macros (`\PaperAuthor`,
`\PaperAffiliation` at the top of `main.tex`) are intentionally empty.

Built PDF: `../Functional_Viability_Paired_Recovery.pdf` (identical to
`main.pdf` here).

This article supersedes the nine-page workspace report in
`problem_workspaces/RAF_AssaySept17_antimicrobial-tolerance_and_functional_viability/`
(`publication/manuscript.tex`). It keeps that paper's theorem chain and its
synthetic planning example and adds the results developed for this release:

| Addition | Where | Status |
|---|---|---|
| Coverage floor on the full range `0 ≤ c ≤ 2`, sharp | Thm 4.1, Cor 4.2–4.3 | newly Lean-verified |
| Sharpness of the approximate-complementarity corollary | Cor 4.5 | newly Lean-verified |
| Exact three-regime allocation profile `M(w;c,d)`, with strictness and plateau | Thm 5.1, Cor 5.2–5.3 | newly Lean-verified |
| Mean-square mismatch budget replacing the uniform bound | Thm 6.1 | newly Lean-verified |
| Exact finite-feasibility characterization incl. the `θg = 1` edge case | Thm 8.1 | newly Lean-verified |
| Adaptive reallocation gives no gain | Thm 9.1 | conventional |
| Finite-follow-up identified set, timing rescaling | Prop 3.1–3.2 | conventional |
| Confidence inversion, margin asymptotics | Prop 8.3–8.4 | conventional |
| Full-range planning row (`c = 1.5`: 750 units instead of 2,300) | Table 2 | exact arithmetic |

The earlier draft's restriction to `c ≤ 1` implied a hard ceiling `g ≤ 1/4`.
That ceiling is an artefact of the domain, not a theorem: `c` bounds a *sum* of
two probabilities. Removing it is the substantive mathematical change here, and
it changes a planning answer by a factor of three.

## Files

| File | Role |
|---|---|
| `main.tex` | manuscript source (11pt article, natbib numbers, `plainnat`) |
| `references.bib` | all 14 references |
| `planning_rows.tex` | generated; macro `\planningrows` holding the five rows of Table 2 |
| `figures/floor_range.pdf` | Figure 2: the sharp floor on the full coverage range |
| `figures/allocation.pdf` | Figure 3: exact allocation profile and the plateau regime |
| `figures/design.pdf` | Figure 4: units required, and the cost of a closing margin |
| `check_paper.py` | recomputes every printed constant and regenerates all figures |
| `results.json` | generated; exact rationals and numerical values |
| `main.bbl` | generated; include it in an arXiv upload alongside `references.bib` |
| `lean/*.lean` | the eight proof modules, copied verbatim from `proofs/FunctionalViability/` |
| `verification/*.verify.json` | strict verification receipts (command, hashes, axioms, elaborated statements) |

Figure 1 is inline TikZ; there is no external file for it.

## Rebuild

From this directory, with the repository Python and MiKTeX on `PATH`
(`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`):

```bash
python check_paper.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

`check_paper.py` runs 476 assertions and exits non-zero on any failure. A clean
build has no `!` lines, no overfull/underfull boxes and no undefined references
in `main.log`; check that, because a full disk makes pdflatex silently drop
`main.aux` and ship a PDF full of `??` references.

## Lean verification

Environment: Lean 4.30.0, repository-pinned Mathlib
(manifest SHA-256 `a8df0b606ec258561c226df89856884be433c19b49fb0a27335d69bb2b6e9fac`),
strict compilation with `-DwarningAsError=true`. No `sorry`; every exported
declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

```powershell
$ResearchPy = Join-Path 'E:\Erdos Problems' '.venv/Scripts/python.exe'
& $ResearchPy scripts/verify_proof.py proofs/FunctionalViability/ExtendedCoverage.lean `
    --timeout 900 --declaration FunctionalViability.Robust.moment_calibrated_certificate
& $ResearchPy scripts/verify_proof.py proofs/FunctionalViability/DesignLimits.lean `
    --timeout 900 --declaration FunctionalViability.Robust.allocation_profile
```

| Module | SHA-256 | Verified | Roots exported |
|---|---|---|---|
| `ExtendedCoverage.lean` | `3c7aef3bf6178b084e794d53316b78a451e41d9f5b92e994686676f33c9f8a10` | true, 19.9 s | 9 declarations incl. `moment_calibrated_certificate` |
| `DesignLimits.lean` | `86d0340d5f67e8eb441fb8c248dbd505eb688b4ab58b90917a3a74fb3ef26f61` | true, 24.6 s | 5 declarations incl. `allocation_profile`, `finite_feasibility` |
| `RobustCertificate.lean` | `c29773c75fc4b03da6bb07b6cb6f6344fbcbd92ff9df372c7f7c72007d9306c6` | true, 112.4 s | `calibrated_robust_certificate` (previous root, unchanged) |

`BalancedSampling.lean`, `CoverageBounds.lean`, `RecoverySource.lean` and
`Sampling.lean` are compiled as source-bound dependencies of those roots; their
hashes are recorded inside the receipts. `Resolution.lean` is the original
campaign's root and is retained as a regression (the 100-unit rational example,
minimum random sample 79, balanced 80).

### What is compiled and what is not

Compiled: the coverage lower bound on `0 ≤ c ≤ 2` and its attaining witnesses;
maximin and the reduction to the restricted formula; the `c-1` high-coverage
bound; the approximate-complementarity bound *and* its attaining witness; the
allocation profile (lower bound plus attainment), its strictness and its
plateau; the mean-square population floor with recording and exceptional mass;
the normalized source paths, the balanced likelihood identity and inequality;
the calibration composition; the finite-feasibility equivalence.

Conventional (proved in the paper, not in Lean): the finite-follow-up identified
set and the timing-rescaling statement; the explicit sharpness *constructions*
for the population floor and the calibrated certificate (exceptional mixture and
bad environments); the logarithmic sample-size formulas and their sandwich; the
confidence-interval inversion; the margin asymptotics; the adaptive-policy
argument; everything in Section 11.

Table 4 of the paper states this split; keep the two levels distinct when
citing. A compiled inequality does not validate a biological interpretation, and
a conventional proof is not thereby weaker.

## Numerical checks

`check_paper.py` verifies, among 476 assertions:

* `R_full = R` on the whole restricted range, and `R_full ≥ c-1` for `c > 1`;
* the equal-allocation floor and the three-branch profile against an independent
  brute-force minimisation over the admissible source set, over
  `c ∈ [0,2]`, `d ∈ [0,1]`, `w ∈ [0,1]` — maximum gap `1.3e-11`, always from the
  correct side;
* the mean-square bound on 4,000 random finite mixtures, plus its attaining
  constant types and the two pooled-summary counterexamples;
* the four planning rows and the full-range row, with the neighbouring integer
  powers checked in exact rational arithmetic (2,299 fails, 2,300 succeeds);
* the endpoint `p_U ≈ 0.00999606` at `n = 2300`;
* the margin asymptotic ratio `→ 1` as `d ↑ c`;
* the invariance of the all-negative mass under arbitrary allocation weights,
  which is the algebraic content of Theorem 9.1.

## Pitfalls hit while building this package

* A TikZ style named `pos` collides with TikZ's own `pos` key and aborts the
  build with a `pgfkeys` error. Style names `hit`/`miss` are safe.
* matplotlib mathtext rejects `\le`; use `\leq` in figure titles.
* Long Lean identifiers overflow a `tabularx` column; `\allowbreak` after each
  escaped underscore plus a fixed-width first column fixes it without
  hyphenating identifiers.
* The Lean `unusedVariables` linter is an *error* under `-DwarningAsError=true`,
  so an unused hypothesis fails the build. Two hypotheses (`c ≤ 2` in the
  coverage bound, the rectangle bounds in `clipped_core`) turned out to be
  genuinely unnecessary and were removed rather than silenced.
* `|2*w-1|*c` lexes as the token `|*`; write `|2*w-1| * c`.
