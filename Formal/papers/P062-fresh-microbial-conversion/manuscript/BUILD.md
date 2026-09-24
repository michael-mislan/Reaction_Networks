# Build and submission notes

**Paper.** *Certifying fresh microbial conversion from finite challenge
records: a sharp two-pool material bound.* 24 pages. Author and affiliation
fields are intentionally left blank.

## Files

| Path | Role |
|---|---|
| `main.tex` | The manuscript. Self-contained: bibliography is an inline `thebibliography`, so no BibTeX pass is needed. |
| `refs.bib` | The same six references in BibTeX form, for convenience if the bibliography is ever switched to BibTeX. Not used by the current build. |
| `figures/reserve.pdf`, `figures/budget.pdf`, `figures/ambiguity.pdf` | The three included vector figures. Figure 1 is inline TikZ and needs no file. |
| `figures.py` | Regenerates the three PDFs from exact rational evaluations of the certificate. Needs `matplotlib` only. |
| `check_paper.py` | Standard-library-only exact-rational audit of every printed number, plus a replay of the attaining schedule. |
| `companion/proofs/*.lean` | The six Lean modules in namespace `MicrobialFunctionAssay`. |
| `companion/verification/verification_summary.json` | Compact per-module receipt summary (toolchain, manifest hash, file SHA-256, declaration list, axiom report). |
| `companion/calculator.py` | The exact-rational decision calculator described in Appendix A. |

## Building

MiKTeX binaries on this machine live under
`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`.

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

Three passes are needed for the table of contents and forward references. The
build is clean: no overfull or underfull boxes, no undefined references or
citations. **Always check the log** — a full disk makes pdflatex silently drop
`main.aux` and emit a PDF full of `??` references.

Packages used: `geometry`, `fontenc`, `inputenc`, `lmodern`, `amsmath`,
`amssymb`, `amsthm`, `booktabs`, `array`, `longtable`, `graphicx`,
`microtype`, `tikz` (libraries `arrows.meta`, `positioning`, `calc`),
`hyperref`. All are standard on arXiv.

## arXiv submission

Upload `main.tex` together with the `figures/` directory. Nothing else is
required: there is no `.bbl`, no BibTeX pass, and all figure paths are
relative. `refs.bib`, `figures.py`, `check_paper.py` and `companion/` are
development and reproducibility material, not part of the TeX build; ship them
as a separate archive or repository link.

Before an actual submission, fill in the author, affiliation, licence,
acknowledgements and a permanent code/version reference, and pick the subject
categories after checking the current definitions. Suggested primary category:
`math.OC` (optimization and control), with cross-lists to `q-bio.QM`
(quantitative methods) and `cs.LO` (logic in computer science, for the formal
verification component).

## Regenerating the artifacts

```bash
python figures.py     # rewrites figures/*.pdf
python check_paper.py # exact audit; prints the two counts quoted in Appendix A
```

At the time of writing `check_paper.py` reports:

```
70 printed values reproduced exactly.
73984 exact-rational attainment replays agreed with both forms of L.
```

## Re-verifying the Lean development

From the research repository root (`E:\Erdos Problems`), using its pinned
Lean 4.30.0 / Mathlib workspace:

```bash
./.venv/Scripts/python.exe scripts/verify_proof.py \
  proofs/MicrobialFunctionAssay/Sharpness.lean \
  --declaration MicrobialFunctionAssay.lower_closed \
  --declaration MicrobialFunctionAssay.lower_attained \
  --declaration MicrobialFunctionAssay.lower_is_minimum \
  --declaration MicrobialFunctionAssay.lower_sound_uptake \
  --declaration MicrobialFunctionAssay.prewash_reserve_from_uptake \
  --declaration MicrobialFunctionAssay.uptake_source_bound \
  --declaration MicrobialFunctionAssay.uptake_bound_attained \
  --output problem_workspaces/RAF_Assays_microbial_function_challenge/verification/Sharpness.verify.json
```

and analogously for `Source.lean`, `Certificate.lean`, `Resolution.lean`,
`Design.lean` and `Sensitivity.lean`. All six verified with
`verified: true`, exit code 0, toolchain `leanprover/lean4:v4.30.0`,
`-DwarningAsError=true`, and axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`.

## What is new here relative to the earlier workspace manuscript

The earlier nine-page manuscript in
`problem_workspaces/RAF_Assays_microbial_function_challenge/publication/`
carried the sharpness construction and the uptake-cap extension as
*conventional* arguments only. Both are now machine-checked:

* `Sharpness.lean` adds `lower_closed` (remaining-stock form),
  `lower_attained` (attaining schedule from any admissible initial split) and
  `lower_is_minimum` (`IsLeast`), so exactness is no longer a paper-only
  claim; and `lower_sound_uptake`, `prewash_reserve_from_uptake`,
  `uptake_source_bound`, `uptake_bound_attained`, which make the
  "bounded uptake replaces direct reserve measurement" route a verified
  theorem, together with its own exactness.
* `Sensitivity.lean` adds `reserve_tolerance` (the exact `L(J)` line),
  `wash_curve_slack` / `improvement_criterion_slack` /
  `target_criterion_slack` (the joint activity-and-reserve-slack budget, which
  previously existed only as a hand-checked table), and the two material
  counterexamples `storage_counterexample`,
  `initial_reserve_substitution_unsound`, `uptake_route_sound_here` and
  `reserve_premise_not_redundant` as explicit `History` witnesses rather than
  as prose.

Wording was also tightened against the supplemental review: the target is
"fresh credited inventory" throughout; the five entries of `L` are described
as a maximum of five affine lower bounds rather than five irredundant facets;
the claim that a pre-wash reserve measurement is mandatory is replaced by the
correct statement plus the uptake substitute; the principal threshold is
$F_\star = 1.6$ consistently, with the calculator's $1.5$ regression default
called out explicitly; the $0.17$ $\mu$mol wash margin is stated next to the
reserve-slack condition that it requires; and the selective, cell-retaining
nature of the first collection is stated in the main text beside the worked
example.
