# Build notes: reliable copying of chemical states

Source files in this folder:

- `main.tex` — preamble, abstract, `\input`s. Author, affiliation and date are the
  three `\newcommand` macros at the top (`\PaperAuthor`, `\PaperAffiliation`,
  `\PaperDate`). Long Lean identifiers are typeset with `\lean{...}` (a
  `url`-style command that breaks at `_` and `.`).
- `sec_intro.tex`, `sec_events.tex`, `sec_constructed.tex`, `sec_redundancy.tex`,
  `sec_semenov.tex`, `sec_discussion.tex` — main text, Sections 1–6.
- `app_verification.tex`, `app_source.tex`, `app_semenov.tex` — Appendices A–C.
- `refs.bib` — bibliography (`plainnat`, numeric); `main.bbl` is generated and must
  be uploaded with the sources for arXiv.
- `check_constants.py` — standard-library Python; re-derives every constant printed
  in the text in exact rational arithmetic and writes `fig_lineage.dat` and
  `fig_family.dat`, the data of Figure 2 (read by pgfplots).
- `terminal_regions.json` — exact rational centres and metrics of the two Semenov
  return regions (Section 5, Appendix C), copied from the research workspace.
- `build.ps1` — the full build chain below.

Compiled output is copied to `..\Reliable_Chemical_State_Copying_Finite_Molecule_Guarantees.pdf`
(28 pages, 13 September 2026).

## Compiling (MiKTeX, user scope, not on PATH)

```powershell
$env:Path = "$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64;$env:Path"
py check_constants.py
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

Packages used beyond the base set: `pgfplots` (already installed), `tikz`,
`natbib`, `longtable`, `booktabs`, `enumitem`, `url`, `hyperref`. The last build had
no errors, no overfull or underfull boxes and no undefined references.
Alternative single-pass engine: the Tectonic binary bundled with the Codex LaTeX
plugin (`%USERPROFILE%\.codex\.tmp\bundled-marketplaces\openai-bundled\plugins\latex\bin\tectonic.exe -X compile main.tex`).

## Sources of the mathematical content

| Paper part | Origin |
|---|---|
| Sections 2, 3, 5, Appendix C | `problem_workspaces\RAF_Compositional_Inheritance` (handoff, `paper\research_paper.tex`, `FINITE_DRIVE_MODEL.md`, `SEMENOV_MODEL.md`, `MEASURED_RECOVERY_ROUTE.md`, `experiments\certificates\*`) and the PDF `CompositionalInheritability_Reliable_Chemical_State_Copying.pdf` |
| Section 4, Appendix B | `problem_workspaces\RAF_compositional_memory_scaling\paper\*.tex` and the PDF `Logarithmic_Molecular_Redundancy_for_Compositional_Inheritance_Prehardening.pdf`; local four-species certificates from `Constructive_Finite_Volume_Bounds.pdf` (FiniteCopy Lean modules) |
| Lineage/family iteration, complementary partition | shared by all three feeder manuscripts; `Quantitative_Inheritance_of_Chemical_Composition.pdf` (single-module version, not otherwise used) |

Deliberately left out (available for a separate supplemental report): the campaign
ledgers and failed routes, the earlier forward-mechanism certificates (N=25, N=47),
the single-module `HeritableCompositions` theorem with its own constants, the
infinite faithful-branch (Galton–Watson) result, the two-founder differential
reproduction comparison, switching/depletion time bounds of the FiniteCopy paper,
the experimental-design diagnostic, the SSA pilots, and all biomedical proposals.

## Lean verification status (see Appendix A of the paper)

Toolchain `leanprover/lean4:v4.30.0`, frozen `mathlib4_project\lake-manifest.json`
(SHA-256 `a8df0b60…`). Receipts live in the workspace `verification\` folders.

| Root | Receipt | Current tree |
|---|---|---|
| `proofs\CompositionalMemory\ReversibleCertificate.lean` (Thm 3.1) | strict pass, 281 s, 174 deps, source `f7578b15…` | all 174 dependency hashes match (re-audited 13 Sep 2026) |
| `proofs\CompositionalMemory\SemenovMeasuredEncoding.lean` (Thm 5.1) | strict pass, 28 s, 130 deps, source `0e693560…` | all 130 dependency hashes match |
| `FiniteEventQuota`, `FiniteQuotaTransport`, `ReversibleDivisionInventory` | strict pass | match |
| `proofs\CompositionalMemory\Publication.lean` (Section 4 entry point) | strict pass 10 Sep 2026, 320 deps, source `d0e0403d…` | **re-verified 13 Sep 2026** after the repair below: strict pass, 1984 s, 316 deps, all hashes match; receipt `problem_workspaces\RAF_compositional_memory_scaling\Publication.reverify-2026-09-13.verify.json`; the four exported declarations use only `Classical.choice`, `Quot.sound`, `propext` |

Repair performed on 13 Sep 2026: `CoupledLocalGenerator.lean` had been overwritten on 10 Sep 23:14 by a same-named module of the constructed-source campaign. The original (recorded source hash `fb6737fd…`) was reconstructed byte-exactly by replaying the `apply_patch` records of the Codex transcript `E:/CodexData/home/sessions/2026/09/10/rollout-2026-09-10T05-45-21-01a08b59-ee4d-7cf0-a654-31e5fcefad5e.jsonl`, saved as `proofs\CompositionalMemory\ScalingLocalGenerator.lean`, and the two importers (`SourceLocalGenerator.lean`, `CountBinding.lean`; neither is a dependency of the constructed-source roots) were repointed to it. Note also that the whole `proofs\CompositionalMemory\` directory is untracked in git
(`git status` shows `??`), so none of the roots is protected by version control yet.

## Numbers checked for this version

`check_constants.py` asserts: the pre-monitor bound 0.991028, the reverse-growth
loss 0.000848, the quota tail bound < 2e-7, the final 0.9901518, 0.9901^10 > 0.905296,
0.992^10 > 0.922819, the capacity 100,100,212,000 ≈ 0.1662 pmol (6.65 pmol for four
pools × ten cycles), the initial inventory 213,801, the birth volume 0.0880 fL, the
Semenov volume 39.85294 µL, the refill means 1.82772e18 and 5.48316e18 < K/2, the
cap margin, and the sufficient-N values plotted in Figure 2.

## arXiv submission

Upload `main.tex`, the nine `sec_*.tex`/`app_*.tex` files, `refs.bib`, `main.bbl`,
`fig_lineage.dat`, `fig_family.dat`. Set the author macros first. Suggested
categories: q-bio.MN (primary), math.PR, physics.chem-ph; cs.LO for the formal
verification component.

## Items to settle before submission

- Author list, affiliation, acknowledgements.
- Commit the Lean sources and produce a public tag/DOI so that the receipt hashes
  quoted in Appendix A can be checked against a public artifact.
- Optionally publish `terminal_regions.json` and the polynomial certificate data
  as ancillary files.
