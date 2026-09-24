# Compatibility of competing biochemical modules: capacity, recovery, and finite operation

arXiv-style source package. Author/affiliation macros at the top of `main.tex`
(`\PaperAuthor`, `\PaperAffiliation`) are intentionally blank.

## Build

    bash build.sh        # clean build in a temp dir; copies main.pdf/main.bbl/main.log here
                         # and the titled PDF to the parent folder; prints "LOG NOT CLEAN" on
                         # overfull boxes / undefined references

or manually: `pdflatex main; bibtex main; pdflatex main; pdflatex main` (MiKTeX).
Do NOT patch `main.tex` through bash heredocs or non-raw Python strings: they eat
`\`, `\t`, `\b` (this bit us three times while writing the paper).

## Contents

| Path | Role |
|---|---|
| `main.tex`, `refs.bib`, `main.bbl` | manuscript source |
| `figures/*.pdf` | vector figures (`scripts/make_figures.py`) |
| `data/modal_box.json` | exact rational certificate (M, M^-1, c, A, b, n); SHA-256 `09ff83c3...c3f8`, identical to the workspace copy |
| `data/tube_nominal.json`, `tube_Q120.json`, `tube_Q60.json` | moving-tube certificates (times, references, radii as rational strings) |
| `data/*_summary.json` | verified outcomes of each tube certificate |
| `data/preparation_geometry.json` | exact tolerance calculations of Section 4.4 |
| `data/donor_threshold_numeric.json` | NUMERICAL ONLY: threshold stock ~70.9 microM, lifetime 1.387 s |
| `scripts/depleted_tube.py` | `build V name` / `verify name`; verify uses only ints/Fractions |
| `scripts/preparation_geometry.py`, `make_figures.py`, `donor_threshold_numeric.py` | supporting computations |
| `lean/SaturatingDonorBounds.lean` | new Lean file (copy of `proofs/DynamicSharedResource/`), receipt in `verification/` |

## Evidence levels used in the paper

* **Lean**: Theorem 4.2 (`fast_joint_service`, `proofs/DynamicSharedResource/OperationalMain.lean`),
  source-perturbation margins, stationary equivalence + repair-velocity lemmas,
  saturating-donor algebra (new, verified 2026-09-19, Lean 4.30.0, Mathlib c5ea0035).
* **Exact (not kernel-checked)**: Theorem 5.3 (120 microM succeeds, 60 microM fails) and the
  finite-horizon part of Corollary 4.3 (0.1% independent preparation box).
  Replay: `python scripts/depleted_tube.py verify tube_Q120` (about 20 s each).
* **Conventional**: Lemma 4.1 (moving centre), Props 2.1, 3.3, 3.4 (log form), Thms 4.4, 5.1, Cor 5.2 flows.
* **Numerical**: trajectory curves, repair-clock crossings, 70.9 microM threshold.

## What changed relative to the 12-page draft `dynamic_shared_resource.pdf`

* Reframed as capacity / recovery / duration; stationary theory attributed to the companion paper.
* New: exact moving-tube certificates. Linear-law stock 1.93 M -> 120 microM (certified), 60 microM
  certified insufficient; source provably below the stationary threshold s_min for t >= 0.434 s
  while both quotas hold; 0.70-0.75 microM drawn from storage.
* New: independent preparation tolerance 0.5 pM -> 0.1% relative in every coordinate
  (Cor 4.3), handing off to the Lean theorem once the tube slice is inside S (t* = 0.2477 s).
* New: saturating donor corollary with Lean-checked algebra; general storage and hidden-clock
  propositions; general moving-box lemma; preparation-geometry analysis (binding direction is the
  fast e2 mode, not chemistry).
* Corrected wording: Omega(1/sigma) necessary delay (not O(1/sigma)); "approximately separates
  modes" (not diagonalizes); commands in verbatim; bibliography expanded 3 -> 27 entries, all DOIs
  checked against Crossref.
* The certificate-hash discrepancy in the guidance note is a stale remote copy: the local
  `certificates/modal_box.json` hashes to the value printed in the paper.
