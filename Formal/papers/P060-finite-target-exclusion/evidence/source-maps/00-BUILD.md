# Build and evidence record

**Paper.** *When does a negative assay exclude a finite target count? Sharp
false-exclusion bounds for native-reference reporting rules.* 24 pages, author
block intentionally blank. Built 17 September 2026.

- Sources: `main.tex`, `formal_map.tex`, `references.bib`, `figures/`,
  seven generated `*_rows.tex` table fragments.
- Compiled PDF: `main.pdf`; a copy sits one level up as
  `../Specimen_Reliability_Finite_Count_Exclusion.pdf`.
- Suggested arXiv categories: `stat.ME` primary, `q-bio.QM` cross-list.

## Rebuilding

```powershell
E:\Erdos` Problems\.venv\Scripts\python.exe check_paper.py   # exact numbers + table fragments
E:\Erdos` Problems\.venv\Scripts\python.exe make_figures.py  # five vector figures
E:\Erdos` Problems\.venv\Scripts\python.exe make_anc.py      # arXiv ancillary directory
.\build.ps1                                                  # pdflatex -> bibtex -> pdflatex x2
```

`build.ps1` puts `TEMP`/`TMP`/`TMPDIR` on `E:\tmp` and then asserts that
`main.log` contains no undefined references, no overfull box, no rerun request
and no disk-space error, and that `main.aux` exists. This matters: when `C:` is
full, pdflatex does not fail — it silently drops `main.aux` and ships a PDF full
of `??`. The current build is clean with **no overfull and no underfull boxes**.

Do not pipe `build.ps1` through `2>&1` in Windows PowerShell 5.1. MiKTeX writes
an "you have not checked for updates" nag to stderr, and redirecting a native
command's stderr in 5.1 wraps each line in an ErrorRecord, which trips
`$ErrorActionPreference = 'Stop'` even though the build succeeded.

## Where the numbers come from

`check_paper.py` regenerates **every** number printed in the manuscript and
asserts each one. Its arithmetic policy:

- Exact `Fraction` arithmetic wherever the quantity is rational: the scalar
  maximum `G_m`, all of Tables 1, 2, 5, 6, 7, the familywise floor, the
  false-positive closed form, and the Clopper–Pearson control-pair count
  (`(1-1/300)^n <= 1/20` at `n = 898`, exact integers).
- Certified rational Taylor enclosures of `exp(-x)` for everything in the
  Poisson section, so each integer threshold in Table 4 is a *proved* decision
  (enclosure widths are asserted below `1e-12`). The alternating series has
  remainder of the sign of its first omitted term, so an even truncation bounds
  above and the next partial sum bounds below.
- Table 7's minimum pair counts are certified from both sides: an adaptive
  exact-rational bisection proves `max_p (2p-p^2)^m B(p) <= 1/20` at the stated
  `m` (bounding the increasing factor by its right endpoint and the quadratic by
  its exact maximum on each subinterval), and an exact rational witness proves
  the maximum exceeds `1/20` at `m-1`.
- The only double-precision quantity in the paper is the interior branch of the
  familywise formula `F_{m,T}(H)`, which carries a power `m/T` and is irrational
  by nature. Table 3 labels it. **No reachability claim depends on it** — those
  use only the exact floor `1-(1-H)^T`.

`results.json` holds the machine-readable output.

## Lean: what is mechanized and what is not

All four receipts below report `verified: true`, exit code 0,
`-DwarningAsError=true`, Lean `leanprover/lean4:v4.30.0`, mathlib manifest
`a8df0b60…`, and exactly the three standard axioms `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, extra axiom, native decision
procedure or numerical oracle. Compact summary in `anc/verification_summary.json`;
full receipts (0.2–0.9 MB each, mostly serialized binders) stay in
`problem_workspaces/RAF_AssaySept17_specimen_to_result_reliability/verification/`.

| Module | Status | New here? |
|---|---|---|
| `PolicyComparison.lean` (+ 9 modules it depends on) | re-verified 17 Sep 2026, 22.7 s warm | no |
| `BatchReporting.lean` | verified, 65.4 s | **yes** |
| `ObservationRobustness.lean` | verified, 61.0 s | **yes** |
| `PoissonReferences.lean` | verified, 59.3 s | **yes** |

Verification command (from the repository root `E:\Erdos Problems`):

```powershell
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/SpecimenReliability/BatchReporting.lean --timeout 900 --declaration SpecimenReliability.atLeastOne_law --declaration SpecimenReliability.batch_identity --declaration SpecimenReliability.batch_witness --declaration SpecimenReliability.batch_floor_exceeds --declaration SpecimenReliability.batch_witness_valid --output <receipt>.json
```

Substitute the module and its declarations for the other three. Note that
`--declaration` misbehaves when one requested name is a prefix of an earlier one,
so request `batch_witness` before `batch_witness_valid`.

### Mechanized

Section 2–6 core (source law, count monotonicity, sharp moment envelope, paired
reference law, feasible moments, complete-event identity, scalar maximum and both
its branches, the sharp calibrated bound with its attaining witness, the
three-pair corollary, availability comparison, the single-preparation comparator,
and the exact `K = 6` thresholds); the batch composition identity
`atLeastOne_law`/`batch_identity` and the floor witness `batch_witness`; the
two-specimen impossibility `batch_floor_exceeds`; the false-positive reduction
`fp_reduction` and bound `fp_bound` with the exact `κ = 1/300` and `κ = 1/250`
examples; and the Poisson comparison `poisson_pointwise` with the
`λ ≤ 1` guarantee `poisson_general`. Table 8 of the paper is the full map.

### Conventional (ordinary proofs, given in full in the paper)

Unequal allocation (§5.1); the extension from finite mixtures to arbitrary laws
on the unit square; the asymptotics of §6; the closed form of `F_{m,T}` and the
limit in Corollary 7.2; the FDR and retry arguments (§7.4); Proposition 9.1 and
its five-point critical set; the concave-envelope reduction Theorem 8.2, its
chord criterion Corollary 8.3 and the sharpness witness; the sharpness half of
Proposition 9.2; and Theorem 10.1 with Corollary 10.2.

### Empirical (unvalidated)

Representative material loss; native-reference transport across preparation
volumes, matrices and target forms; independence across experiments; conditional
target marks; counted reference inputs; accurate terminal observation; absence of
competition. No biological data are fitted anywhere. The error statement is for
one complete campaign-and-specimen event — not posterior absence, not conditional
error given a passed gate, and not unlimited reuse.

## What changed relative to the 11-page workspace edition

The core (Sections 2–6) is the earlier paper's, with the exposition tightened.
Everything from Section 7 on is new, and three of the supplement's proposed
results were corrected or strengthened in the process:

1. **Poisson transport, corrected proof.** The supplement justified
   `w_λ ≤ w` for `λ ≤ 1` by `1-e^{-λt} ≤ λt ≤ t`, which compares the Poisson
   acceptance against `X+Y` rather than against `X+Y-XY` and therefore does not
   prove the claim. The claim is true; the proof needs `1-t ≤ e^{-t} ≤ e^{-λt}`.
   That is the proof now in Proposition 8.1, and it is what `poisson_pointwise`
   mechanizes.
2. **Poisson sharp regime, widened and shown sharp.** The supplement gave the
   closed form under the curvature condition `λ ≤ a(K-1)`. The exact condition is
   that the concave envelope be a chord, namely `Ka/λ ≥ (1-J)/d_λ`, which is
   strictly weaker — at `K = 6, a = .45` it extends the range from `λ ≤ 2.25` to
   `λ ≤ 2.68`, and the table's `λ = 5/2` row lives in the gap. It is also exactly
   the right condition: at `λ = 3` a certified two-point source exceeds the chord
   value. The general case is closed by Theorem 8.2 rather than left open.
3. **False positives, closed form.** The supplement left the sharp value as an
   unevaluated maximum. It reduces exactly to the original scalar problem with a
   rescaled parameter, giving `A_κ G_m(H_κ)` in closed form, hence the concrete
   specificity budget `κ ≤ 1/300` and the 898 control pairs needed to certify it.

Two results are new outright: the exact familywise value with its floor
(Section 7), and the observation that equal means plus nonnegative covariance
move the feasibility threshold from `(1-a)^K` to `(1-2a)^K` (Section 10), which
turns the `K = 2` impossibility into a 38-pair cost.

## arXiv packaging notes

- `anc/` carries the thirteen Lean sources, `check_paper.py`, `make_figures.py`,
  `results.json`, `verification_summary.json` and a SHA-256 inventory.
- `main.bbl` is generated by the build and should be shipped alongside
  `references.bib`; its stem matches `main.tex` as arXiv requires.
- Figures are vector PDFs; no raster assets.
- Author, affiliation and licence are deliberately unset.
