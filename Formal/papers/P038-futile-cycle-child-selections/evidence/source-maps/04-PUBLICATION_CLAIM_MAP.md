# Publication claim map

14 September 2026. Original DET/NEG/POS guide: **48/48 PASS**, preserved.
Postproof results are additional statements, not a reopened original frontier.

## Definitions and source reconciliation

`Child` selects distinct species and distinct reactant-supported reactions. The
owned reaction supplies the corresponding column, so deleting owners gives a
principal restriction. `MinimalUnstable` requires an eigenvalue of positive real
part for the matrix and no such eigenvalue for any proper principal restriction.
`DNonUnstable` quantifies over all strictly positive column scalings.
Noninstability permits zero eigenvalues. Dimension-minimal among all children and
principal-minimal are different properties. Determinant sign is preserved by
positive column scaling. A sign-conjugate Metzler matrix is a spectral device,
not an assertion that the original chemical child is Metzler.

The final conjecture of Supplementary Example D in Vassena–Stadler,
[arXiv:2308.11486v3](https://arxiv.org/html/2308.11486v3), is distinguished from
its displayed dual-cycle positive motifs. The determinant assertion is confirmed;
the all-positive extrapolation is refuted. Literal unbounded size does not
refute classification up to subdivision. The separate full-network example
uses saturating kinetics and makes no mass-action or oscillator claim.

## Claim-to-evidence table

All proof paths below are relative to the repository root. Publication paths are
relative to this directory, except the root receipt in its parent.

| Paper claim | Exact supporting evidence | Status |
| --- | --- | --- |
| Theorem 1.1 / 3.2: every elementary enzyme-conversion child has determinant 0, ±1 | `proofs/FutileCycle/Resolution.lean`, exports `FutileCycle.resolution`, `FutileCycle.allN_child_det`; `../PostproofRoot.verify.json` | Lean PASS |
| Six-species ordinary negative core in every n≥3 source; det=1 | Root export `FutileCycle.negative_core_all_n`, same fresh receipt | Lean PASS |
| Positive child of dimension 2n+1 for every n≥2; det=1; proper restrictions D-nonunstable; literal size unbounded | Root export `FutileCycle.positive_core_all_n` and `resolution`, same receipt | Lean PASS |
| Proposition 5.2: full positive child has a positive real eigenpair for every positive scaling and stays principal-minimal | `proofs/FutileCycle/PositiveAllRates.lean`; exports `FutileCycle.positive_all_rates`, `FutileCycle.positive_all_rates_minimal`; `PositiveAllRates.verify.json` | New Lean PASS |
| Theorem 4.2: source-realized five-species child is D-unstable and every proper restriction is D-nonunstable, all n≥3 | `proofs/FutileCycle/NegativeFiveMinimality.lean`; exports `FutileCycle.negativeFive_core_all_n`, `FutileCycle.negativeFive_scaled_unstable`; transitive `NegativeFive.lean`; `NegativeFiveMinimality.verify.json` | New Lean PASS |
| B has determinant −1, BD* has determinant −4; quintic and exact two-RHP-root count | `exact_certificates.json`, negative section; exact Routh column plus positivity of polynomial coefficients | Exact algebra + conventional proof; determinant sign and exact root count are not separately exported Lean declarations |
| B is strictly stable at unit scaling | Existing `ExceptionalRestriction.lean`, included in the fresh root dependency closure; Q positive definite and BᵀQ+QB=−218I reproduced in `exact_certificates.json` | Existing Lean dependency + exact algebra |
| Six-species ordinary minimality differs from D-minimality | Five-species proper D-unstable child combined with original root; paper Section 4 | Conventional immediate consequence of compiled statements |
| Theorem 5.3: scalar return equation identifies the spectral abscissa, including added losses | Eigenvector propagation and modulus comparison in paper | Conventional proof |
| Corollaries 5.4–5.5: strict individual rate monotonicity, homogeneous scaling, min/max bounds, exact added-loss threshold | Monotone scalar equation and eigenvalue shift | Conventional proof |
| Proposition 6.1: decreasing αn→0, finite Lambert brackets, stated error estimate and logarithmic equivalent | Elementary logarithm inequalities and increasing scalar equation | Conventional proof |
| Six-value table and n=10 example with three RHP roots | `exact_certificates.json`, positive section; exact rational first column, signs + repeated 19 times, −,+,− | Exact root-count certificate; rounded α values numerical |
| Full n=3 source-generated S,R; balanced positive flux and positive equilibrium | `postproof_checks.py`, `exact_certificates.json`, kinetic section; paper Equation 26 | Exact algebra + direct conventional proof |
| Complete Jacobian has exactly three RHP roots and exactly three zero eigenvalues | Exact degree-nine polynomial for 100J and rational Routh column; paper Proposition 7.1 | Exact algebra + classical Routh criterion |
| Saturating realization, rank S=9, conserved totals 4,4,10, nonzero modes in im S | Direct derivative identity, exact rank and flux checks, Ju=λu⇒u=S(Ru/λ) | Conventional proof + exact algebra |
| Plotted spectra | Floating eigenvalue calculations in the exact-check script | Illustration only |

## Strict verification summary

The frozen Lean toolchain is `leanprover/lean4:v4.30.0`. All three final receipts
have `verified=true`, `exit_code=0`, authenticated declaration interfaces, and
warnings treated as errors. Every exported interface lists only
`Classical.choice`, `Quot.sound`, and `propext`.

| Target | SHA256 of target source | Verification duration |
| --- | --- | --- |
| Resolution.lean | `273d87134366cd53138918b233abe007e621af2be5eeaa7a538150d144b45579` | 32.890 s |
| PositiveAllRates.lean | `76196f5780cbcc6d1ee047296d2c511762e0a0e72be0249987265744ff79ed3f` | 91.187 s |
| NegativeFiveMinimality.lean | `7dcbe2486472c70724557eef415261adf0cbec08251e1b003bc138d148b52581` | 104.766 s |

The final negative receipt supersedes the failed development receipt
`NegativeFive.verify.json`. That earlier file is a diagnostic, never evidence of
the final status. Neither numerical checks nor AGC lifecycle records substitute
for the strict compiler receipts. No original proof or dependency pin was changed.
