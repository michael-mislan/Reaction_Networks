# Addendum (16 September 2026): free-X floor 1/160 and the arXiv paper

This addendum records work done after `PUBLICATION_HANDOFF.md` was written.
No existing Lean file, receipt or record in this workspace was modified.

## New Lean modules (proofs/C4Assemblies/)

- `FinePhaseBounds.lean` — `fine_phase_comparison`: the four phase rows with
  the distinct losses 48, 43, 41, 24 and the `2z` link in the C2 row
  (same hypotheses as `sharp_phase_comparison`).
- `FinePhaseTransfer.lean` — `finePhaseWeight` (degree-4 truncation of
  e_X exp(a K'') with K'' = K + diag(0,5,7,24)), `finePhaseWeight_assembly`,
  `fine_backward_phase_local` (identity: sum of nonnegative products, closed
  by `ring` + `linarith`), `fine_backward_phase_deriv`,
  `fine_phase_minimum_propagation` (rate 48, same shape as the sharp version).
- `FineFreeProduct.lean` — `fine_exp_twelve_sevenths`
  (`Real.exp (12/7) ≤ 961355/172872`, via `Real.exp_bound'` with x = 6/7,
  n = 8, rounded to 2357/1000 and squared), `fine_assembly_free_phase_floor`
  (`(1/8)·b ≤ x_i(t + 1/28)` when all `Y_j(t) ≥ b`),
  `fine_assembly_routine_free_export` (floor and integral 1/160 on [3,4]).
- `PublicationFine.lean` — `fine_conservative_assembly_operation` (the root
  statement of `sharp_conservative_assembly_operation` with every 1/209
  replaced by 1/160), `fine_path_operation`, `fine_ring_operation`.

Receipts (all `verified: true`, exit 0, empty compiler streams, toolchain
leanprover/lean4:v4.30.0, manifest `a8df0b60…`, axioms propext /
Classical.choice / Quot.sound only): `FinePhaseBounds.verify.json`,
`FinePhaseTransfer.verify.json`, `FineFreeProduct.verify.json`,
`PublicationFine.verify.json` (root SHA-256
`ad7da3c0b6e99b0e6904523288b341272361e7bd3d7117f61a9da18327a92c7d`).

Exact preflight for the certificate: p(1/28) = (1, 961355/1229312,
1847785/1843968, 665611/307328); ratios to the Y weights
(1, 961355/1382976, 9238925/12907776, 3328055/2765952); minimum at C1;
8·(961355/1382976) = 961355/172872 ≈ 5.5611 > exp(12/7) ≈ 5.5527.
The exact matrix exponential of the same lower system with the lag
optimized numerically would give only about 1/157, so the remaining slack
(pilot ≈ 20× the floor) is in the lower system and the uniform threshold,
not in the truncation.

## Paper

The arXiv-style paper (25 pages) and its editable sources are in
`key_results/RAFs/Conservative_Exchange_Reactor_Networks_arxiv/` (see its
`BUILD.md`); the compiled PDF is
`key_results/RAFs/Conservative_Exchange_Preserves_Repeated_Production_Autocatalytic_Reactor_Networks.pdf`.
It supersedes `C4_Conservative_Exchange_Paper.pdf` in this directory as the
publication manuscript; the workspace PDF and tex are retained as the plan
they were.
