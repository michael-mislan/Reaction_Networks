# Ancillary files

* `lean/` - the 41 Lean 4 modules of the namespace `ACRZeroDivisors`
  (toolchain `leanprover/lean4:v4.30.0`, pinned Mathlib). In the source
  repository they live in `proofs/ACRZeroDivisors/` and import each other as
  `proofs.ACRZeroDivisors.<Module>`.
  * `CampaignRoot.lean` - `campaign_root`: the two bimolecular counterexamples,
    the mixed-order counterexample, block-order completeness for rational
    mass-action input, and the product-release algebra and ACR transfer.
  * `PaperRoot.lean` - `paper_root`: the above plus the residual bound, the
    reactor characteristic polynomial, the EnvZ identities and the product-loss
    inequality.
  * `RegularityCertificates.lean` - the EnvZ Jacobian minor and the rational
    Lyapunov data of the invariant ellipsoid (verified separately).
  All are compiled with warnings as errors, contain no `sorry`, and the roots
  depend only on `propext`, `Classical.choice`, `Quot.sound`.
* `check_paper.py` - exact replay of every identity and number printed in the
  paper (SymPy); prints a JSON report ending in `"status": "PASS"`.
* `make_figures.py` - regenerates the three PDF figures (matplotlib, numpy, scipy).

Geometric and dynamical arguments (Theorem 6.2, nonlinear stability, the
invariance argument, the existence part of the pool classification) are
conventional proofs in the paper and are not formalised.
