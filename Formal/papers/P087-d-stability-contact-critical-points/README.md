# A critical-point criterion for D-stability in every dimension

[Read the paper](../../../Theory/D-Stability/P087-d-stability-contact-critical-points.pdf) · [Manuscript](manuscript/main.tex) · [Claim map](claims.json) · [Build instructions](../../BUILD.md)

Critical points on Johnson’s contact variety characterize D-stability in every dimension. The paper gives an explicit 5×5 critical-point system, a boundary dichotomy, and robustness margins for bounded time-scale ratios.

**Formalization:** The contact criterion, critical-point coverage, five-dimensional specialization, boundary dichotomy, bounded time-scale stability, separation protection, and diagonal-Lyapunov certificates are formalized. Generic finiteness, Bézout bounds, singular-locus termination, and the numerical decision tool are outside the Lean formalization.

Selected Lean sources:

- [Paper.lean](../../proofs/DStability5x5/Paper.lean)
- [FiveByFive.lean](../../proofs/DStability5x5/FiveByFive.lean)
- [KappaStar.lean](../../proofs/DStability5x5/KappaStar.lean)

[Verification scope](../../VERIFICATION.md) · [All papers](../../../README.md)
