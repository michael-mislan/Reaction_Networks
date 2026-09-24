# The declared Lean subset

This paper is **not** machine verified. Its probabilistic content — the
chronological construction, the observation laws, the resolvent integral,
matrix-logarithm uniqueness, the Chernoff/Pinsker coverage argument, the
normalized-mixture region and the cooperative comparison principle — is proved
conventionally in the manuscript.

What Lean checks is a *declared finite-algebra subset*: identities that are
pure real-field or matrix algebra, where a transcription error would silently
corrupt an implementation. Compiling them rules out that failure mode and
nothing else.

## Modules

| File | What is proved |
|---|---|
| `Resolution.lean` | exact pair-law equality, its third-view separator, decision equality for rational-valued pair rules, mixture/preparation algebra, generic emission/exit cancellation, daughter-marginal perturbation algebra |
| `Resolvent.lean` | `resolvent_generator_recovery`: from `A X = 1` and `(λI − H) A = λI`, that `λ(1 − X) = H`; `resolvent_exit_recovery`: `λ(X D) = B` when `A = λR`, `D = RB`; `direct_target_identity`: the rational two-state target identity, eq. (13) |
| `DelayedChannel.lean` | `rectangular_channel_recovery` and `delayed_upper_channel_left_inverse`: the rectangular cancellations used after the tensor left-inverse step in Theorem 3.1 |
| `OffspringOrder.lean` | `offspring_difference`: the exact identity of eq. (27), `Σ (K⁺−K)(j,k) xⱼxₖ = ε(x_S−x_T)²`; its nonnegativity; and marginal preservation |
| `CancelledTarget.lean` | **new in this version.** `marker_offdiagonal` and `marker_determinant`: `M_{ST} = N/δ_E²` and `det M = det J/δ_E²`, the two computations behind Proposition 4.1; `cancelled_target`: that substituting them into (13) yields (15); `mixture_calibration`: the three formulas (22); `contamination_bound`: Remark 5.2; `six_category_features`: the subtraction identity of Proposition 4.5 |
| `Postproof.lean` | aggregate import of the subset; asserts nothing itself |

`CancelledTarget.lean` is self-contained and imports only Mathlib, so it can be
checked without the rest of the repository.

## What is *not* formalized

Stochastic paths and the branching construction; the resolvent integral and its
convergence; Hoeffding's and Chernoff's inequalities, Pinsker's inequality and
the coverage statement of Theorem 4.4; the interval-arithmetic inclusion
property and the certified `kl` enclosures of Appendix A; Markov's inequality
and Proposition 4.6; the cooperative comparison principle and the cubic
expansion of Theorem 6.1; and every numerical claim. These are conventional
proofs, and the exact-arithmetic claims are replayed by `check_paper.py`.

## Reproducing the compilation

```
python lean_verify.py
```

with Lean 4.30.0 and the frozen Mathlib build pinned by this repository. Paths
are taken from `LEAN_BIN`, `MATHLIB_ROOT` and `PROOF_ROOT` if set. The script
compiles each module with warnings promoted to errors, then runs
`#print axioms` on the six new declarations, and writes `lean_receipt.json`
with exit codes, source hashes and the probe output. A run is only meaningful
if every exit code is zero, the output is empty and no declaration depends on
`sorryAx`.
