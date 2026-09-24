# Inherited-family dependence can reverse an equal-exposure treatment decision

[Read the paper](../../../Applications/Cell-Memory/P066-inherited-family-dependence.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Two branching sources can share every type-resolved mean under a common deterministic schedule yet prefer opposite orders of two equal-exposure interventions when the decision depends on extinction.

**Reproduction:** From this dossier, use `python manuscript/verify_claims.py --workspace support` for the saved-certificate arithmetic checks, and `python manuscript/figures.py --workspace support` to regenerate figures. Python 3.11 with NumPy is needed for the checker; figures also need Matplotlib and SciPy. The explicit workspace argument selects the included inputs instead of the archival Erdos default. The independent four-flow producer is retained as `support/experiments/validated.py`. Compile `manuscript/main.tex` with two pdflatex passes; figures are already included.

**Formalization:** The current 22-page publication uses the expanded EvolutionaryRescue algebra root. Lean supports finite source normalization and augmented linearization, offspring/covariance algebra, the continuation weight, barrier and scalar-envelope inequalities, regret algebra and presentation margins. The branching/ODE bridge, Nagumo/Harris covariance sign argument, curvature theorem, interval integrator and complete extinction comparison remain conventional or exact computational evidence. The newer continuation bounds in the manuscript are not asserted to follow from the older auxiliary robustness constant. Individual axiom coverage is limited to the declarations explicitly probed in the saved receipts. The synthetic near-tie example is not a calibrated treatment recommendation.

[Historical verification review](../../papers/P066-inherited-family-dependence/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 8 selected modules, including shared dependencies. 23 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Source.lean](../../proofs/EvolutionaryRescue/Source.lean)
- [Expansion.lean](../../proofs/EvolutionaryRescue/Expansion.lean)
- [Barrier.lean](../../proofs/EvolutionaryRescue/Barrier.lean)
- [Decision.lean](../../proofs/EvolutionaryRescue/Decision.lean)
- [ScalarBarrier.lean](../../proofs/EvolutionaryRescue/ScalarBarrier.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
