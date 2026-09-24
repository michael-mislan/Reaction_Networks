# When does a negative assay exclude a finite target count? Sharp false-exclusion bounds for native-reference reporting rules

[Read the paper](../../../Applications/Assays/P060-finite-target-exclusion.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A negative readout need not exclude targets in the original specimen when extraction failures are shared across targets and splitting consumes material.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 15 selected modules, including shared dependencies. 20 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BatchReporting.lean](../../proofs/SpecimenReliability/BatchReporting.lean)
- [Design.lean](../../proofs/SpecimenReliability/Design.lean)
- [ObservationRobustness.lean](../../proofs/SpecimenReliability/ObservationRobustness.lean)
- [PoissonReferences.lean](../../proofs/SpecimenReliability/PoissonReferences.lean)
- [PolicyComparison.lean](../../proofs/SpecimenReliability/PolicyComparison.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
