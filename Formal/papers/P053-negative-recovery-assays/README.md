# When can a negative recovery assay exclude a recoverable subpopulation? Sharp coverage, stage mismatch and allocation bounds for paired observations

[Read the paper](../../../Applications/Assays/P053-negative-recovery-assays.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A finite recovery experiment that records no qualifying event is compatible both with the absence of recoverable units and with a failure to observe their recovery.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 8 selected modules, including shared dependencies. 15 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [DesignLimits.lean](../../proofs/FunctionalViability/DesignLimits.lean)
- [ExtendedCoverage.lean](../../proofs/FunctionalViability/ExtendedCoverage.lean)
- [RobustCertificate.lean](../../proofs/FunctionalViability/RobustCertificate.lean)
- [BalancedSampling.lean](../../proofs/FunctionalViability/BalancedSampling.lean)
- [CoverageBounds.lean](../../proofs/FunctionalViability/CoverageBounds.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
