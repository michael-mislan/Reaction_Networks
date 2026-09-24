# Trustworthy decisions in stochastic amplification assays: timing limits, measurement design, and effective capacity

[Read the paper](../../../Applications/Assays/P057-amplification-decisions.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Changing a readout time, adding an identity-sensitive measurement, increasing the reagent reserve, and improving the inference procedure solve different problems, and a laboratory that confuses them can spend its effort on a step that cannot succeed.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 37 selected modules, including shared dependencies. 14 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BlockRatio.lean](../../proofs/AssayInformation/BlockRatio.lean)
- [CrossingDensity.lean](../../proofs/AssayInformation/CrossingDensity.lean)
- [DecisionGap.lean](../../proofs/AssayInformation/DecisionGap.lean)
- [DensitySigns.lean](../../proofs/AssayInformation/DensitySigns.lean)
- [DualMargin.lean](../../proofs/AssayInformation/DualMargin.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
