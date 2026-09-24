# Finite-copy productive operation in a reversible autocatalytic binding network: an explicit probability guarantee with a machine-checked proof

[Read the paper](../../../Theory/Production/P018-finite-copy-binding-operation.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Structural criteria for autocatalysis, such as reflexively autocatalytic food-generated (RAF) sets or stoichiometric autocatalytic cores, certify that a reaction network can in principle amplify its own catalysts.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 44 selected modules, including shared dependencies. 12 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BindingCountChannels.lean](../../proofs/RandomViability/BindingCountChannels.lean)
- [BindingCountDrift.lean](../../proofs/RandomViability/BindingCountDrift.lean)
- [BindingCountExponential.lean](../../proofs/RandomViability/BindingCountExponential.lean)
- [BindingDisabledProbability.lean](../../proofs/RandomViability/BindingDisabledProbability.lean)
- [BindingEntryProbability.lean](../../proofs/RandomViability/BindingEntryProbability.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
