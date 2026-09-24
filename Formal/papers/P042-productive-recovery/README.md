# Productive recovery and repeated harvesting in a reversible autocatalytic reactor: a uniform operating theorem with a machine-checked proof

[Read the paper](../../../Theory/Production/P042-productive-recovery.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Autocatalytic reaction structure does not by itself establish that a reactor can be harvested repeatedly.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 39 selected modules, including shared dependencies. 21 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [PostproofResolution.lean](../../proofs/ProductiveRecovery/PostproofResolution.lean)
- [RepeatedOperation.lean](../../proofs/ProductiveRecovery/RepeatedOperation.lean)
- [Resolution.lean](../../proofs/ProductiveRecovery/Resolution.lean)
- [SourceFlow.lean](../../proofs/ProductiveRecovery/SourceFlow.lean)
- [WeightedGrowth.lean](../../proofs/ProductiveRecovery/WeightedGrowth.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
