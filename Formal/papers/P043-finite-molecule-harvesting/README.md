# Reliable repeated harvesting in a finite-molecule autocatalytic reactor: a source-level finite-horizon operating theorem with a machine-checked proof

[Read the paper](../../../Theory/Production/P043-finite-molecule-harvesting.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Repeated harvesting asks a reactor that has just been thinned to make product and to restore its own catalytic stock before the next withdrawal.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 258 selected modules, including shared dependencies. 57 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

[Publication source-selection review](../../migration/selection-reviews/P043.md) records the final source closure and any excluded drafts.

Selected entry points:

- [PublicationResolution.lean](../../proofs/FiniteCopyReactor/PublicationResolution.lean)
- [Resolution.lean](../../proofs/FiniteCopyReactor/Resolution.lean)
- [WeightedGrowth.lean](../../proofs/ProductiveRecovery/WeightedGrowth.lean)
- [EffectiveScale.lean](../../proofs/FiniteCopyReactor/EffectiveScale.lean)
- [EntryProbability.lean](../../proofs/FiniteCopyReactor/EntryProbability.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
