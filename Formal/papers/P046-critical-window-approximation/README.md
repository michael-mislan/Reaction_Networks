# Effective approximation, low-intensity bounds, and finite-size effects for autocatalytic emergence in reversible polymer networks

[Read the paper](../../../Theory/Emergence/P046-critical-window-approximation.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

The critical-window law for reflexively autocatalytic and food-generated (RAF) sets in the reversible binary-polymer model states that, when the mean number of reactions catalysed per molecule grows like λn, the RAF probability converges to Sν (1 − e−λ ), where Sν is the probability that ordinary reversible closure of the food set is unbounded in an infinite field of independently open reaction channels.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 244 selected modules, including shared dependencies. 21 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BoundedRecords.lean](../../proofs/RAFCriticalWindowQuantitative/BoundedRecords.lean)
- [CertifiedEvaluator.lean](../../proofs/RAFCriticalWindowQuantitative/CertifiedEvaluator.lean)
- [EffectiveSeed.lean](../../proofs/RAFCriticalWindowQuantitative/EffectiveSeed.lean)
- [EscapeEvaluation.lean](../../proofs/RAFCriticalWindowQuantitative/EscapeEvaluation.lean)
- [ExplicitTruncation.lean](../../proofs/RAFCriticalWindowQuantitative/ExplicitTruncation.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
