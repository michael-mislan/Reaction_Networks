# Critical-window emergence of autocatalytic sets under reaction-channel quotienting

[Read the paper](../../../Theory/Emergence/P036-channel-quotient-emergence.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

We determine the limiting probability that a reflexively autocatalytic and food-generated (RAF) set exists in the reversible binary-polymer model in the reaction convention used by the public generator of the finite-core theory of RAF emergence: two split descriptions u + v ⇌ uv and v + u ⇌ vu are identified precisely when uv = vu.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 200 selected modules, including shared dependencies. 13 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [CatalyticOR.lean](../../proofs/RAFReactionQuotient/CatalyticOR.lean)
- [CommutingUniqueness.lean](../../proofs/RAFReactionQuotient/CommutingUniqueness.lean)
- [CountLoss.lean](../../proofs/RAFReactionQuotient/CountLoss.lean)
- [Counts.lean](../../proofs/RAFReactionQuotient/Counts.lean)
- [FiniteApproximation.lean](../../proofs/RAFReactionQuotient/FiniteApproximation.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
