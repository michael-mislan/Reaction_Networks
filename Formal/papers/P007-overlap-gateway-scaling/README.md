# Exact Overlap Partitions and Gateway Scaling in Kauffman RAF Networks

[Read the paper](../../../Theory/Emergence/P007-overlap-gateway-scaling.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

We study the probability that a reflexively autocatalytic and food-generated (RAF) set exists in Kauffman’s binary-polymer model with random catalysis, in the exact reaction convention of the public code accompanying the recent finite-core theory of RAF emergence of Varanasi and Korenaga.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 35 selected modules, including shared dependencies. 3 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [CorrectedEmergenceResolution.lean](../../proofs/OverlapCorrectedRAF/CorrectedEmergenceResolution.lean)
- [GatewayConditionedBulk.lean](../../proofs/OverlapCorrectedRAF/Asymptotic/GatewayConditionedBulk.lean)
- [GatewayProbability.lean](../../proofs/OverlapCorrectedRAF/Asymptotic/GatewayProbability.lean)
- [LinearCatalysis.lean](../../proofs/OverlapCorrectedRAF/Asymptotic/LinearCatalysis.lean)
- [SublinearCatalysis.lean](../../proofs/OverlapCorrectedRAF/Asymptotic/SublinearCatalysis.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
