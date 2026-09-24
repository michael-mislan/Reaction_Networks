# Permanence and composition control for self-limited consumers coupled to a dynamic resource network

[Read the paper](../../../Theory/Persistence/P031-dynamic-resource-control.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

We study finitely many consumers that copy themselves from a shared resource, are each separately self-limited, and are coupled to a four-variable mass-action network that produces the resource.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 86 selected modules, including shared dependencies. 15 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [CompositionConsequences.lean](../../proofs/MultiConsumerPermanence/CompositionConsequences.lean)
- [Main.lean](../../proofs/MultiConsumerPermanence/Main.lean)
- [NegativeControl.lean](../../proofs/MultiConsumerPermanence/NegativeControl.lean)
- [RateMain.lean](../../proofs/MultiConsumerPermanence/RateMain.lean)
- [ReservoirMain.lean](../../proofs/MultiConsumerPermanence/ReservoirMain.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
