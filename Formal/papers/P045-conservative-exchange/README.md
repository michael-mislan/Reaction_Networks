# Conservative exchange preserves repeated production in autocatalytic reactor networks: a uniform composition theorem with a machine-checked proof

[Read the paper](../../../Theory/Production/P045-conservative-exchange.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

An isolated reactor’s guarantee of repeated productive operation does not automatically survive connection to other reactors: exchange changes the state during recovery, and the exchanged material includes the catalyst in all of its chemical forms.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 72 selected modules, including shared dependencies. 32 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Examples.lean](../../proofs/C4Assemblies/Examples.lean)
- [FineFreeProduct.lean](../../proofs/C4Assemblies/FineFreeProduct.lean)
- [FinePhaseBounds.lean](../../proofs/C4Assemblies/FinePhaseBounds.lean)
- [FinePhaseTransfer.lean](../../proofs/C4Assemblies/FinePhaseTransfer.lean)
- [Publication.lean](../../proofs/C4Assemblies/Publication.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
