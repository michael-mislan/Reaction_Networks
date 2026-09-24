# Complete enumeration of irreducible autocatalytic sets with bounded supplier choice

[Read the paper](../../../Theory/Algorithms/P028-bounded-supplier-enumeration.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

An irreducible reflexively autocatalytic and food-generated set (irreducible RAF, or irrRAF) is an inclusion-minimal nonempty RAF of a finite catalytic reaction system.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 44 selected modules, including shared dependencies. 11 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [RestrictedCompletion.lean](../../proofs/IrrRAFEnumeration/RestrictedCompletion.lean)
- [DeterministicSuppliers.lean](../../proofs/RAFStructuredEnumeration/DeterministicSuppliers.lean)
- [EarliestProducer.lean](../../proofs/RAFStructuredEnumeration/EarliestProducer.lean)
- [OverlapBounds.lean](../../proofs/RAFStructuredEnumeration/OverlapBounds.lean)
- [Resolution.lean](../../proofs/RAFStructuredEnumeration/Resolution.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
