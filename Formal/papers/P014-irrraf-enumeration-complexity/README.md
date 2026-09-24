# The complexity of complete irreducible autocatalytic families: output-polynomial enumeration of irreducible RAFs if and only if P = NP

[Read the paper](../../../Theory/Algorithms/P014-irrraf-enumeration-complexity.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

An irreducible reflexively autocatalytic and food-generated set (irreducible RAF, or irrRAF) is an inclusion-minimal nonempty RAF of a finite catalytic reaction system.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 417 selected modules, including shared dependencies. 26 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

[Publication source-selection review](../../migration/selection-reviews/P014.md) records the final source closure and any excluded drafts.

Selected entry points:

- [CircuitBijection.lean](../../proofs/IrrRAFEnumeration/CircuitBijection.lean)
- [CircuitClosure.lean](../../proofs/IrrRAFEnumeration/CircuitClosure.lean)
- [Classification.lean](../../proofs/IrrRAFEnumeration/Classification.lean)
- [CompletionConditionalEnumeration.lean](../../proofs/IrrRAFEnumeration/CompletionConditionalEnumeration.lean)
- [CompletionLabelTransport.lean](../../proofs/IrrRAFEnumeration/CompletionLabelTransport.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
