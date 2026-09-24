# Minimum autocatalytic networks cannot be approximated within any constant factor

[Read the paper](../../../Theory/Algorithms/P001-min-raf-inapproximability.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A reflexively autocatalytic and food-generated set (RAF) is a nonempty set of reactions in a catalytic reaction system whose reactants can all be built up from a designated food set and each of whose reactions is catalysed by a food molecule or by a product of the set.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 21 selected modules, including shared dependencies. 18 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [ApproximationTransfer.lean](../../proofs/MinRAFApprox/ApproximationTransfer.lean)
- [ComplexityTransfer.lean](../../proofs/MinRAFApprox/ComplexityTransfer.lean)
- [EncodingSize.lean](../../proofs/MinRAFApprox/EncodingSize.lean)
- [SetCoverBijection.lean](../../proofs/MinRAFApprox/Gadgets/SetCoverBijection.lean)
- [SetCoverCardinality.lean](../../proofs/MinRAFApprox/Gadgets/SetCoverCardinality.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
