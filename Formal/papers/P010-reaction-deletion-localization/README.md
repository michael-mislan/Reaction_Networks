# Certified localization of reaction deletions in autocatalytic networks: ranked support witnesses, witness selection, and exact robustness laws

[Read the paper](../../../Theory/Algorithms/P010-reaction-deletion-localization.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A reflexively autocatalytic and food-generated (RAF) set is the standard combinatorial model of a self-sustaining reaction network.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 133 selected modules, including shared dependencies. 44 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [ChargedLocal.lean](../../proofs/RAFQueryCompilation/ChargedLocal.lean)
- [RankedWitness.lean](../../proofs/RAFQueryCompilation/RankedWitness.lean)
- [ResidualRAF.lean](../../proofs/RAFQueryCompilation/ResidualRAF.lean)
- [SparseRankedWitness.lean](../../proofs/RAFQueryCompilation/SparseRankedWitness.lean)
- [TerminalFamily.lean](../../proofs/RAFQueryCompilation/TerminalFamily.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
