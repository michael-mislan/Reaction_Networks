# Finite-batch selection between inherited chemical states under a shared limiting resource

[Read the paper](../../../Theory/Evolution/P021-finite-batch-state-selection.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A chemical difference between compartments can change how fast they grow without changing how many compartments of each kind there are: in an asynchronously dividing population, accumulated size and offspring number are out of phase.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 121 selected modules, including shared dependencies. 9 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Main.lean](../../proofs/ResourceLimitedCompetition/Main.lean)
- [PostProof.lean](../../proofs/ResourceLimitedCompetition/PostProof.lean)
- [AccuracyScaling.lean](../../proofs/ResourceLimitedCompetition/AccuracyScaling.lean)
- [ActiveAncestralGeometry.lean](../../proofs/ResourceLimitedCompetition/ActiveAncestralGeometry.lean)
- [AffineGrowthGenerator.lean](../../proofs/ResourceLimitedCompetition/AffineGrowthGenerator.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
