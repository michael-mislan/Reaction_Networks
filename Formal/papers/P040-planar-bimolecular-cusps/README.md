# Reaction-minimal cusps in planar bimolecular mass-action networks: an exhaustive certified classification

[Read the paper](../../../Theory/Kinetics/P040-planar-bimolecular-cusps.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A cusp of equilibria is the simplest generic mechanism by which a two-parameter family of vector fields passes between one and three nearby equilibria, and it organizes bistability in chemical reaction networks.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 1074 selected modules, including shared dependencies. 9 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

The finite algebraic cusp classification includes explicit checked certificates. Its historical classification audit reports 3,826 native-evaluation axioms in addition to the standard three; the recorded declaration audit records the actual trust base for this checkout. The manuscript separately identifies the conventional analytic reduction and related consequences.

[Publication source-selection review](../../migration/selection-reviews/P040.md) records the final source closure and any excluded drafts.

Selected entry points:

- [BimolecularClassification.lean](../../proofs/SmallCusp/Classification/BimolecularClassification.lean)
- [BimolecularCorollaries.lean](../../proofs/SmallCusp/Classification/BimolecularCorollaries.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
