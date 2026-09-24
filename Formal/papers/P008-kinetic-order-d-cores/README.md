# Kinetic order is invisible to D-cores: a support-preserving mass-action lift and an exact counterexample

[Read the paper](../../../Theory/Kinetics/P008-kinetic-order-d-cores.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Unstable-core methods explain the instability of a reaction-network equilibrium through a small child selection: a square submatrix of the stoichiometric matrix, chosen by assigning to each of a few species one reaction in which it is a reactant, that is unstable under some positive diagonal scaling.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 52 selected modules, including shared dependencies. 15 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

[Publication source-selection review](../../migration/selection-reviews/P008.md) records the final source closure and any excluded drafts.

**Trust base:** the recorded declaration audit records 7 native-evaluation axioms for finite computations beyond Lean's three standard classical axioms. The exact names and per-declaration dependencies are recorded in the [axiom report](../../migration/clean-verification.json).

Selected entry points:

- [Main.lean](../../proofs/DUnstableCores/ClassicalMassAction/Main.lean)
- [RationalLift.lean](../../proofs/DUnstableCores/ClassicalMassAction/RationalLift.lean)
- [UnpaddedStability.lean](../../proofs/DUnstableCores/ClassicalMassAction/UnpaddedStability.lean)
- [DiagonalDissipative.lean](../../proofs/DUnstableCores/DiagonalDissipative.lean)
- [Source.lean](../../proofs/DUnstableCores/ClassicalMassAction/Source.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
