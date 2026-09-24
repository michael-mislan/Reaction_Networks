# A reaction-deletion-minimal mass-action oscillator without D-unstable child selections

[Read the paper](../../../Theory/Kinetics/P037-reaction-minimal-oscillator.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A child selection of a reaction network assigns to each species in a subset a distinct reaction in which it is a reactant; the corresponding square submatrix of the stoichiometric matrix is D-unstable if some positive diagonal scaling gives it an eigenvalue with positive real part.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 97 selected modules, including shared dependencies. 6 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [DiagonalDissipative.lean](../../proofs/DUnstableCores/DiagonalDissipative.lean)
- [LocalBranchCorollaries.lean](../../proofs/OscillatoryCores/LocalBranchCorollaries.lean)
- [PublicationConsequences.lean](../../proofs/OscillatoryCores/PublicationConsequences.lean)
- [Resolution.lean](../../proofs/OscillatoryCores/Resolution.lean)
- [AmplitudeOrbit.lean](../../proofs/OscillatoryCores/AmplitudeOrbit.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
