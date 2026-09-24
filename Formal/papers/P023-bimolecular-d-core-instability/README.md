# Reactant-bimolecular mass-action instability without D-unstable cores

[Read the paper](../../../Theory/Kinetics/P023-bimolecular-d-core-instability.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A child selection of a reaction network assigns to each species in a subset a distinct reaction consuming it; the corresponding square submatrix of the stoichiometric matrix is D-unstable if some positive diagonal column scaling gives it an eigenvalue with positive real part.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 58 selected modules, including shared dependencies. 9 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

[Publication source-selection review](../../migration/selection-reviews/P023.md) records the final source closure and any excluded drafts.

Selected entry points:

- [DiagonalDissipative.lean](../../proofs/DUnstableCores/DiagonalDissipative.lean)
- [ElementaryFluxFamily.lean](../../proofs/DUnstableCores/Elementary/ElementaryFluxFamily.lean)
- [ElementaryParameterPolynomial.lean](../../proofs/DUnstableCores/Elementary/ElementaryParameterPolynomial.lean)
- [ElementarySpectralMargin.lean](../../proofs/DUnstableCores/Elementary/ElementarySpectralMargin.lean)
- [Resolution.lean](../../proofs/DUnstableCores/Elementary/Resolution.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
