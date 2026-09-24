# Unistationarity of Type IIℓ and Type V autocatalytic cores with nonnegative degradation

[Read the paper](../../../Theory/Kinetics/P026-nonnegative-degradation.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Nandan, Nghe and Unterberger classified the minimal autocatalytic cores of diluted reaction networks into five families and proved that, under strictly positive linear degradation of every species, every classified core has at most one positive stationary state, with the exception of the Type IIℓ cores with ℓ > 2 forks, which were settled subsequently.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 91 selected modules, including shared dependencies. 11 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BoundaryUniqueness.lean](../../proofs/MixedDegradation/BoundaryUniqueness.lean)
- [Coincident.lean](../../proofs/MixedDegradation/Coincident.lean)
- [Main.lean](../../proofs/MixedDegradation/Main.lean)
- [PassiveChain.lean](../../proofs/MixedDegradation/PassiveChain.lean)
- [Publication.lean](../../proofs/MixedDegradation/Publication.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
