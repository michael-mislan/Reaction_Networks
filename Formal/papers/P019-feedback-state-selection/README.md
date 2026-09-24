# Feedback-induced bistability and global state selection in coupled autocatalytic cores

[Read the paper](../../../Theory/Kinetics/P019-feedback-state-selection.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

We study a driven four-species mass-action assembly in which two minimal gain-two autocatalytic cores, an AB core and a ZH core, are joined by a shared fork reaction A ⇌ B + z and a small reverse channel B + G ⇌ 2A.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 167 selected modules, including shared dependencies. 1 declaration record is linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [CoreCouplingGlobal/Main.lean](../../proofs/CoreCouplingGlobal/Main.lean)
- [CoreCouplingCAC/Main.lean](../../proofs/CoreCouplingCAC/Main.lean)
- [Absorbing.lean](../../proofs/CoreCouplingGlobal/Absorbing.lean)
- [ActivityEndpoint.lean](../../proofs/CoreCouplingGlobal/ActivityEndpoint.lean)
- [ActualExitEnergy.lean](../../proofs/CoreCouplingGlobal/ActualExitEnergy.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
