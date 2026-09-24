# An Exact Counterexample to the D-Unstable-Core Conjecture for Parameter-Rich Reaction Networks

[Read the paper](../../../Theory/Kinetics/P003-parameter-rich-d-cores.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Vassena and Stadler introduced unstable cores, minimal square child-selection subma- trices of the stoichiometric matrix, and proved that a D-unstable core is suﬃcient for a reaction network with parameter-rich kinetics to admit an unstable positive equilib- rium.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 45 selected modules, including shared dependencies. 2 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

**Trust base:** the recorded declaration audit records 7 native-evaluation axioms for finite computations beyond Lean's three standard classical axioms. The exact names and per-declaration dependencies are recorded in the [axiom report](../../migration/clean-verification.json).

Selected entry points:

- [DiagonalDissipative.lean](../../proofs/DUnstableCores/DiagonalDissipative.lean)
- [ParameterRichCounterexample.lean](../../proofs/DUnstableCores/ParameterRichCounterexample.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
