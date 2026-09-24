# Biochemical readouts that preserve native function: reporter storage, finite-time inference and certified recovery in a shared cofactor pool

[Read the paper](../../../Applications/Assays/P061-native-function-readouts.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A reporter that consumes a regenerated cofactor also stores it: while the cofactor sits in a reporter complex it is available neither to the native reaction it is meant to report on nor to the regenerating reaction that would replenish it.

**Formalization:** Formal source algebra, integral account with derivative premises, conditional envelope/classifier transport, inversion algebra and exact rational/exponential certificates. Existence, invariance, comparison, convergence, Michaelis–Menten slope ranges and uniqueness arguments remain conventional; biochemical calibration is a premise. The sharper published recovery bounds are not substituted for the looser named Lean certificates. Six declarations have source-matched historical axiom probes; the other mapped declarations are covered by whole-module compilation but have no separate saved axiom probe.

[Historical verification review](../../papers/P061-native-function-readouts/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 2 selected modules, including shared dependencies. 24 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BiochemicalReadout.lean](../../proofs/BiochemicalReadout.lean)
- [BiochemicalReadoutExtensions.lean](../../proofs/BiochemicalReadoutExtensions.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
