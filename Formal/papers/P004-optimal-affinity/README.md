# Optimal affinity of autocatalytic networks beyond gross stoichiometry: a counterexample, the response-profile capacity, and its kinetic realization

[Read the paper](../../../Theory/Thermodynamics/P004-optimal-affinity.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Despons, De Decker and Lacoste showed that for a tightly coupled mass-action autocatalytic network whose overall reaction consumes α and produces β copies of the controlled autocatalyst, the thermodynamic affinity A∗ at which the production flux is maximal equals log(β/α) for generalized Type I networks, is at least log(β/α) for the class of non-intersecting networks, and they conjectured that the lower bound A∗ ≥ log(β/α) holds in general.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 74 selected modules, including shared dependencies. 52 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

[Publication source-selection review](../../migration/selection-reviews/P004.md) records the final source closure and any excluded drafts.

Selected entry points:

- [OptimalAffinity/Main.lean](../../proofs/OptimalAffinity/Main.lean)
- [FirstOrderRealizability.lean](../../proofs/OptimalAffinityCorrected/FirstOrderRealizability.lean)
- [OptimalAffinityCorrected/Main.lean](../../proofs/OptimalAffinityCorrected/Main.lean)
- [RecyclingFamilyGlobal.lean](../../proofs/OptimalAffinityCorrected/RecyclingFamilyGlobal.lean)
- [SourceAdapter.lean](../../proofs/OptimalAffinityCorrected/SourceAdapter.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
