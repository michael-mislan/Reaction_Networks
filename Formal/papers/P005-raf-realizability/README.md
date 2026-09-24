# Interior operators realizable by autocatalytic networks: an antimatroid characterization

[Read the paper](../../../Theory/Structural/P005-raf-realizability.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A catalytic reaction system with a food set determines an interior operator on the subsets of its reaction set: each set of reactions is sent to the largest reflexively autocatalytic and food-generated (RAF) subset it contains.

**Formalization:** The main characterization theorem and selected corollaries are formalized. Corollary 6.5 (sharp size bound) and Theorem 6.6 (threshold theorem) are conventional, as Section 7.1 specifies. The original abstract and overview overstate that scope; read the [editorial correction](../../../ERRATA.md#p005--scope-of-formalization).

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 20 selected modules, including shared dependencies. 4 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Corollaries.lean](../../proofs/RAFInteriorRealizability/Corollaries.lean)
- [Main.lean](../../proofs/RAFInteriorRealizability/Main.lean)
- [AntimatroidRealization.lean](../../proofs/RAFInteriorRealizability/AntimatroidRealization.lean)
- [Basic.lean](../../proofs/RAFInteriorRealizability/Basic.lean)
- [CatalysisRealization.lean](../../proofs/RAFInteriorRealizability/CatalysisRealization.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
