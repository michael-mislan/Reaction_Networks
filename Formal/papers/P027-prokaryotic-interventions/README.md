# Certified selective interventions and closed-RAF structure in a pooled prokaryotic network

[Read the paper](../../../Applications/Metabolic-and-Redox-Function/P027-prokaryotic-interventions.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

We give a source-specific, computer-assisted analysis of catalytic food-generated reaction structure in a pooled prokaryotic network with 6,039 reaction actions and 9,231 directed reactions.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 20 selected modules, including shared dependencies. 13 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

[Publication source-selection review](../../migration/selection-reviews/P027.md) records the final source closure and any excluded drafts.

Selected entry points:

- [BiochemicalResult.lean](../../proofs/RAFBiochemicalInterventions/BiochemicalResult.lean)
- [CutClosed.lean](../../proofs/RAFBiochemicalInterventions/CutClosed.lean)
- [ParentClosed.lean](../../proofs/RAFBiochemicalInterventions/ParentClosed.lean)
- [ParentRobust.lean](../../proofs/RAFBiochemicalInterventions/ParentRobust.lean)
- [PoolingClosed.lean](../../proofs/RAFBiochemicalInterventions/PoolingClosed.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
