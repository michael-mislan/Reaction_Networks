# Prediction coverage in inherited-state branching models: an exact mean-closure counterexample, a repaired count threshold, and the effect of founder number

[Read the paper](../../../Applications/Cell-Memory/P048-inherited-state-coverage.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Low-cell-count proliferation assays are often summarized by a scalar birth–death model whose per-cell rates are read off the expected phenotypic composition of the population.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 112 selected modules, including shared dependencies. 6 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [PositiveLaw.lean](../../proofs/InheritedCellAssay/PositiveLaw.lean)
- [PositiveRepair.lean](../../proofs/InheritedCellAssay/PositiveRepair.lean)
- [PositiveScalarLaw.lean](../../proofs/InheritedCellAssay/PositiveScalarLaw.lean)
- [ConcreteScalarSource.lean](../../proofs/InheritedCellAssay/ConcreteScalarSource.lean)
- [CountAssaySource.lean](../../proofs/InheritedCellAssay/CountAssaySource.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
