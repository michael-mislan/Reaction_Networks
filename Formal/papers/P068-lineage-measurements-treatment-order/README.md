# When single-lineage measurements fail to determine treatment order: sister dependence, branching extinction, and decision-focused assays

[Read the paper](../../../Applications/Cell-Memory/P068-lineage-measurements-treatment-order.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Complete observations of one retained lineage can agree across branching sources while the sources prefer opposite intervention orders for the whole family; paired sister measurements can distinguish the missing dependence under stated model assumptions.

**Reproduction:** From the `manuscript/` directory, use pdflatex, bibtex, then two further pdflatex passes. `python scripts/check_paper.py` uses SymPy and writes the local certificates file; `python scripts/figures.py` additionally needs NumPy and Matplotlib. All paths are relative to the included scripts. The saved Lean sources and receipts describe the earlier finite-algebra subset and need not be rerun to build the current manuscript.

**Formalization:** The current 26-page manuscript supersedes the earlier working note and supplement. Its stochastic, comparison, integration and testing results are conventional proofs. The accompanying exact/symbolic calculation scripts and saved certificates are preserved without a new numerical replay. Five earlier Lean modules are retained as archival finite-algebra support; their 20 declaration records do not formalize the current strengthened descendant-division ranges, sensitivity reserve, retained-history law or statistical guarantees. In particular, the old 1/500 occupation margin and tiny-pulse certificate must not be relabelled as the newer 1/30 or full-range results. No end-to-end stochastic formalization or clinical efficacy is claimed.

[Historical verification review](../../papers/P068-lineage-measurements-treatment-order/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 5 selected modules, including shared dependencies. 20 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [FiniteSource.lean](../../proofs/CellTreatmentDecision/FiniteSource.lean)
- [SeedThreshold.lean](../../proofs/CellTreatmentDecision/SeedThreshold.lean)
- [RiskComparison.lean](../../proofs/CellTreatmentDecision/RiskComparison.lean)
- [FinitePulse.lean](../../proofs/CellTreatmentDecision/FinitePulse.lean)
- [Resolution.lean](../../proofs/CellTreatmentDecision/Resolution.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
