# Exposure and amplitude limits for eradicating populations with inherited cellular states

[Read the paper](../../../Applications/Cell-Memory/P065-exposure-amplitude-limits.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

The paper separates exposure and amplitude obstructions for controlled populations with inherited cellular states, retaining correlated daughter inheritance in a synthetic molecular source.

**Formalization:** The 26-page publication supersedes the older 12-page workspace report. Lean supports the literal six-state source algebra, supersolution segment and control inequalities, improved weight, RR Taylor coefficient, and auxiliary finite barrier and dose identities. The main controlled stochastic theorems, amplitude floor, general site-count conclusions and validated integrator remain conventional mathematical or exact computational evidence as specified in the manuscript. The 23 mapped declarations are finite algebra support, not formal proofs of eradication or clinical efficacy. Only declarations explicitly listed in the saved probes have individual historical axiom audits. No new Lean run or numerical replay is claimed. The preserved workspace handoff describes an earlier publication and supplies provenance for unchanged algebra; the current manuscript governs scope.

[Historical verification review](../../papers/P065-exposure-amplitude-limits/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 8 selected modules, including shared dependencies. 23 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [ControlSource.lean](../../proofs/PersisterMemory/ControlSource.lean)
- [BudgetBarrier.lean](../../proofs/PersisterMemory/BudgetBarrier.lean)
- [SupersolutionSegment.lean](../../proofs/PersisterMemory/SupersolutionSegment.lean)
- [ImprovedPulseCertificate.lean](../../proofs/PersisterMemory/ImprovedPulseCertificate.lean)
- [RemainingBudgetAlgebra.lean](../../proofs/PersisterMemory/RemainingBudgetAlgebra.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
