# Cycle structure, capacity, and resource costs of phosphorylation memory

[Read the paper](../../../Applications/Phosphorylation/P072-phosphorylation-memory-capacity-costs.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

For unordered multisite phosphorylation with shared enzymes, the paper separates stable-equilibrium capacity from finite-molecule operation, relating cycle balance to capacity and quantifying sufficient retention, recovery and resource costs.

**Reproduction:** Build from `manuscript/` with pdflatex main.tex, bibtex main and two further pdflatex passes. `python check_paper.py` (optionally --full) replays included finite certificates using SymPy; diagnostics additionally use mpmath, and figures use NumPy/Matplotlib. All inputs and the saved report needed by make_figures.py are included and paths are local. Use a suitable Python environment instead of the original absolute Erdos interpreter reference in README.md.

**Formalization:** The current 33-page paper supersedes the 21-page workspace manuscript and incorporates corrected sequential-capacity input from its companion. Three small Mathlib-only modules supply ten routine algebraic identities: scalar tree-total reconstruction, multiplicity and quadratic jumps, stationary loading and numerator identities. Their original bytes match both the publication copies and strict historical compilation receipts; no saved declaration-interface probes accompany these receipts. The capacity bounds, stability constructions, Sard/degree arguments, invariant foliations, finite-copy probability contract and large-deviation estimates are conventional mathematics. Rational and interval certificates are checked by the supplied Python program, not Lean. Exponential-order capacity is not an exact capacity formula for all n, and enormous sufficient resource costs are not universal lower bounds. Writing between labels is not established.

[Historical verification review](../../papers/P072-phosphorylation-memory-capacity-costs/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 3 selected modules, including shared dependencies. 10 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [SymmetricAggregation.lean](../../proofs/PhosphorylationMemory/SymmetricAggregation.lean)
- [TreeTotals.lean](../../proofs/PhosphorylationMemory/TreeTotals.lean)
- [UniformLoading.lean](../../proofs/PhosphorylationMemory/UniformLoading.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
