# The material and kinetic cost of productive chemical memory: exact frontiers for support and proportion encodings

[Read the paper](../../../Theory/Memory/P074-productive-memory-material-cost.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Two explicit chemical architectures quantify the material cost of jointly producing fresh output and retaining identity in both daughters, with exact architecture-specific frontiers and distinct support and proportion encodings.

**Reproduction:** From `manuscript/`, run pdflatex main.tex three times; the bibliography is inline and no BibTeX pass is needed. `python check_paper.py` uses the saved data for support memory and exact standard-library arithmetic for proportion memory. --full reruns the longer producers; scripts use local paths and NumPy/SciPy for CTMC calculations. figures.py reads included data and requires Matplotlib. The Erdos-specific commands in archived BUILD.md are provenance; use the local scripts and this repository's pinned Lean environment.

**Formalization:** The current 26-page manuscript merges and supersedes two earlier drafts. Ten local modules in UsefulChemicalMemoryCost and ProductiveChemicalHeredity, plus shared dependencies, match the publication copies and saved strict receipts; eleven declarations have saved elaborated axiom interfaces. The formal subset covers source conservation, material necessities, kernel envelopes, conditional coverage/frontier implications, closed-pair and rate identities, binomial tail certificates and earlier arithmetic margins. The 3,384-state recurrence execution, protocol-to-semigroup bridge, Bernoulli coupling and normalization, and exact architecture-class search are conventional or external exact computation. New bias/rate boxes, the untied minimum 42, sharper 0.9997/0.997 guarantees and optimized 253-core frontier are not inferred from the earlier formal arithmetic. These are architecture-specific results, not universal encoding lower bounds or calibrated chemistry.

[Historical verification review](../../papers/P074-productive-memory-material-cost/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 17 selected modules, including shared dependencies. 44 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Frontier.lean](../../proofs/UsefulChemicalMemoryCost/Frontier.lean)
- [MaterialBound.lean](../../proofs/UsefulChemicalMemoryCost/MaterialBound.lean)
- [Resolution.lean](../../proofs/UsefulChemicalMemoryCost/Resolution.lean)
- [RobustEnvelope.lean](../../proofs/UsefulChemicalMemoryCost/RobustEnvelope.lean)
- [Source.lean](../../proofs/UsefulChemicalMemoryCost/Source.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
