# D-stability under first-order attachments at a single coordinate: an exact static threshold and a subset-sum criterion

[Read the paper](../../../Theory/D-Stability/P084-first-order-attachments.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

This 24-page paper supersedes the shorter [P083 draft](../P083-granularity-coordinate-interfaces/README.md); their central threshold proof is shared.

**Formalization:** Theorem 4.3, with its supporting threshold lemmas, is represented by granularity_threshold and its complete dependency closure. The saved strict receipt probes that declaration with only propext, Classical.choice and Quot.sound. The subset-sum criterion, edge-and-corner reduction, bounded-spread conclusions and further extensions are conventional arguments or exact computer-assisted results as identified in the manuscript; this release does not label them kernel-verified.

**Formal sources:** 20 modules including shared dependencies, with 1 saved declaration probes linked in the claim map.

Selected entry points:

- [Threshold.lean](../../proofs/DStabilityCharacterization/Threshold.lean)

## Verification

The [historical verification review](evidence/historical-verification.json) matches every selected source and transitive local import to its saved strict receipt and the pinned Lean 4.30.0 / Mathlib environment. Sources and module names are unchanged. No fresh destination compilation or axiom audit was run for this migration. Source-era command paths in receipts are archival; machine-account components are redacted consistently with the existing collection.

## Reproduction

From `Formal/`, after obtaining the pinned Mathlib cache as described in the [build guide](../../BUILD.md):

```text
python scripts/verify.py --paper P084 --max-modules 60 --max-seconds 3600 --threads 1
python scripts/audit_claims.py --paper P084 --threads 1
```

The [manuscript source](manuscript/main.tex) is preserved with its figure and bibliography inputs and blank author fields. It can be built from `manuscript/` with pdflatex (and BibTeX where a bibliography is used). No manuscript recompilation is claimed. Original [source notes](evidence/source-maps/BUILD.md) are archival; use the shared build guide for migrated Lean reproduction.
