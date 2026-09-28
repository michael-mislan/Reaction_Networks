# Granularity and stability at coordinate interfaces: Static thresholds, planar response sets, and finite-rate instability

[Read the paper](../../../Theory/D-Stability/P083-granularity-coordinate-interfaces.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

This 11-page draft is superseded by [P084](../P084-first-order-attachments/README.md). Both reading copies are preserved.

**Formalization:** The coordinate-port threshold theorem and its full dependency closure are source- and environment-matched to a saved strict receipt. The saved elaborated interface probes granularity_threshold and reports only propext, Classical.choice and Quot.sound. The other extensions and examples in this draft have the conventional or computational scope stated in its formalization section.

**Formal sources:** 20 modules including shared dependencies, with 1 saved declaration probes linked in the claim map.

Selected entry points:

- [Threshold.lean](../../proofs/DStabilityCharacterization/Threshold.lean)

## Verification

The [historical verification review](evidence/historical-verification.json) matches every selected source and transitive local import to its saved strict receipt and the pinned Lean 4.30.0 / Mathlib environment. Sources and module names are unchanged. No fresh destination compilation or axiom audit was run for this migration. Source-era command paths in receipts are archival; machine-account components are redacted consistently with the existing collection.

## Reproduction

From `Formal/`, after obtaining the pinned Mathlib cache as described in the [build guide](../../BUILD.md):

```text
python scripts/verify.py --paper P083 --max-modules 60 --max-seconds 3600 --threads 1
python scripts/audit_claims.py --paper P083 --threads 1
```

The [manuscript source](manuscript/main.tex) is preserved with its figure and bibliography inputs and blank author fields. It can be built from `manuscript/` with pdflatex (and BibTeX where a bibliography is used). No manuscript recompilation is claimed. Original [source notes](evidence/source-maps/PUBLICATION_HANDOFF.md) are archival; use the shared build guide for migrated Lean reproduction.
