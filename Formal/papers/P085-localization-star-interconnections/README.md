# Localization of D-instability in star interconnections and a sharp bound on synchronized groups

[Read the paper](../../../Theory/D-Stability/P085-localization-star-interconnections.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

The existing 17-page PDF and its matching manuscript source are preserved. The outdated lean_receipt_all.json is not used: the newer final root receipt matches the selected sources.

**Formalization:** The final root receipt covers spectral localization, strict-instability lifting, the one-way D-stability criterion, D-semistability equivalence, marginal-gap and synchronized-lumping counterexamples, and sharpness. Four saved root probes cover localization_and_sharpness, sharpness_full, lumping_needed and cyc2_example. A separate source-matched Counting receipt adds two probes for boundary-system counting and equality by loads; this is an additional formal result, not a replacement of the published 17-page PDF. All six probes report only propext, Classical.choice and Quot.sound. Conventional physical interpretation and numerical illustrations are separate from these formal statements.

**Formal sources:** 16 modules including shared dependencies, with 6 saved declaration probes linked in the claim map.

Selected entry points:

- [All.lean](../../proofs/DStabilityLocalization/All.lean)
- [Counting.lean](../../proofs/DStabilityLocalization/Counting.lean)

## Verification

The [historical verification review](evidence/historical-verification.json) matches every selected source and transitive local import to its saved strict receipt and the pinned Lean 4.30.0 / Mathlib environment. Sources and module names are unchanged. No fresh destination compilation or axiom audit was run for this migration. Source-era command paths in receipts are archival; machine-account components are redacted consistently with the existing collection.

## Reproduction

From `Formal/`, after obtaining the pinned Mathlib cache as described in the [build guide](../../BUILD.md):

```text
python scripts/verify.py --paper P085 --max-modules 60 --max-seconds 3600 --threads 1
python scripts/audit_claims.py --paper P085 --threads 1
```

The [manuscript source](manuscript/main.tex) is preserved with its figure and bibliography inputs and blank author fields. It can be built from `manuscript/` with pdflatex (and BibTeX where a bibliography is used). No manuscript recompilation is claimed. Original [source notes](evidence/source-maps/BUILD.md) are archival; use the shared build guide for migrated Lean reproduction.
