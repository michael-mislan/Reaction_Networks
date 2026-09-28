# Deciding D-stability is coNP-hard

[Read the paper](../../../Theory/D-Stability/P086-deciding-d-stability-conp-hard.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

The revised 19-page reading copy is unchanged. The [earlier supplied version](../../../Theory/D-Stability/versions/P086-deciding-d-stability-conp-hard-supplied.pdf) remains available.

**Formalization:** Saved strict Paper and All receipts cover the explicit PARTITION reduction, matrix stability dichotomy, encoding/size bounds, contact exclusion and static-window certificates, plus time-scale and restricted-classification follow-ups. The saved declaration probes use only propext, Classical.choice and Quot.sound. The complexity conclusion uses the conventional NP-completeness of PARTITION and the conventional connection to the chosen machine/bit-complexity model; those are not claimed as a formalized complexity-theory library. Hardness is in the weak (binary-encoding) sense, as stated in the paper.

**Formal sources:** 57 modules including shared dependencies, with 12 saved declaration probes linked in the claim map.

Selected entry points:

- [Paper.lean](../../proofs/DStabilityHardness/Paper.lean)
- [All.lean](../../proofs/DStabilityHardness/All.lean)

## Verification

The [historical verification review](evidence/historical-verification.json) matches every selected source and transitive local import to its saved strict receipt and the pinned Lean 4.30.0 / Mathlib environment. Sources and module names are unchanged. No fresh destination compilation or axiom audit was run for this migration. Source-era command paths in receipts are archival; machine-account components are redacted consistently with the existing collection.

## Reproduction

From `Formal/`, after obtaining the pinned Mathlib cache as described in the [build guide](../../BUILD.md):

```text
python scripts/verify.py --paper P086 --max-modules 60 --max-seconds 3600 --threads 1
python scripts/audit_claims.py --paper P086 --threads 1
```

The [manuscript source](manuscript/main.tex) is preserved with its figure and bibliography inputs and blank author fields. It can be built from `manuscript/` with pdflatex (and BibTeX where a bibliography is used). No manuscript recompilation is claimed. Original [source notes](evidence/source-maps/BUILD.md) are archival; use the shared build guide for migrated Lean reproduction.
