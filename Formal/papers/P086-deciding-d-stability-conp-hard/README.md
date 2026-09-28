# Deciding D-stability is coNP-hard

[Read the paper](../../../Theory/D-Stability/P086-deciding-d-stability-conp-hard.pdf) · [Manuscript](manuscript/main.tex) · [Claim map](claims.json) · [Build instructions](../../BUILD.md)

An explicit reduction from PARTITION establishes coNP-hardness of D-stability and NP-hardness of strict diagonal destabilization for rational matrices. The construction uses a four-state core with first-order attachments.

**Formalization:** The matrix reduction, stability dichotomy, encoding bounds, contact certificates, and time-scale follow-ups are formalized. The complexity conclusion also uses the conventional NP-completeness of PARTITION and the bit-complexity model. The hardness is weak, in the binary-encoding sense.

Selected Lean sources:

- [Paper.lean](../../proofs/DStabilityHardness/Paper.lean)
- [All.lean](../../proofs/DStabilityHardness/All.lean)

[Verification scope](../../VERIFICATION.md) · [All papers](../../../README.md)
