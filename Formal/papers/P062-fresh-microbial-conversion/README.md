# Certifying fresh microbial conversion from finite challenge records: a sharp two-pool material bound

[Read the paper](../../../Applications/Assays/P062-fresh-microbial-conversion.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A finite record of product collected from a microbial preparation is compatible both with fresh conversion and with release of material that was already present.

**Formalization:** The current 24-page release formalizes the two-pool lower bound, its attaining schedule and exact minimum, the uptake substitute, observation wrapper, design arithmetic and material counterexamples. General interleavings, sensitivity and probability containment retain conventional proofs. Numerical examples are synthetic; biological calibration and substrate-specific attribution are unvalidated premises. Positive certification does not establish viability or future function. The current six-module release supersedes the older workspace draft whose sharpness argument was still conventional. The 35 mapped declarations include two separately identified supporting source lemmas; each has a matching historical declaration interface and standard-axiom probe.

[Historical verification review](../../papers/P062-fresh-microbial-conversion/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 6 selected modules, including shared dependencies. 35 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Source.lean](../../proofs/MicrobialFunctionAssay/Source.lean)
- [Certificate.lean](../../proofs/MicrobialFunctionAssay/Certificate.lean)
- [Sharpness.lean](../../proofs/MicrobialFunctionAssay/Sharpness.lean)
- [Resolution.lean](../../proofs/MicrobialFunctionAssay/Resolution.lean)
- [Design.lean](../../proofs/MicrobialFunctionAssay/Design.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
