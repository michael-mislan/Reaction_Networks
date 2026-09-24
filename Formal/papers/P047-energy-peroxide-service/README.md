# Energy service and peroxide handling in a proteome-constrained red-cell model: exact inventory certificates, a certified turnover plateau, and kinetic limits

[Read the paper](../../../Applications/Metabolic-and-Redox-Function/P047-energy-peroxide-service.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Whether stored red cells can sustain an ATP-dependent service while consuming an oxidative challenge is usually approached through a metabolic flux envelope.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 30 selected modules, including shared dependencies. 7 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [FiniteCertificate.lean](../../proofs/StoredRedCells/FiniteCertificate.lean)
- [PairedRecovery.lean](../../proofs/StoredRedCells/PairedRecovery.lean)
- [S7Application.lean](../../proofs/StoredRedCells/S7Application.lean)
- [S7Certificate.lean](../../proofs/StoredRedCells/S7Certificate.lean)
- [S7Source.lean](../../proofs/StoredRedCells/S7Source.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
