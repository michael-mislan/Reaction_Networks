# Inherited chemical-state selection across serial transfers: a finite stochastic construction with a machine-checked proof

[Read the paper](../../../Theory/Evolution/P044-serial-transfer-selection.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A heritable chemical difference between compartments supports repeated selection only if the selected state survives the operations that separate one competition from the next: growth on a shared resource, transfer of a random subset of intact compartments, a recovery interval without growth, and replenishment.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 186 selected modules, including shared dependencies. 29 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BatchChemicalProbability.lean](../../proofs/SerialTransferSelection/BatchChemicalProbability.lean)
- [BatchDeadlineProbability.lean](../../proofs/SerialTransferSelection/BatchDeadlineProbability.lean)
- [BatchJointProbability.lean](../../proofs/SerialTransferSelection/BatchJointProbability.lean)
- [BatchOddsProbability.lean](../../proofs/SerialTransferSelection/BatchOddsProbability.lean)
- [BatchService.lean](../../proofs/SerialTransferSelection/BatchService.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
