# Reliable copying of chemical states: finite-molecule guarantees and molecular redundancy

[Read the paper](../../../Theory/Inheritance/P017-reliable-chemical-copying.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Chemical multistability supplies candidate memory states, but a list of stable states does not say whether a finite population of molecules copies a state reliably through growth, division and recovery.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 562 selected modules, including shared dependencies. 10 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

The constructed copying and nominal Semenov certificates use native evaluation for finite-table checks. Their historical reports include native-evaluation axioms in addition to the standard three. The scaling theorem has a separate, standard-axiom proof. These are distinct trust bases.

Selected entry points:

- [Publication.lean](../../proofs/CompositionalMemory/Publication.lean)
- [ReversibleCertificate.lean](../../proofs/CompositionalMemory/ReversibleCertificate.lean)
- [SemenovMeasuredEncoding.lean](../../proofs/CompositionalMemory/SemenovMeasuredEncoding.lean)
- [ReversibleDivisionInventory.lean](../../proofs/CompositionalMemory/ReversibleDivisionInventory.lean)
- [ReversibleDimensionalRates.lean](../../proofs/CompositionalMemory/ReversibleDimensionalRates.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
