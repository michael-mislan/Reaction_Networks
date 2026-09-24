# Certifying complete families of irreducible autocatalytic sets is co-W[P]-complete

[Read the paper](../../../Theory/Algorithms/P013-complete-family-certification.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

An irreducible reflexively autocatalytic and food-generated set (irrRAF) is an inclusion- minimal self-sustaining reaction subsystem of a catalytic reaction system.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 37 selected modules, including shared dependencies. 4 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Publication.lean](../../proofs/AllIrrRAFCert/Publication.lean)
- [CliqueToRAF.lean](../../proofs/AllIrrRAFCert/Hardness/CliqueToRAF.lean)
- [Encoding.lean](../../proofs/AllIrrRAFCert/Hardness/Encoding.lean)
- [EncodingSize.lean](../../proofs/AllIrrRAFCert/Hardness/EncodingSize.lean)
- [GraphAdapter.lean](../../proofs/AllIrrRAFCert/Hardness/GraphAdapter.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
