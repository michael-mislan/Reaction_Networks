# Exact common-activity compatibility for autocatalytic junction–path assemblies: boundary reduction, a rational decision algorithm, and operating certificates

[Read the paper](../../../Theory/Thermodynamics/P033-junction-path-compatibility.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Autocatalytic cores that are each realizable in isolation need not be realizable together: under thermodynamically consistent mass action, every reaction that involves a species sees the same activity of that species, and the stoichiometric powers of the activities constrain both the direction and the magnitude of every current.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 25 selected modules, including shared dependencies. 17 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Examples.lean](../../proofs/ThermoCoreCompatibility/MultiInterface/Examples.lean)
- [JunctionAssembly.lean](../../proofs/ThermoCoreCompatibility/MultiInterface/JunctionAssembly.lean)
- [PathReconstruction.lean](../../proofs/ThermoCoreCompatibility/MultiInterface/PathReconstruction.lean)
- [PostproofRoot.lean](../../proofs/ThermoCoreCompatibility/MultiInterface/PostproofRoot.lean)
- [Root.lean](../../proofs/ThermoCoreCompatibility/MultiInterface/Root.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
