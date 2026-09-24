# Exact interfaces for modular autocatalytic reaction networks: amplification prices, catalyst-aware cores, degradation onset, and boundary traces

[Read the paper](../../../Theory/Structural/P011-modular-interfaces.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Modular reasoning about an autocatalytic reaction network is trustworthy only when the environment cannot exploit information that a module summary discarded.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 65 selected modules, including shared dependencies. 8 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

[Publication source-selection review](../../migration/selection-reviews/P011.md) records the final source closure and any excluded drafts.

**Trust base:** the recorded declaration audit records 3 native-evaluation axioms for finite computations beyond Lean's three standard classical axioms. The exact names and per-declaration dependencies are recorded in the [axiom report](../../migration/clean-verification.json).

Selected entry points:

- [Star.lean](../../proofs/CoreInteraction/Degradation/Star.lean)
- [CoreInteraction/Main.lean](../../proofs/CoreInteraction/Main.lean)
- [MAFComposition/Main.lean](../../proofs/MAFComposition/Main.lean)
- [SourceDirectEnumeration.lean](../../proofs/AutocatalyticCS/SourceDirectEnumeration.lean)
- [DegradationControl/Main.lean](../../proofs/DegradationControl/Main.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
