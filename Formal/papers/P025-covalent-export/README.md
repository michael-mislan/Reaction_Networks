# Reliable covalent export from an autocatalytic reactor under driven cleavage: explicit finite-copy operating, output and supply certificates over an exponential horizon

[Read the paper](../../../Theory/Production/P025-covalent-export.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

We prove an explicit reliability theorem for a six-species continuous-flow autocatalytic reactor with reversible substrate binding, templated ligation, duplex release, and an additional maintained-drive cleavage pathway that returns free covalent product to its two food components.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 87 selected modules, including shared dependencies. 31 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [BindingCompetitionComparison.lean](../../proofs/RandomViability/BindingCompetitionComparison.lean)
- [BindingCompetitionCounterHistory.lean](../../proofs/RandomViability/BindingCompetitionCounterHistory.lean)
- [BindingCompetitionDisabledProbability.lean](../../proofs/RandomViability/BindingCompetitionDisabledProbability.lean)
- [BindingCompetitionDrift.lean](../../proofs/RandomViability/BindingCompetitionDrift.lean)
- [BindingCompetitionEntryLaw.lean](../../proofs/RandomViability/BindingCompetitionEntryLaw.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
