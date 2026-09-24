# Reliable productive operation of coupled autocatalytic reactors under mechanistic refinement

[Read the paper](../../../Theory/Production/P051-coupling-refinement.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

When does a chemical reactor retain useful operation after it is coupled to other reactors and an effective reaction is replaced by an explicit intermediate mechanism? For a specified reversible autocatalytic exporter, we prove a finite-mission guarantee that includes recovery after molecular withdrawal, loss and refill, collected product, food input and gross reaction service.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 716 selected modules, including shared dependencies. 18 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

The refined deterministic and finite-count mission results, returned-history construction, connected witness and food-to-output bounds have formal support. The six-species probability theorem, Propositions 6–8 and service/duration consequences are conventional. The whole manuscript is not claimed formally verified. The claim map separately labels eleven publication interfaces, six companion-source references and one earlier supporting witness.

[Publication source-selection review](../../migration/selection-reviews/P051.md) records the final source closure and any excluded drafts.

Selected entry points:

- [Publication.lean](../../proofs/RAF1519/Publication.lean)
- [Repeated.lean](../../proofs/RAF1519/Refinement/Repeated.lean)
- [RelaxedMission.lean](../../proofs/RAF1519/Refinement/RelaxedMission.lean)
- [ReturnedHistory.lean](../../proofs/RAF1519/Refinement/ReturnedHistory.lean)
- [MissionAccounting.lean](../../proofs/RAF1519/Refinement/MissionAccounting.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
