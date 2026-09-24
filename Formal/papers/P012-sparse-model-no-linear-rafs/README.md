# Linear-size autocatalytic sets are asymptotically absent in the sparse binary polymer model

[Read the paper](../../../Theory/Emergence/P012-sparse-model-no-linear-rafs.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

In the binary polymer model of Kauffman, molecules are bit strings of length at most n, reactions are ligations and their reverse cleavages, and a random catalysis assignment decides which molecules catalyse which reactions.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 54 selected modules, including shared dependencies. 14 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

The audit distinguishes twelve publication declarations from two adjacent scalar input lemmas. Those two supplementary lemmas are outside the paper and do not establish a growing-intensity RAF theorem. The positive quadratic witness bound cited from the literature is not claimed locally formalized.

[Publication source-selection review](../../migration/selection-reviews/P012.md) records the final source closure and any excluded drafts.

Selected entry points:

- [LiteratureResolution.lean](../../proofs/SparseLinearRAF/LiteratureResolution.lean)
- [PublicationAudit.lean](../../proofs/SparseLinearRAF/PublicationAudit.lean)
- [PolynomialIntensityAudit.lean](../../proofs/SparseLinearRAF/PolynomialIntensityAudit.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
