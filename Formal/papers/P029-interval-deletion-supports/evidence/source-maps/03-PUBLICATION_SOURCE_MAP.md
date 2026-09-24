# Manuscript and consequence source map

All paths below are repository-relative. The main paper is independent of optional post-proof consequences; theorem names and experiment histories are kept here instead.

## Paper critical path

| Paper statement | Lean source/declaration |
|---|---|
| Theorem 2, realizability iff intrinsic deletion | proofs/DigraphRealizability/IntervalDeletion.lean: digraphRealizable_iff_intrinsicPeeling |
| Eligibility equals exclusion from the existing interior | IntervalDeletion.eligible_iff_interior |
| Least-model facts and first half of Lemma 3 | HornClosure.subset_closure, closure_le, closure_models, normalize |
| Replacement, second half of Lemma 3 | ResidualNormalization.replacement, extend_completion |
| Finite completeness | HornElimination.elimination_complete |
| Soundness | HornElimination.elimination_sound |
| Exact graph reconstruction | ComplementBridge.reconstruct_row, reconstruct_models, reconstructed_support |
| Complementary/direct procedure equality | IntervalDeletion.Eliminates.toPeels, Peels.toEliminates |
| Residual-policy completeness | ResidualPolicy.policy_complete (complementary minimal-residual formulation) |
| Complete Boolean checker | TraceChecker.digraphRealizable_iff_checked_trace |

Historical root receipts: root_verification.json and checker_verification.json. Current root recheck: publication_root_verification.json. The aggregate publication receipt is publication_verification.json; its dependency entries identify the exact hashes of all additional compiled modules.

The exported root requires only a finite type, decidable equality, and the target finite family. It has no assumed completion, normalization, or successful-trace hypothesis. Standard axioms are propext, Classical.choice, and Quot.sound.

## Consequences (excluded from the main paper)

| Result | Declaration/module |
|---|---|
| Exact roots and length | TraceConsequences.exact_trace_roots, exact_trace_length |
| Reconstructed interior equality | RAFConsequences.reconstructed_interior_eq |
| Family determines loops | TraceConsequences.realizing_loops |
| Elementary fixed-family criterion | RAFConsequences.elementary_iff_peeling |
| Antimatroid/peelable factorization | RAFConsequences.raf_iff_antimatroid_peeling |
| Single-vertex elimination | Projection.single_vertex_projection |
| Arbitrary elimination | Projection.arbitrary_projection |
| Exact graph on the visible subtype | PublicationResolution.source_projection_on_visible (with the lightweight projection kernel) |
| Auxiliary-vertex impossibility | Projection.hidden_vertices_cannot_rescue |
| Projected interior identity | Projection.projected_interior |
| Induced deletion and independent products | Composition.induced_deletion, independent_product |
| Shared-ground intersection obstruction | Composition.conjunction_intersection, conjunction_not_realizable |
| General-CRS realization of the obstruction | Composition.conjunction_general_realizable (existing marker constructor) |
| Dynamic Hall matching | Obstructions.residual_matching |

The factorial node bound and its representation-specific costs are proved in POSTPROOF_SUPPLEMENT.md. The explicit three-reaction food-catalyzed conjunction construction and the six-coordinate failure of initial matching also have ordinary proofs there. Their finite experiments are in consequence_results.json and pilot_results.json. They are not advertised as separately compiled theorems.

Projection uses a lightweight predicate definitionally identical to the existing RAF PredSupported. PublicationResolution.vertexSupported_iff_predSupported proves that identity and source_projection_on_visible exports the exact visible-ground theorem in the existing predicate. This import boundary reduces memory use without changing the mathematics.

## Reproduction

Use .venv/Scripts/python.exe for all repository Python work. Run verify_proof.py from the repository root; it enforces the pinned mathlib working directory. A full aggregate command is:

```powershell
$env:LEAN_NUM_THREADS='1'
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/DigraphRealizability/PublicationResolution.lean --declaration DigraphRealizability.publication_resolution --timeout 900 --output problem_workspaces/RAF_characterization_digraph-realizable_union_closed_families/publication_verification.json
```

The extended timeout covers serial dependency compilation, not a numerical search. Memory-allocation failures on concurrent attempts motivated serial verification.

Build the paper with build_paper.ps1 in this problem workspace. It compiles twice, rejects overfull boxes or unresolved references, writes the PDF to the workspace root, and renders all pages for inspection. The bibliography is embedded in the TeX source for a two-pass standalone build and also supplied in references.bib.

No new root axiom, native-decide proof, dependency update, or bulk formal census is used.

