# Publication handoff — 14 September 2026

The research paper is **Intrinsic_Interval_Deletion_Characterization.pdf**, in this workspace root. Its editable source is **Intrinsic_Interval_Deletion_Characterization.tex**. The five-page paper presents only the intrinsic characterization, the normalization/replacement lemma needed for completeness, soundness, exact reconstruction, and formal-verification scope. It contains no discovery census, failed-route examples, optional RAF/projection/Hall results, or campaign administration. The residual-policy formulation follows directly from the same completeness proof.

## Mathematical endpoint and contribution

For any finite ground set E and family F, same-ground digraph support realizability is equivalent to a successful intrinsic rooted interval-deletion sequence. A successful sequence reconstructs predecessor rows on exactly E. Completeness follows by preserving a single-head completion while replacing one violated rule body by a minimal residual model. This is the key structural step: closure under the accepted rules, rather than equality of the original body with the residual, justifies replacement.

The prior-art account was corrected against the published source. Liberatore already provides complete single-head reconstruction and explicitly handles unit clauses. The paper claims the direct intrinsic formulation, its completion-preserving proof and the verified graph connection; it does not claim priority for general Horn reconstruction, unique recovery, or unspecified polynomial recognition.

## Follow-up deliverables and coverage

PUBLICATION_REGISTER.md tracks the 16 requested post-proof deliverables separately from the historical guide score of 35/40 at primary-root completion. The historical score is retained as a dated record, not an indication of an unresolved primary theorem.

PUBLICATION_SOURCE_MAP.md gives exact theorem-to-source coverage. The added Lean modules establish:

- exact accepted-trace roots and length, and the forced self-loop locations;
- completeness for an arbitrary fixed valid residual policy;
- elementary-CRS realizability iff intrinsic peeling, reconstructed interior equality, and the existing general RAF factorization expressed with peeling;
- single-vertex and arbitrary projection, a graph on the exact visible subtype, hidden-vertex impossibility, and the projected interior identity;
- induced deletion, independent products, the shared-ground intersection obstruction and its general-CRS realization;
- an injective assignment of fresh forced heads to minimal residuals, yielding dynamic Hall necessity.

POSTPROOF_SUPPLEMENT.md contains complete ordinary proofs and explains every requested consequence. Its factorial search-node count and representation costs, finite Hall cardinal inequality, explicit three-reaction conjunction realization, and six-coordinate failure of initial matching are ordinary mathematical arguments. They are not presented as separate Lean-verified declarations. The general-CRS existence theorem is formally verified through the existing antimatroid constructor. No unresolved mathematical extension is required for the paper's theorem.

## Experiments and lessons

The canonical numerical smoke suite passed. The guarded consequence experiment completed in 7.578 seconds: 263,714 single-vertex projections of all labelled graphs through four vertices had zero family mismatches; all 256 independent products passed. It also checked the intersection obstruction and the explicit three-reaction food-generation construction. Scripts and results are consequence_experiments.py and consequence_results.json. The original pilot and its explanatory six-coordinate obstruction are retained.

The projection tests checked the loop/no-loop boundary and the lifting cases before accepting the general formalization. The conjunction example separates support alternatives from food-generation conjunctions. The six-coordinate example shows why initial matching does not ensure the connectivity needed for complete derivations. Numerical counts support implementation conventions; they do not discharge the universal theorem.

Concurrent Lean attempts encountered memory-allocation failures. Verification was serialized with LEAN_NUM_THREADS=1, and projection was separated from the heavy RAF import chain using a definitionally identical predicate plus a proved source bridge. Subsequent name-substitution errors were fixed without changing theorem statements. A locked LaTeX transcript was bypassed by building in tmp_pdf/release; no dependency updates were made. The running ledger is logs/2026-09-14.md, supplemented by the original FINAL_HANDOFF.md and POSTPROOF_SUPPLEMENT.md.

## Reproduction and evidence

The strict root recheck is publication_root_verification.json. Additional receipts are raf_consequences_verification.json, trace_consequences_verification.json and the aggregate publication_verification.json. The aggregate includes 32 local dependencies and exports publication_resolution and source_projection_on_visible. Its successful result must be read together with its exact source hashes; PUBLICATION_AUDIT.json checks all four saved receipts against current sources. The audit is bookkeeping, not substitute kernel evidence.

Run the commands in PUBLICATION_SOURCE_MAP.md with the repository's .venv/Scripts/python.exe. The Lean verifier enforces the frozen mathlib working directory and treats warnings as errors. No sorry, new root axiom, unchecked native computation, or finite-case replacement of universal completeness is used. Standard logical axioms are propext, Classical.choice and Quot.sound.

Run build_paper.ps1 from this workspace to build twice and render all five pages. The final PDF was visually inspected page by page; the final log has no overfull boxes, unresolved references, citation warnings, or PDF destination warnings. Text extraction confirms the end of completeness and both references are present. references.bib accompanies the embedded standalone bibliography.

AGC checkpoints were used for continuity and handoff control. They were helpful in preserving the authored route and avoiding historical failed routes; they supplied no new mathematical insight or proof evidence. The diagnostic canonical graph still reports ROOT in its open cut because formal authority integration is separate. This handoff claims the saved strict Lean result, not an unauthorized change to that graph. No generated-evidence commits or canonical authority edits were made.

## Final acceptance

Post-proof score: **16/16 PASS**. Primary ROOT: **PASS**. Aggregate strict verification completed successfully in 590.344 seconds; both exported declarations use only standard logical axioms. PUBLICATION_AUDIT.json is PASS: all four current receipts and every recorded dependency source hash match. The final PDF has five inspected pages and a clean LaTeX log. No primary mathematical obligation remains. Final AGC checkpoint: CURRENT, saved in PUBLICATION_AGC_CHECKPOINT.yaml; it remains proof-neutral.

