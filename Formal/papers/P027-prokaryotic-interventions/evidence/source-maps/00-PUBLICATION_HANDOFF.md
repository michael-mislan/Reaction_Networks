# Publication handoff

The original finite case-study guide remains **64/64 PASS**. The separate requested postproof follow-ups are **16/16 PASS**. The combined theorem is `RAFBiochemicalLiteral.publication_result` in `proofs/RAFBiochemicalInterventions/PublicationResult.lean`. Strict verification compiled the current dependency closure, checked the exported interface and axiom dependencies, and reported no warning, admitted proof or unproved custom axiom.

## Deliverables

- `certified_selective_interventions.pdf`: publication-style paper containing the final critical proof path, conventional proofs, three vector diagrams and primary-source bibliography.
- `research_supplement.pdf`: complete food, reaction equations, barrier producers, restoration witnesses/ranks, certificate mapping and reproducibility instructions.
- Editable sources: the corresponding `.tex` files, `parent_verification_status.tex`, `references.bib`, and `figures/` with `make_paper_figures.py`.
- Formal and source evidence: `verification/publication.verify.json`, `PUBLICATION_AUDIT.json`, the original `FINAL_AUDIT.json`, and `PDF_QA.json`.
- Research record: `POSTPROOF_LEDGER.md`, `POSTPROOF_CHECKLIST.json`, `POSTPROOF_GRAPH.json`, and the preserved original `FINAL_HANDOFF.md`.

All paper outputs are in this project workspace root. No publication was submitted to a journal or external service.

## What was tested and learned

1. **Parent constructive closure.** Exact computation compared direction sets, not just counts: the constructively activated set equals the maxRAF in the original 9,231-direction source and the 9,227-direction postcut source. The respective maxima contain 2,148 and 2,085 directions, each activated in 23 synchronous layers. The pilot took approximately 0.63 seconds. Those counts and layer totals are exact computational data; the corresponding concrete uniqueness statements are additionally kernel-certified.
2. **The structural proof of uniqueness.** Positive catalyst formulas permit induction through activation ranks. Every closed RAF contains the activated set; two upper-pool certificates show every RAF is contained in the selected maximum. The bounds meet, so each parent has exactly one closed RAF. This closes the requested parent implication without enumerating irreducible RAFs.
3. **Small target support.** Necessary producers and a required NAD catalyst force all ten directions from valine capability. Thus the whole ten-direction subsystem is the only target-producing RAF, despite its two singleton irreducible RAFs. The two closed RAFs are exactly L={0,1,4,7,8} and H={0,...,9}. L and H have the same complete irreducible catalogue but different target capability.
4. **Pooling and ambient dependence.** The source row R_NADs_1 forward is food-enabled because C00003 and Pooling are supplied. Adding it activates all eleven directions. The augmented subsystem has one closed RAF; its literal embedding forces H into every parent closed RAF. The parent maximum is the common least parent closed extension of L and H. The two small closed subsets therefore cannot be interpreted as two parent organizations or concentration states.
5. **Environmental robustness.** The 18-species siphon is independent of food except for disjointness. Its negative conclusion survives arbitrary catalyst replacement, further deletions and added reactions respecting the same siphon condition. Under food enlargement outside the siphon and catalyst weakening, the original three restoration witnesses and methionine witness survive, proving robust selective inclusion-minimality.
6. **An actual boundary, not a generic warning.** Adding C00141 to food admits the certified four-direction postcut valine RAF [7,8,4,5]. This does not assert rescue by every barrier species. Catalyst strengthening is not included in positive witness robustness.
7. **Firing and kinetics.** The finite firing induction is formalized. The paper separately explains the conventional invariant-face consequence for nonnegative locally Lipschitz reactant-respecting kinetics, crediting the existing siphon literature. Continuous ODE semantics are not represented as a Lean theorem. Neither the structural nor kinetic argument proves depletion of initially present barrier species.

## Computational diagnostics and the successful representation

Early parent source-tree representations exceeded 300/180-second bounds. Replacing the tree with one global array proved the representation equality but did not solve lookup reduction; a representative certificate still exceeded 120 seconds. Balanced symbolic rank functions also made the source large. Bit-plane integer tables and source blocks of 128 directions reduced the representative pilot to 12.875 seconds. The same four finite predicate scans were partitioned into 73 reaction blocks and 23 molecule blocks; these are bounded checks of the exact theorem inputs, not an enumeration of additional mathematical cases.

The first complete parent pass was rejected only for two unused simplification arguments; removing them yielded a warning-free receipt. A postcut attempt failed with a process-level error and no Lean diagnostic during observed system memory pressure. The bounded follow-up disabled asynchronous elaboration and exposed a simplifier mismatch after unfolding the deletion filter. Stating the block lemmas with the matching filter head closed the final assembly and yielded the clean 280.172-second receipt. Other agents' processes and dependency pins were not changed. No failure was relabelled as a mathematical counterexample or a successful proof.

AGC checkpoints were used at entry, structural changes, failures and handoff. They were helpful for identifying stale proof-input bindings and producing the exact proof-neutral reconciliation action. Their mathematical guidance continued to point to an abandoned Mathlib draft and did not contribute to the successful literal-certificate proof. AGC status is not a substitute for the strict kernel receipt.

## Scope and remaining nonclaims

This completes the supplied finite-source result and the bounded postproof follow-ups. It is not a claim to solve an unnamed universal literature conjecture. The pooled source is not organism-specific, and the parser and biological annotations are independently audited rather than kernel-verified. The parent irrRAF catalogue remains partial; global minimum intervention cost is not proved. Those are separate tasks, not missing premises of the delivered theorem. Unique closed-RAF structure does not imply a unique concentration equilibrium, growth or kinetic persistence.

Discovery-only lemmas, failed routes, scoreboards and process history were excluded from the main article. Their useful diagnostics remain here and in the ledger. Every final PDF page was rendered and inspected; the QA record binds that inspection to the delivered PDF hashes.

## Verification timings

- `parent_closed`: 126.921 seconds.
- `cut_closed`: 280.172 seconds.
- `publication`: 14.031 seconds.

Finalized 2026-09-14T18:59:06.196683+00:00.

Final AGC handoff checkpoint: CURRENT after proof-neutral same-frontier reconciliation. Its freshness subtype still records an older failed declaration attempt and its route preview names the abandoned ValineSmall draft; neither overrides the current warning-free PublicationResult receipt. AGC was useful for binding freshness, not for selecting the successful proof route.
