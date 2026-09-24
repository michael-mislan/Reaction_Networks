# Theorem concordance and frozen evidence

The main paper contains only the classification's final mathematical path. Numbered statements below refer to `paper.tex`. All paths in this table are relative to `proofs/IrrRAFEnumeration/`. Namespace prefixes are shown where they differ. A prose explanation of an existing formal theorem is not a new verification of the prose itself.

| Paper component | Lean evidence | Level |
|---|---|---|
| Theorem 1, exact iff | `Classification.lean`, `IrrRAFEnumeration.outputPolynomialEnumeration_iff_P_eq_NP` | Machine-formalized, no outer premises |
| Encoding and uniform quantifiers | `EnumerationContract.lean`, `Enumerates`, `OutputPolynomialEnumeration`, `outputBits_length` in `IrrRAFEnumeration.EnumerationContract` | Literal formal contract |
| RAF closure and minimality | `proofs/RAF/Core/Closure.lean`, `proofs/RAF/Core/RAF.lean`; `RAFCompletion.lean`, `mem_irrRAFFamily`, `hasRAFWithin_iff_contains_irrRAF` | Lean finite semantics |
| Lemma 4, exact completion query | `PositiveCompletion.lean`, `IrrRAFEnumeration.PositiveCompletion.available_univ_iff_missing`, `available_mono` | Lean finite theorem |
| Lemma 5, support encoding | `PositiveSupportedTrace.lean`, `isRAF_iff_supported`; `PositiveCompletionCNF.lean`, `formula_eval_iff`, `formula_sound`; `PositiveCompletionReduction.lean`, `formula_complete`, `formula_satisfiable_iff` | Lean finite SAT correspondence; compiler charged by machine modules |
| Lemma 6, minimal accepted choices | `SATCompletion.lean`, `IrrRAFEnumeration.SATCompletion.minimal_eval_iff` | Lean finite theorem, hypothesis n >= 2 |
| Lemma 7, mandatory auxiliary cycle | `CircuitSource.lean`, `IrrRAFEnumeration.CircuitSource.raf_contains_all_aux` | Lean finite theorem |
| Lemma 7, reset cannot self-enable | `CircuitClosure.lean`, `raf_output_reached_without_reset`, `isRAF_iff_all_aux_and_output` | Lean food-closure theorem |
| Lemma 7, whole family and minimality | `CircuitBijection.lean`, `canonical_irreducible_iff`; `SATSource.lean`, `accepts_encode_iff_eval`; `SATReduction.lean`, `sourceSet_irreducible_iff`, `irreducible_iff_exists_sourceSet` | Exact Lean family correspondence |
| Known small output | `SATFamily.lean`, `baseline_card`, `baseline_subset_irrRAFFamily`, `irrRAFFamily_eq_baseline_iff_unsat`; `SATCountTimeout.lean`, `irrRAFFamily_card_eq_iff_cnf_unsat` | Lean finite count equality and encoded length |
| Lower-bound machine | `SourceEnumeratorRun.lean`, `source_enumerator_no_case`; `SATMembership.lean`, `SAT_mem_P_of_sourceCountBound`; `NegativeClassification.lean`, `P_eq_NP_of_outputPolynomialEnumeration` | Actual source compiler, bounded machine simulation, syntax guard, SAT NP-completeness |
| Lemma 8, filtered deletion | `PositiveCompletion.lean`, `sweep_minimal`, `minimal_available`, `sweep_new_minimal`, `raf_sweep_new` | Lean finite algorithm correctness |
| Uniform prepared machine | `CompletionUniformEnumerationCost.lean`, `preparedEnumeration_polynomial`; `CompletionConditionalEnumeration.lean`, `preparedEnumeration_of_P_eq_NP` | Fixed machine and polynomial extracted before CRS quantification |
| Original-input entry | `CompletionOriginalInput.lean`, `originalInitializer_correct`, `initialFinalWork_eq` | Literal initial tapes, fixed machine, explicit polynomial |
| Arbitrary identifiers | `CompletionLabelTransport.lean`, `enumerates_of_finEnumerates` | Closure/minimality and exact input/output bits transported |
| Positive root direction | `Classification.lean`, `outputPolynomialEnumeration_of_P_eq_NP` | Initializer and prepared machine composed |

The publication adds no Lean module and alters none of these proofs. The finite deletion/essentiality identities in `followups.md` reuse `hasRAFWithin_iff_contains_irrRAF`; the model-assisted invariant is a separate conventional proof. The coNP/NP completeness consequences in that file are conventional complexity arguments using the verified SAT source, not additional compiled machine-level declarations. The experimental Python implementation and Z3 results are empirical/reference evidence, not kernel evidence.

## Frozen verification record

- Root: `IrrRAFEnumeration.outputPolynomialEnumeration_iff_P_eq_NP`.
- Strict successful receipt: `../../campaign_2026_09_08/classification.verify.json` relative to the project root's publication directory layout; repository path is `problem_workspaces/RAF_polynomial_enumeration_irrRAFs/campaign_2026_09_08/classification.verify.json`.
- Verification accepted the exact root and positive direction; warnings were errors, exit code 0, elapsed 66.297 seconds.
- Root outer binders: none. Axioms: `Classical.choice`, `Quot.sound`, `propext` only.
- Toolchain: `leanprover/lean4:v4.30.0`.
- Frozen `mathlib4_project/lake-manifest.json` SHA-256: `a8df0b606ec258561c226df89856884be433c19b49fb0a27335d69bb2b6e9fac`.
- Root source SHA-256: `3aee5560a7b19cdd7f2d2ef5e5806989fe0758a8b899f780821d4d5aadd0d473`.
- Root artifact SHA-256: `1bbc72c4bf4b5b44a23ee9aab87014f985f4c007160c796e0ef307b455d2925c`.
- The publication pass reran `completion_evidence_audit.py`: PASS, root and all 378 local source/artifact dependency pairs match the receipt. This freshness audit is distinct from compilation.
- The original successful receipt was preserved. No new proof dependency required recompilation.
- AGC's canonical authority record still requires authority-integrator binding. It does not invalidate the local strict proof, and this publication does not claim to have changed protected theorem-graph status.

## Scope checks

The lower bound uses the circuit/SAT source, including all clause-index/choice-index rule pairs and one reset. It does not use the different Minimum Axiom Set source. Its instances have singleton food and one nonfood catalyst per reaction, but no extra restricted-chemistry classification is asserted. The source input padding is from the actual library SAT encoding. The count-based timeout uses the unsatisfiable output size; it makes no assertion that satisfiable cases finish by that deadline.

The supported-trace clause pattern is one-way, not an equivalence encoding of every closure row. The proof establishes inclusion in real closure by induction and completeness through canonical closure rows. The upper minimizer asks the avoiding query throughout. The machine's original-input prefix and byte-preserving label transport remove prepared-input and per-instance advice premises. The output is count-first; no polynomial-delay statement is included.
