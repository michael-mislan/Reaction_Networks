# Current publication theorem index

The strongest current result is co-W[P]-completeness and coNP-completeness,
with finite reductions compiled in Lean and conventional complexity arguments
in the paper. The final public declaration is
`AllIrrRAFCert.axiom_iff_not_exactCertification` in `Publication.lean`.
`Main.lean:axiom_reduction` packages the source equivalence, validity, and
exact parameter. The current receipt is
`results/postproof_terminal_verification.json`, authenticating four declarations
and all 36 dependencies. The former Main receipt is historical.

The complete current WPHardness module inventory, declaration concordance,
and formal/conventional boundary are in `publication/FORMAL_SUPPLEMENT.md`.
The original Clique reduction remains useful for the ETH consequence recorded
in `POSTPROOF_FOLLOWUPS.md`.

# Retained Clique theorem index

All new declarations are in `AllIrrRAFCert.Hardness`, except the final package
and completeness interface in `AllIrrRAFCert`.

| File | Declarations | Role |
|---|---|---|
| proofs/AllIrrRAFCert/Hardness/Source.lean | crs, cat, guard; signal_origin, guardCat_origin, globalCat_origin, colorOK_origin, pairOK_origin | Literal finite source and unique provenance |
| proofs/AllIrrRAFCert/Hardness/GuardCycles.lean | guard_isRAF, guard_isIrrRAF, guards_injective, irrRAF_without_close_eq_guard | Promise and close/no-close dichotomy |
| proofs/AllIrrRAFCert/Hardness/NoSpurious.lean | extra_contains_close, extra_avoids_guard, extra_omission_pattern, close_forces_pair, extra_implies_clique | Decisive converse |
| proofs/AllIrrRAFCert/Hardness/CliqueToRAF.lean | witness_isRAF, clique_implies_extra, clique_iff_extra | Three closure layers and finite minimal extraction |
| proofs/AllIrrRAFCert/Hardness/GraphAdapter.lean | compatible_graph_iff, indexed_clique_iff, graph_clique_iff_extra | Standard Mathlib SimpleGraph.IsNClique source |
| proofs/AllIrrRAFCert/Hardness/EncodingSize.lean | reaction_count, molecule_count, parameter_eq, encoding_polynomial | Exact output dimensions and list parameter |
| proofs/AllIrrRAFCert/Hardness/Encoding.lean | encode, encode_food, encode_inputs, encode_outputs, encode_catalysis, encode_list, encoding_card | Explicit Boolean representation |
| proofs/AllIrrRAFCert/Main.lean | AllCertified, listed_promise, extra_iff_not_allCertified, clique_reduction | Terminal source-level reduction |

Reused: `RAF.Frankl.mem_closureAt_imp_food_or_output`,
`RAF.Frankl.catalyzedFromClosure_iff_productGraph`,
`IrrRAFEnumeration.CircuitSource.cyclic_all`,
`IrrRAFEnumeration.exists_minimal_subset`, and
`MinRAFApprox.SetCoverSource.IsIrreducibleRAF`.

Strict results are under `results/`. A failed receipt is not proof evidence.
The terminal receipt must authenticate the current Main.lean declaration.
