# Final-paper theorem concordance

All declarations below have namespace `HordijkSteelThreshold`, except the underlying source definitions in `RAF.Concrete`. Module filenames are under `proofs/HordijkSteelThreshold/` at the repository root. The strict compilation receipts and current source/artifact hashes are recorded in `verification_manifest.json`.

The mathematical root is `full_corrected_transition` in `CriticalWindowSource.lean`. The publication interface `publication_resolution` states the limiting infinite-product event literally. The additional corollaries are separately authenticated; they are not inferred only by reading the conjunction's prose description.

| Paper result | Lean module and declaration(s) | Evidence |
|---|---|---|
| Theorem 2.1, (2) | `CriticalWindowSource.full_corrected_transition`; `PublicationResolution.publication_resolution` | Original `verification/critical_window_source.json`; new `publication_verification/PublicationResolution.json` |
| Molecular and reaction counts (1) | `PolymerCounts`; `RAF.Polymer.Counts` | Local dependency hashes in reproduction manifest |
| Survival definition (3) | `SprinkledSeedLowerBound` / definition `staticSurvival`; `ReversibleMeasurableEvents` | Definition and measurable-event modules in dependency closure |
| Lemma 3.1; escape approximation (4) | `ReversibleFiniteCertificates`; `ReversibleEscape.reversible_escape_iff_cap`; `ReversibleEscapeProbability.finite_static_escape_probability_tendsto` | Local dependency compilation; original final audit |
| Proposition 4.1, (5)–(6) | `GatewayProbability.rafProbability_limsup_le_gateway_ceiling`, `card_seedCoord_exact`, `seedClosedProbability_tendsto_exp` | Original gateway receipt; rebuilt dependency |
| Lemma 5.1, (7) | `ScalarHistoryDistribution.activeTrace_map_eq_scalar`; `NestedColumnHistory`, `HistoryProductLaw` | Rebuilt history-distribution dependency chain |
| Lemma 6.1, (8)–(9) | `SourceStaticRAFBound.canonical_raf_ge_static_barrier`; `SourceTerminalRAF` | Rebuilt dependency |
| Prefix openness limit (10) | `TransitionLowerBound.source_probability_eventually_above`; canonical prefix limit modules | Rebuilt dependency |
| Theorem 7.1, (11) | `StaticBulk.static_bulk_near_full` | Rebuilt dependency |
| Count and failure estimates (12)–(15) | `WordMoleculeContourCount.wordMoleculeContourEnvelope_card`; `WordContourProbability.staticReaction_contour_failure`; `WordRootedMass.measure_rootedMolecularWords_deficit` | Rebuilt dependencies; geometric proof in Appendix A |
| Positive survival, Section 7 | `TransitionConsequences.staticSurvival_pos`; original positive-survival producer in final root chain | `publication_verification/TransitionConsequences.json` |
| Lemmas 8.1–8.2 | `ReversibleRecordWords.unbounded_record_words`; `RecordTargetTrial.record_target_support` | Record/trial construction in final dependency closure |
| Theorem 8.3, (16)–(19) | `SameParameterRichness.same_parameter_target_ae`, `unbounded_missing_target_null`; `InfiniteClosureDichotomy.survival_iff_complete_ae`, `finite_or_complete_ae`, `staticSurvival_eq_complete` | `publication_verification/InfiniteClosureDichotomy.json`; underlying rebuilt dependencies |
| Finite witnesses (20) | `InfiniteStaticLaw.finite_static_seed_probability_tendsto`; `ReversibleFiniteCertificates`; `SameParameterRichness.staticSurvival_le_same_parameter_seed` | Rebuilt dependencies |
| Theorem 9.1, (21)–(22) | `SeedSurvivalApproximation.seed_probability_le_survival_add_error`; `InfiniteClosureDichotomy.uniform_seed_survival_approximation` | Original seed receipt and new dichotomy receipt |
| Theorem 9.2, (23)–(24) | `StaticSurvivalContinuity.staticSurvival_tendsto`; `StaticSurvivalLeftContinuity.staticSurvival_le_left` | Original continuity receipt; rebuilt dependencies |
| Endpoint at one | `OuterScalingRegimes.staticSurvival_one`, `transitionLimit_infinity` | `publication_verification/OuterScalingRegimes.json` |
| Lower bound (25)–(29) | `TransitionLowerBound.transition_liminf_lower`; same-parameter seed comparison as described below | Rebuilt dependencies; original root receipt |
| Upper bound (30)–(32) | `TransitionUpperBound.transition_limsup_le_finite_escape`, `transition_limsup_upper` | Rebuilt dependencies |
| Fixed-intensity limit | `CorrectedTransition.rafProbability_tendsto_transitionLimit`, `corrected_transition` | Original corrected-transition receipt; rebuilt dependency |
| Arbitrary-sequence squeeze (33) | `VariableIntensityTransition.variable_intensity_transition`, `critical_window_transition`; `CanonicalParameterMonotonicity` | Original variable-intensity receipt; rebuilt dependencies |
| Exact normalization (34) | `CriticalWindowSource.critical_window_parameter_exact` | Original root receipt; rebuilt dependency |
| Corollary 11.1, outer regimes | `OuterScalingRegimes.sublinear_regime`, `superlinear_regime` | `publication_verification/OuterScalingRegimes.json` |
| Continuity, monotonicity, strict bounds, zero endpoint | `TransitionConsequences.continuous_transitionLimit`, `transitionLimit_mono`, `transitionLimit_mem_Ioo`, `transitionLimit_zero` | `publication_verification/TransitionConsequences.json` |
| Refutation of Eq. (21) of Hordijk–Steel | `TransitionConsequences.no_finite_step_threshold` | Same receipt, independently authenticated declaration |
| Lemma A.1 | `WordDiamondCuts.wordDiamond_integrate` | Rebuilt dependency |
| Lemma A.2 | `WordBondConnected.wordBond_diamond_connected`; `WordDiamondDegree`; `WordContourCounting` | Rebuilt dependencies |
| Lemma A.3 | `WordMolecularAnchors.wordBond_molecular_anchor_radius` | Rebuilt dependency |
| Lemma A.4 | `WordMoleculeContourCount.wordMoleculeContourEnvelope_card`, `wordBond_mem_molecule_envelope` | Rebuilt dependency |
| Lemma A.5 and greedy selection | `WordDetourLiteralPaths.wordDetourSource_reach_parent`; `WordDetourIncidence`; `DisjointDetourSelection.exists_disjoint_detours` | Rebuilt dependencies |

## Mathematical compression in the paper

The displayed lower bound uses the now-available same-parameter richness theorem directly. At fixed `b` and `m`, seed acquisition minus `1/m` bounds near-full mass; the canonical catalytic barrier then bounds the source probability. This removes an independent-sprinkling intermediate lemma from the prose. The original compiled lower-bound producer retains that intermediate in its dependency graph. The endpoints and exact inequalities agree; the manuscript does not claim that every prose sentence is a line-for-line translation of one Lean module.

Several constants and inequalities in a displayed proof are elementary specializations or arithmetic consequences of the listed declarations, rather than individually named exported theorems. The table records this at the level of the mathematical result; a dependency receipt is not falsely described as an independently authenticated declaration interface.

All receipt paths in the Evidence column are relative to `../transition_campaign/`. The full manifest distinguishes normal strict verification from the isolated local rebuild. Kernel verification and the explicit source-model definitions jointly support the scope claim; AGC progress files themselves are not theorem evidence.
