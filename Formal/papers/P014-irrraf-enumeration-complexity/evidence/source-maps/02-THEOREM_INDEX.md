# Theorem index

- `MinRAFApprox.SetCoverSource.irreducibleRAF_iff_minimalTransversal` — literal
  CRS hypergraph embedding; inherited and strictly verified.
- `IrrRAFEnumeration.irreducibleRAF_iff_oneDeletion` — one-deletion criterion.
- `IrrRAFEnumeration.irreducibleRAF_iff_minimal_hasRAFWithin` — irrRAFs are the
  minimal true sets of the monotone RAF-existence predicate.
- `IrrRAFEnumeration.blocker_blocker` — finite blocker involution for clutters.
- `IrrRAFEnumeration.minimal_hitter_eq_singleton_of_common_vertex` and
  `IrrRAFEnumeration.minimal_hitters_card_le_one_of_common_vertex` — if `x`
  lies in every input edge, a minimal hitter containing `x` is exactly `{x}`;
  therefore a family of such minimal hitters all containing `x` has at most
  one member.
- `IrrRAFEnumeration.knownFamily_complete_iff` — generic minimal-hitter
  completeness criterion.
- `IrrRAFEnumeration.irrRAF_blocker_involution` — intrinsic RAF blocker duality.
- `IrrRAFEnumeration.knownIrrRAFs_complete_iff` — exact sharpening of the
  Cartesian-product completeness test.

- `IrrRAFEnumeration.pair_irrRAFFamily_eq` — exact literal pair-CRS realization.
- `IrrRAFEnumeration.two_pow_le_pairCRS_deletion_frontier` — native exponential
  deletion-frontier lower bound.
- `IrrRAFEnumeration.source_irrRAFFamily_eq_image` — whole-family,
  output-preserving hypergraph-to-RAF correspondence.
- `IrrRAFEnumeration.source_irrRAFFamily_card_eq_minimalTransversalFamily_card`
  — parsimonious counting reduction.
- `IrrRAFEnumeration.star_leaf_subset_hits_iff_eq` — unbounded batch-exchange
  obstruction for local reverse search.
- `IrrRAFEnumeration.memoryResidualFamily_card` — exact `2^k` lower bound on
  distinct canonical residual families in the choice-memory construction.
- `IrrRAFEnumeration.memory_irrRAFFamily_eq` — exact realization of the
  choice-memory family as the irrRAFs of a compact elementary CRS.
- `IrrRAFEnumeration.memoryCRSResidualFamily_card` — native RAF theorem: the
  `3k`-reaction CRS with exactly `3k` irrRAFs has `2^k` canonical residual
  irrRAF states.
- `IrrRAFEnumeration.missing_minimalTransversal_iff_completionWitness` — exact
  equivalence between an incomplete output list and satisfiability of the
  positive-input/negative-known-output completion CNF.
- `IrrRAFEnumeration.hornCounterexample_not_renamable` — a valid four-vertex
  completion instance whose exact CNF admits no Horn renaming.
- `IrrRAFEnumeration.hornCounterexample_not_qHorn` — executable strict proof
  that none of the `3^4` q-Horn weight assignments certifies that instance.
- `IrrRAFEnumeration.completeBipartite_blocker_eq` — exact classification of
  the two minimal transversals of the complete bipartite edge clutter.
- `IrrRAFEnumeration.completeBipartiteFamily_card` and
  `completeBipartite_blocker_card` — quadratic input size versus two outputs.
- `IrrRAFEnumeration.residual_cross_intersects` — every pair of surviving
  positive and negative clauses in a completion residual still intersects.
- `IrrRAFEnumeration.blocker_subfamily_residual_cross_intersects` — the same
  invariant specialized to any supplied blocker subfamily.
- `IrrRAFEnumeration.fullEdge_blocker_eq_singletons` — exact blocker of the
  one-full-edge clutter.
- `IrrRAFEnumeration.fullEdgeFalseResidualFamily_card` and
  `singletonFamily_card` — `2^k` ambient residuals despite only `k` outputs.
- `IrrRAFEnumeration.minimal_hitter_private_edge` and
  `blocker_private_edge` — every element of a minimal transversal has an input
  edge meeting it nowhere else.
- `IrrRAFEnumeration.private_edge_escape` — every missing hitting set realizes
  an omitted-element/private-edge-repair branch.
- `IrrRAFEnumeration.selfDualStar_blocker_eq` — the star-plus-all-leaves
  family is exactly self-blocking.
- `IrrRAFEnumeration.selfDualStarFamily_card` and
  `starLeaves_self_intersection_card` — this family has exactly `n+3` outputs
  while its all-leaves member intersects itself in `n+2` vertices.
- `IrrRAFEnumeration.bipDiagonal_private_repair` and
  `bipDiagonal_repair_injective` — the complete bipartite obstruction has a
  perfect matching of distinct private repairs despite only two outputs.
- `IrrRAFEnumeration.cliqueMatching_blocker_eq` and
  `cliqueMatching_blocker_card` — the clique-plus-matching family has exactly
  the all-left transversal and its `k` one-coordinate swaps.
- `IrrRAFEnumeration.cliqueMatchingFamily_card_le`,
  `cliqueMatching_private_repair`, and
  `bipRight_subset_of_hits_private_repairs` — quadratic input size and linear
  output coexist with `k` disjoint singleton repairs and repair-cover size `k`.
- `IrrRAFEnumeration.knownBlockerMemberFullCover_isFullCover` — a known
  minimal transversal yields the standard full cover by itself and
  complement-of-one-point regions.
- `IrrRAFEnumeration.knownBlocker_complete_iff_regions` — exact regional
  completeness equivalence for a blocker subfamily under that full cover.
- `IrrRAFEnumeration.strongMemberFullCover_isFullCover` — the ordered
  Boros--Makino construction is a full cover of every minimal transversal;
  the proof uses the least intersection point and its private input edge.
- `IrrRAFEnumeration.filterWithin_strongRegion_card_le_vertexFiber` — every
  surviving blocker member in a strong-cover child contains its distinguished
  vertex, yielding the exact frequency-fiber cardinality bound.
- `IrrRAFEnumeration.strongMemberFullCover_card_le_incidence` — the number of
  strong-cover regions is at most total input incidence.
- `IrrRAFEnumeration.strongBlocker_complete_iff_regions` — exact global
  completion is equivalent to completion in every ordered strong-cover region.
- `IrrRAFEnumeration.states_card_le_rootChargeBudget` — Hall expansion of a
  reached-state family into compatible root triples yields the exact
  `|U|·|F|·|G|` state bound.
- `IrrRAFEnumeration.removedXorCandidates` — polarity-aware root triples whose
  vertex has left the current universe and lies in exactly one of the root
  input/output members.
- `IrrRAFEnumeration.states_card_le_one_add_of_removedXorExpansion` — a unique
  root plus Hall expansion of nonroot polarity charges yields the exact
  `1 + |U|·|F|·|G|` memo-state bound.
- `IrrRAFEnumeration.entryRemovedXorCandidates`,
  `IrrRAFEnumeration.HasChargeExpansion.monoCandidates`, and
  `IrrRAFEnumeration.states_card_le_one_add_of_entryRemovedXorExpansion` —
  first-entry edge charges embed into cumulative removed-XOR charges, so Hall
  expansion for the induction-local neighborhoods already gives the same exact
  `1 + |U|·|F|·|G|` bound.
- `IrrRAFEnumeration.biUnion_entryRemovedXorCandidates`,
  `IrrRAFEnumeration.hasChargeExpansion_of_entryCutBounds`, and
  `IrrRAFEnumeration.states_card_le_one_add_of_entryCutBounds` — the union of
  first-entry neighborhoods depends only on the union of their removed
  vertices; consequently the vertex-cut inequalities imply Hall expansion and
  the complete `1 + |U|·|F|·|G|` memo-state bound.
- `IrrRAFEnumeration.entrySurvivorXorCandidates` and
  `IrrRAFEnumeration.hybridStates_card_le_of_entrySurvivorExpansion` — a
  genuine hybrid entry may use only a crossing root pair whose common trace
  survives the child; Hall expansion for these reconstructive charges bounds
  all hybrid-entry states by `|U|·|F|·|G|`, leaving factor nodes separate.
- `IrrRAFEnumeration.FactorTree.nodeCount_lt_two_mul_leafCount`,
  `IrrRAFEnumeration.factorForestNodeCount_le_two_mul_leafCount`, and
  `IrrRAFEnumeration.factorForestNodeCount_le_two_mul_ground` — a binary
  refinement of each recursive component tree has fewer than twice as many
  states as terminal components; if those leaves inject into `U`, the whole
  factor forest has at most `2·|U|` states.
- `IrrRAFEnumeration.disjointNonemptyComponents_card_le_ground` and
  `IrrRAFEnumeration.factorForestNodeCount_le_of_disjointComponents` —
  pairwise-disjoint nonempty terminal supports inject into the ground set, so
  the structural component hypotheses discharge the forest leaf budget.
- `IrrRAFEnumeration.sum_candidate_card_eq_sum_charge_degree` and
  `IrrRAFEnumeration.hasChargeExpansion_of_degree_codegree` — exact incidence
  double counting proves Hall whenever every state has at least `d > 0`
  candidates and every charge occurs in at most `d` states.  This applies
  componentwise to the survivor-neighborhood overlap graph.
- `IrrRAFEnumeration.hasChargeExpansion_of_orderedCandidateRanks` — an ordered
  state family satisfies Hall whenever each state's candidate neighborhood is
  at least as large as its initial segment.  Applied separately after sorting
  each overlap component, this is the exact `k`-th degree at least `k` route.
- `IrrRAFEnumeration.hasChargeExpansion_of_disjointParts` — Hall expansion on
  pairwise-disjoint state parts whose candidate unions are pairwise disjoint
  composes to Hall expansion on their union.
- `IrrRAFEnumeration.hasChargeExpansion_of_degreeSublevelBounds` — the
  induction-ready distributional form: if at every threshold `k` there are at
  most `k` states with at most `k` candidates, then survivor Hall follows.
- `IrrRAFEnumeration.hasChargeExpansion_of_coverDominance_and_pivotSublevels`
  — if every cover entry has degree at least the total hybrid-state count,
  every nontrivial degree sublevel contains only pivots, so pivot-only
  sublevel bounds imply survivor Hall.
- `IrrRAFEnumeration.survivorOutputFiber_card_le_entrySurvivorXorCandidates`,
  `IrrRAFEnumeration.survivorInputFiber_card_le_entrySurvivorXorCandidates`,
  `IrrRAFEnumeration.survivorFibers_add_card_le_entrySurvivorXorCandidates`,
  and `IrrRAFEnumeration.filteredVertexFibers_add_card_le_entrySurvivorXorCandidates`
  — at a singleton pivot, each polarity's surviving incident residual fiber
  injects into its own root survivor-charge block; the disjoint blocks make
  the two fiber cardinalities additive below the child's candidate degree.
- `IrrRAFEnumeration.filteredVertexFibers_add_card_le_of_proper` — strict
  non-universality of both filtered pivot fibers automatically produces the
  two omitted root witnesses, eliminating the existential side condition from
  the additive candidate-degree bound.
- `IrrRAFEnumeration.filteredOutputVertexFiber_card_le_of_inputProper` and
  `IrrRAFEnumeration.filteredInputVertexFiber_card_le_of_outputProper` — in
  either one-universal/one-proper pivot case, the entire incident fiber on the
  universal side injects into survivor charges using an omitted witness from
  the proper side.
- `IrrRAFEnumeration.two_le_entrySurvivorXorCandidates_of_pivotFibers` — the
  complete local proper/universal case split: nonempty pivot fibers, at least
  one proper side, and cardinality at least two on every universal side imply
  at least two survivor charges, enough to pay a binary pivot packet.
- `IrrRAFEnumeration.pivot_entrySurvivorXorCandidates_overlap_imp_eq` — two
  singleton-deletion pivot entries sharing a survivor charge delete the same
  vertex.
- `IrrRAFEnumeration.mem_rawAssignmentMinor_iff` — exact provenance
  characterization of a family restricted by projected and filtered vertices.
- `IrrRAFEnumeration.rawAssignmentMinor_compose` — consecutive restrictions
  along a shrinking-universe path equal one accumulated assignment minor.
- `IrrRAFEnumeration.twoLevelCharges_card` and
  `IrrRAFEnumeration.states_card_le_twoLevelBudget` — exact cardinality and
  injective-encoding adapter for the candidate `n²·|H|·|G|` hybrid DAG bound.
- `IrrRAFEnumeration.twoStageCode_card` — the root/first-choice/ordered-pair
  code space has exact cardinality `1+t+t²`.
- `IrrRAFEnumeration.selectorAlternating_twoStage_exceeds_linearCharge` and
  `selectorAlternating_twoStage_card` — strict Lean certificates that the
  7,168-choice product has 51,387,393 codes and exceeds the 50,331,649 linear
  root-charge budget.

- `IrrRAFEnumeration.switchProductFamily_card` and
  `IrrRAFEnumeration.switchProduct_blocker_card` — the parametric block-product
  clutter has exactly `2^b` edges and exact blocker size `4b`.
- `IrrRAFEnumeration.strongProductCover_card_ge` — the ordered strong cover of
  the selected product edge contains at least `b * 2^b` distinct regions.
- `IrrRAFEnumeration.hits_stagedProductFamily_iff` and
  `IrrRAFEnumeration.minimal_hits_stagedProductFamily_iff` — hitting and
  inclusion-minimality factor exactly over the disjoint stages.
- `IrrRAFEnumeration.stagedBlockerEquiv` and
  `IrrRAFEnumeration.stagedProduct_blocker_card` — the outer blocker is an
  independent stagewise product with exact cardinality `(4*b)^r`.
- `IrrRAFEnumeration.strongStagedCover_card_ge` — every outer stage supplies
  at least `b*2^b` distinct strong-cover regions.
- `IrrRAFEnumeration.blocker_subset_stagedCoverRegion_iff` — containment in a
  stage region fixes exactly its distinguished singleton blocker section.
- `IrrRAFEnumeration.filteredStagedBlockerEquiv` and
  `IrrRAFEnumeration.filterWithin_stagedCoverRegion_card` — a cover child has
  an independent residual blocker on the remaining stages of exact size
  `(4*b)^(r-1)`.
- `IrrRAFEnumeration.mem_minimalMembers_rawStagedProjection_iff` and
  `IrrRAFEnumeration.projectWithin_stagedCoverRegion_eq` — positive projection
  into a staged strong-cover region normalizes exactly to its distinguished
  singleton together with every untouched component family.
- `IrrRAFEnumeration.blocker_subset_accumulatedStagedRegion_iff`,
  `IrrRAFEnumeration.filteredAccumulatedStagedBlockerEquiv`, and
  `IrrRAFEnumeration.filterWithin_accumulatedStagedRegion_card` — after any
  processed-stage set `P`, all those sections are fixed while the residual
  blocker factors independently and has exact size `(4*b)^(r-|P|)`.
- `IrrRAFEnumeration.mem_rawAccumulatedStagedProjection_iff`,
  `IrrRAFEnumeration.mem_minimalMembers_rawAccumulated_iff`, and
  `IrrRAFEnumeration.projectWithin_accumulatedStagedRegion_eq` — accumulated
  positive projection normalizes to one fixed singleton per processed stage
  plus all component edges on precisely the unprocessed stages.
- `IrrRAFEnumeration.processedSingletonFamily_card`,
  `IrrRAFEnumeration.stagedProductFamilyOutside_card`, and
  `IrrRAFEnumeration.accumulatedPositiveNormalForm_card` — the positive state
  has exact size `|P| + (r-|P|)*2^b`.
- `IrrRAFEnumeration.fixedChoiceEquiv`,
  `IrrRAFEnumeration.switchProduct_switchFiber_card`, and
  `IrrRAFEnumeration.switchProduct_universalFiber_card` — component switch
  and universal incidence numerators are exactly `2^(b-1)` and `2^b`.
- `IrrRAFEnumeration.accumulatedPositive_unprocessedSwitchFiber_card`,
  `IrrRAFEnumeration.accumulatedPositive_unprocessedUniversalFiber_card`, and
  `IrrRAFEnumeration.accumulatedPositive_processedFiber_card` — those
  numerators lift unchanged to unprocessed stages, while every processed
  distinguished vertex occurs in exactly one positive edge.
- `IrrRAFEnumeration.mem_switchProductDual_and_vertex_iff` and
  `IrrRAFEnumeration.switchProductDual_vertexFiber_card` — every component
  vertex lies in exactly one of the `4b` component blockers.
- `IrrRAFEnumeration.filteredAccumulatedVertexFiberEquiv` and
  `IrrRAFEnumeration.filteredAccumulated_unprocessedFiber_card` — fixing an
  unprocessed vertex removes one free blocker coordinate, giving numerator
  `(4*b)^(r-|P|-1)`.
- `IrrRAFEnumeration.filteredAccumulated_processedFiber_card` — a processed
  distinguished vertex lies in the entire residual blocker family and has
  numerator `(4*b)^(r-|P|)`.
- `IrrRAFEnumeration.accumulatedPositive_unprocessedSwitch_frequency`,
  `IrrRAFEnumeration.accumulatedPositive_unprocessedUniversal_frequency`,
  `IrrRAFEnumeration.accumulatedPositive_processed_frequency`,
  `IrrRAFEnumeration.filteredAccumulated_unprocessed_frequency`, and
  `IrrRAFEnumeration.filteredAccumulated_processed_frequency` — exact
  real-valued frequency identities for every accumulated state.
- `IrrRAFEnumeration.accumulatedPositive_switch_frequency_ge`,
  `IrrRAFEnumeration.accumulatedPositive_universal_frequency_ge`,
  `IrrRAFEnumeration.filteredAccumulated_unprocessed_frequency_eq`, and
  `IrrRAFEnumeration.accumulatedPositive_processed_frequency_lt` — the
  certified frequency gap placing every unprocessed positive vertex above
  `1/(2*r)`, every unprocessed negative vertex at `1/(4*b)`, and processed
  positive vertices below `1/(4*b)` under the explicit state-size hypothesis.
- `IrrRAFEnumeration.accumulated_frequency_sandwich` — one uniform statement
  packages those inequalities for all stages, blocks, choices, and component
  vertices at an arbitrary threshold in `(1/(4*b), 1/(2*r)]`.
- `IrrRAFEnumeration.accumulated_hasNoFrequentPivot` — the sandwich rules out
  the hybrid algorithm's two-sided frequency pivot at every accumulated state.
- `IrrRAFEnumeration.isPositiveBranchCandidate_iff_unprocessedStage` — the
  positive strong-cover candidates are exactly lifted component edges on
  unprocessed stages, independent of tie-breaking among those candidates.

All listed declarations have warning-as-error strict receipts under Lean
4.30.0 with no `sorry`.
