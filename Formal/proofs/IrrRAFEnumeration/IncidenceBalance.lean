import proofs.IrrRAFEnumeration.FactorForest

namespace IrrRAFEnumeration

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
/-- Double-count incidences between a finite state family and its candidate
charges. -/
theorem sum_candidate_card_eq_sum_charge_degree
    (states : Finset β) (candidates : β → Finset α) :
    (∑ state ∈ states, (candidates state).card) =
      ∑ charge ∈ states.biUnion candidates,
        (states.filter fun state => charge ∈ candidates state).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state hstate
  rw [← Finset.sum_filter]
  rw [← Finset.card_eq_sum_ones]
  congr 1
  ext charge
  simp only [Finset.mem_filter]
  constructor
  · intro hcharge
    exact ⟨Finset.mem_biUnion.mpr ⟨state, hstate, hcharge⟩, hcharge⟩
  · exact fun hcharge => hcharge.2

omit [DecidableEq β] in
/-- A uniform lower bound on state degrees and upper bound on charge
codegrees implies Hall expansion.  Applying this theorem to each connected
component of the candidate-overlap graph is exactly the live E4BU
incidence-balance route. -/
theorem hasChargeExpansion_of_degree_codegree
    (states : Finset β) (candidates : β → Finset (RootCharge α))
    (degree : ℕ) (hDegree : 0 < degree)
    (hState : ∀ state ∈ states, degree ≤ (candidates state).card)
    (hCharge : ∀ charge ∈ states.biUnion candidates,
      (states.filter fun state => charge ∈ candidates state).card ≤ degree) :
    HasChargeExpansion states candidates := by
  intro sub hsub
  have hLeft : degree * sub.card ≤
      ∑ state ∈ sub, (candidates state).card := by
    calc
      degree * sub.card = ∑ state ∈ sub, degree := by simp [Nat.mul_comm]
      _ ≤ ∑ state ∈ sub, (candidates state).card := by
        apply Finset.sum_le_sum
        intro state hstate
        exact hState state (hsub hstate)
  have hRight :
      (∑ charge ∈ sub.biUnion candidates,
        (sub.filter fun state => charge ∈ candidates state).card) ≤
        degree * (sub.biUnion candidates).card := by
    calc
      (∑ charge ∈ sub.biUnion candidates,
          (sub.filter fun state => charge ∈ candidates state).card) ≤
          ∑ _charge ∈ sub.biUnion candidates, degree := by
        apply Finset.sum_le_sum
        intro charge hcharge
        apply Nat.le_trans (Finset.card_le_card ?_) (hCharge charge ?_)
        · intro state hstate
          obtain ⟨hstateSub, hmem⟩ := Finset.mem_filter.mp hstate
          exact Finset.mem_filter.mpr ⟨hsub hstateSub, hmem⟩
        · obtain ⟨state, hstate, hmem⟩ := Finset.mem_biUnion.mp hcharge
          exact Finset.mem_biUnion.mpr ⟨state, hsub hstate, hmem⟩
      _ = degree * (sub.biUnion candidates).card := by simp [Nat.mul_comm]
  have hMul : degree * sub.card ≤
      degree * (sub.biUnion candidates).card := by
    exact hLeft.trans ((sum_candidate_card_eq_sum_charge_degree
      sub candidates).le.trans hRight)
  exact Nat.le_of_mul_le_mul_left hMul hDegree

omit [DecidableEq β] in
/-- A nonuniform alternative to incidence balance.  If the states are ordered
so that every state's candidate neighborhood pays for its entire initial
segment, then the candidate relation satisfies Hall.  Sorting each connected
overlap component by candidate cardinality turns the live numerical
`k`-th-neighborhood-has-at-least-`k` condition into exactly this premise. -/
theorem hasChargeExpansion_of_orderedCandidateRanks
    [LinearOrder β] (states : Finset β)
    (candidates : β → Finset (RootCharge α))
    (hRank : ∀ state ∈ states,
      (states.filter fun prior => prior ≤ state).card ≤
        (candidates state).card) :
    HasChargeExpansion states candidates := by
  intro sub hsub
  by_cases hsubEmpty : sub.Nonempty
  · let last := sub.max' hsubEmpty
    have hlastSub : last ∈ sub := Finset.max'_mem sub hsubEmpty
    have hlastState : last ∈ states := hsub hlastSub
    calc
      sub.card ≤ (states.filter fun prior => prior ≤ last).card := by
        apply Finset.card_le_card
        intro state hstate
        exact Finset.mem_filter.mpr
          ⟨hsub hstate, Finset.le_max' sub state hstate⟩
      _ ≤ (candidates last).card := hRank last hlastState
      _ ≤ (sub.biUnion candidates).card := by
        apply Finset.card_le_card
        intro charge hcharge
        exact Finset.mem_biUnion.mpr ⟨last, hlastSub, hcharge⟩
  · simp only [Finset.not_nonempty_iff_eq_empty] at hsubEmpty
    simp [hsubEmpty]

/-- Hall expansion composes across a partition whose charge unions are
pairwise disjoint.  Candidate-overlap connected components have exactly this
property, so `hasChargeExpansion_of_orderedCandidateRanks` may be applied
componentwise without paying ranks from unrelated components. -/
theorem hasChargeExpansion_of_disjointParts
    (states : Finset β) (candidates : β → Finset (RootCharge α))
    (parts : Finset (Finset β))
    (hCover : parts.biUnion id = states)
    (hDisjoint : (parts : Set (Finset β)).PairwiseDisjoint id)
    (hCandidateDisjoint :
      (parts : Set (Finset β)).PairwiseDisjoint
        (fun part => part.biUnion candidates))
    (hPart : ∀ part ∈ parts, HasChargeExpansion part candidates) :
    HasChargeExpansion states candidates := by
  classical
  intro sub hsub
  let piece : Finset β → Finset β := fun part => sub ∩ part
  have hPieceDisjoint :
      (parts : Set (Finset β)).PairwiseDisjoint piece := by
    intro left hleft right hright hne
    exact (hDisjoint hleft hright hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hPieceCandidates : ∀ part ∈ parts,
      (piece part).biUnion candidates ⊆ part.biUnion candidates := by
    intro part hpart charge hcharge
    obtain ⟨state, hstate, hmem⟩ := Finset.mem_biUnion.mp hcharge
    exact Finset.mem_biUnion.mpr
      ⟨state, Finset.inter_subset_right hstate, hmem⟩
  have hPieceCandidateDisjoint :
      (parts : Set (Finset β)).PairwiseDisjoint
        (fun part => (piece part).biUnion candidates) := by
    intro left hleft right hright hne
    exact (hCandidateDisjoint hleft hright hne).mono
      (hPieceCandidates left hleft) (hPieceCandidates right hright)
  have hSubUnion : parts.biUnion piece = sub := by
    ext state
    constructor
    · intro hstate
      obtain ⟨part, _hpart, hstatePiece⟩ := Finset.mem_biUnion.mp hstate
      exact (Finset.mem_inter.mp hstatePiece).1
    · intro hstate
      have hstateStates : state ∈ states := hsub hstate
      rw [← hCover] at hstateStates
      obtain ⟨part, hpart, hstatePart⟩ :=
        Finset.mem_biUnion.mp hstateStates
      exact Finset.mem_biUnion.mpr
        ⟨part, hpart, Finset.mem_inter.mpr ⟨hstate, hstatePart⟩⟩
  have hCandidateUnion :
      parts.biUnion (fun part => (piece part).biUnion candidates) =
        sub.biUnion candidates := by
    ext charge
    constructor
    · intro hcharge
      obtain ⟨part, _hpart, hchargePart⟩ :=
        Finset.mem_biUnion.mp hcharge
      obtain ⟨state, hstatePiece, hmem⟩ :=
        Finset.mem_biUnion.mp hchargePart
      exact Finset.mem_biUnion.mpr
        ⟨state, (Finset.mem_inter.mp hstatePiece).1, hmem⟩
    · intro hcharge
      obtain ⟨state, hstateSub, hmem⟩ := Finset.mem_biUnion.mp hcharge
      have hstateStates : state ∈ states := hsub hstateSub
      rw [← hCover] at hstateStates
      obtain ⟨part, hpart, hstatePart⟩ :=
        Finset.mem_biUnion.mp hstateStates
      exact Finset.mem_biUnion.mpr ⟨part, hpart,
        Finset.mem_biUnion.mpr
          ⟨state, Finset.mem_inter.mpr ⟨hstateSub, hstatePart⟩, hmem⟩⟩
  calc
    sub.card = (parts.biUnion piece).card := congrArg Finset.card hSubUnion.symm
    _ = ∑ part ∈ parts, (piece part).card :=
      Finset.card_biUnion hPieceDisjoint
    _ ≤ ∑ part ∈ parts, ((piece part).biUnion candidates).card := by
      apply Finset.sum_le_sum
      intro part hpart
      exact hPart part hpart (piece part) Finset.inter_subset_right
    _ = (parts.biUnion
        (fun part => (piece part).biUnion candidates)).card :=
      (Finset.card_biUnion hPieceCandidateDisjoint).symm
    _ = (sub.biUnion candidates).card := congrArg Finset.card hCandidateUnion

omit [DecidableEq β] in
/-- Distributional form of the ordered-rank route.  If at every threshold
`k` there are at most `k` states with at most `k` candidates, then Hall holds.
This is the induction-ready statement for the hybrid recursion: it mentions
only candidate degrees, not a chosen ordering or matching. -/
theorem hasChargeExpansion_of_degreeSublevelBounds
    (states : Finset β) (candidates : β → Finset (RootCharge α))
    (hSublevel : ∀ k,
      (states.filter fun state => (candidates state).card ≤ k).card ≤ k) :
    HasChargeExpansion states candidates := by
  intro sub hsub
  by_cases hsubNonempty : sub.Nonempty
  · let degrees := sub.image fun state => (candidates state).card
    have hdegreesNonempty : degrees.Nonempty := by
      obtain ⟨state, hstate⟩ := hsubNonempty
      exact ⟨(candidates state).card,
        Finset.mem_image.mpr ⟨state, hstate, rfl⟩⟩
    let k := degrees.max' hdegreesNonempty
    have hkDegrees : k ∈ degrees := Finset.max'_mem degrees hdegreesNonempty
    obtain ⟨witness, hwitnessSub, hwitnessDegree⟩ :=
      Finset.mem_image.mp hkDegrees
    have hSubLow : sub ⊆
        states.filter fun state => (candidates state).card ≤ k := by
      intro state hstate
      apply Finset.mem_filter.mpr
      refine ⟨hsub hstate, ?_⟩
      apply Finset.le_max' degrees (candidates state).card
      exact Finset.mem_image.mpr ⟨state, hstate, rfl⟩
    calc
      sub.card ≤
          (states.filter fun state => (candidates state).card ≤ k).card :=
        Finset.card_le_card hSubLow
      _ ≤ k := hSublevel k
      _ = (candidates witness).card := hwitnessDegree.symm
      _ ≤ (sub.biUnion candidates).card := by
        apply Finset.card_le_card
        intro charge hcharge
        exact Finset.mem_biUnion.mpr ⟨witness, hwitnessSub, hcharge⟩
  · simp only [Finset.not_nonempty_iff_eq_empty] at hsubNonempty
    simp [hsubNonempty]

omit [DecidableEq β] in
/-- Cover-dominance reduction for the hybrid recursion.  If every non-pivot
entry has at least as many candidates as there are states altogether, then
non-pivot entries cannot occur in any nontrivial degree sublevel.  Consequently
it suffices to prove the sublevel inequalities only for pivot entries. -/
theorem hasChargeExpansion_of_coverDominance_and_pivotSublevels
    (states pivots : Finset β)
    (candidates : β → Finset (RootCharge α))
    (hCover : ∀ state ∈ states, state ∉ pivots →
      states.card ≤ (candidates state).card)
    (hPivotSublevel : ∀ k,
      (pivots.filter fun state => (candidates state).card ≤ k).card ≤ k) :
    HasChargeExpansion states candidates := by
  apply hasChargeExpansion_of_degreeSublevelBounds states candidates
  intro k
  by_cases hk : states.card ≤ k
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hk
  · apply (Finset.card_le_card ?_).trans (hPivotSublevel k)
    intro state hstate
    obtain ⟨hstateStates, hdegree⟩ := Finset.mem_filter.mp hstate
    apply Finset.mem_filter.mpr
    refine ⟨?_, hdegree⟩
    by_contra hstatePivot
    exact hk ((hCover state hstateStates hstatePivot).trans hdegree)

end IrrRAFEnumeration
