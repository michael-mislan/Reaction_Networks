import proofs.HordijkSteelThreshold.TerminalCavityBarrier

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Maximality of the stabilized diagonal pruning core: a target assigned
initially but absent at the fixed point cannot have an open viable reaction
family against that fixed point.  Otherwise adjoining the target to both
pools would give a larger fixed pair contained in every pruning iterate. -/
theorem terminal_absent_familyClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A : Finset (Molecule n))
    (hfix : crossPoolIter foodLength Cat (A, A) (k + 1) =
      crossPoolIter foodLength Cat (A, A) k)
    {x : Molecule n} (hxA : x ∈ A)
    (hxAbsent : x ∉ (crossPoolIter foodLength Cat (A, A) k).1) :
    ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2)
      (crossPoolIter foodLength Cat (A, A) k).2
      (crossViableReactions
        (crossPoolIter foodLength Cat (A, A) k).1
        (crossPoolIter foodLength Cat (A, A) k).2 x) := by
  classical
  let S := crossPoolIter foodLength Cat (A, A) k
  have hSfix : crossPoolStep foodLength Cat S = S := by exact hfix
  have hdiag : S.1 = S.2 := crossPoolIter_diagonal Cat A
  intro hopen
  let Q : Finset (Molecule n) × Finset (Molecule n) :=
    (insert x S.1, insert x S.2)
  have hQfix : crossPoolStep foodLength Cat Q = Q := by
    apply Prod.ext
    · apply Finset.Subset.antisymm
      · exact crossPoolStep_left_subset Cat Q
      · intro z hz
        apply Finset.mem_filter.mpr
        refine ⟨hz, ?_⟩
        rcases Finset.mem_insert.mp hz with hzx | hzS
        · subst z
          right
          obtain ⟨r, hr, y, hy, hcat⟩ := hopen
          have hrData := (mem_crossViableReactions S.1 S.2 x r).mp hr
          refine ⟨r, hrData.1, ?_, ?_, y, Finset.mem_insert_of_mem hy, hcat⟩
          · rcases Finset.mem_union.mp hrData.2.1 with h | h
            · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
          · rcases Finset.mem_union.mp hrData.2.2 with h | h
            · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
        · have hzStep : z ∈ (crossPoolStep foodLength Cat S).1 := by
            rw [hSfix]
            exact hzS
          have hzSurvives := (Finset.mem_filter.mp hzStep).2
          exact crossLeftSurvives_mono (fun _ _ h => h)
            (Finset.subset_insert x S.1) (Finset.subset_insert x S.2)
            hzSurvives
    · apply Finset.Subset.antisymm
      · exact crossPoolStep_right_subset Cat Q
      · intro z hz
        apply Finset.mem_filter.mpr
        refine ⟨hz, ?_⟩
        rcases Finset.mem_insert.mp hz with hzx | hzS
        · subst z
          right
          obtain ⟨r, hr, y, hy, hcat⟩ := hopen
          have hrData := (mem_crossViableReactions S.1 S.2 x r).mp hr
          have hyLeft : y ∈ S.1 := by simpa [hdiag] using hy
          refine ⟨r, hrData.1, ?_, ?_, y,
            Finset.mem_insert_of_mem hyLeft, hcat⟩
          · rcases Finset.mem_union.mp hrData.2.1 with h | h
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
            · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
          · rcases Finset.mem_union.mp hrData.2.2 with h | h
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
            · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
        · have hzStep : z ∈ (crossPoolStep foodLength Cat S).2 := by
            rw [hSfix]
            exact hzS
          have hzSurvives := (Finset.mem_filter.mp hzStep).2
          exact crossLeftSurvives_mono (fun _ _ h => h)
            (Finset.subset_insert x S.2) (Finset.subset_insert x S.1)
            hzSurvives
  have hSinit := crossPoolIter_mono_time (foodLength := foodLength)
    Cat (A, A) (Nat.zero_le k)
  have hQleft : Q.1 ⊆ A := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzS
    · exact hxA
    · exact hSinit.1 hzS
  have hQright : Q.2 ⊆ A := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzS
    · exact hxA
    · exact hSinit.2 hzS
  have hlower := fixedPair_subset_crossPoolIter Cat Q (A, A)
    hQfix hQleft hQright k
  apply hxAbsent
  exact hlower.1 (by simp [Q])

/-- Every fixed batch absent from the stabilized diagonal core has all of its
terminal viable reaction families closed against that core. -/
theorem terminal_absent_familiesClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A U : Finset (Molecule n))
    (hfix : crossPoolIter foodLength Cat (A, A) (k + 1) =
      crossPoolIter foodLength Cat (A, A) k)
    (hUA : U ⊆ A)
    (hUAbsent : Disjoint U (crossPoolIter foodLength Cat (A, A) k).1) :
    catalystPoolFamiliesClosed (fun z => Cat z.1 z.2)
      (crossPoolIter foodLength Cat (A, A) k).2 U
      (crossViableReactions
        (crossPoolIter foodLength Cat (A, A) k).1
        (crossPoolIter foodLength Cat (A, A) k).2) := by
  intro x hxU
  exact terminal_absent_familyClosed Cat A hfix (hUA hxU)
    (Finset.disjoint_left.mp hUAbsent hxU)

/-- Closing targets already absent from a stabilized diagonal core does not
change that terminal core. -/
theorem crossPoolIter_close_terminalAbsent_eq
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A U : Finset (Molecule n))
    (hfix : crossPoolIter foodLength Cat (A, A) (k + 1) =
      crossPoolIter foodLength Cat (A, A) k)
    (hUAbsent : Disjoint U (crossPoolIter foodLength Cat (A, A) k).1) :
    crossPoolIter foodLength (closeTargetBlocks Cat U) (A, A) k =
      crossPoolIter foodLength Cat (A, A) k := by
  let S := crossPoolIter foodLength Cat (A, A) k
  have hdiag : S.1 = S.2 := crossPoolIter_diagonal Cat A
  change Disjoint U S.1 at hUAbsent
  have hUright : Disjoint U S.2 := by
    rw [← hdiag]
    exact hUAbsent
  have hSfix : crossPoolStep foodLength Cat S = S := by exact hfix
  have hSfixClosed : crossPoolStep foodLength (closeTargetBlocks Cat U) S = S := by
    rw [crossPoolStep_closeTargetBlocks_eq_of_disjoint
      Cat U S.1 S.2 hUAbsent hUright]
    exact hSfix
  have hSinit := crossPoolIter_mono_time (foodLength := foodLength)
    Cat (A, A) (Nat.zero_le k)
  have hlower := fixedPair_subset_crossPoolIter
    (closeTargetBlocks Cat U) S (A, A) hSfixClosed hSinit.1 hSinit.2 k
  have hupper := crossPoolIter_mono (foodLength := foodLength)
    (P := (A, A)) (Q := (A, A)) (closeTargetBlocks_le Cat U)
    (Finset.Subset.rfl) (Finset.Subset.rfl) k
  apply Prod.ext
  · exact Finset.Subset.antisymm hupper.1 hlower.1
  · exact Finset.Subset.antisymm hupper.2 hlower.2

/-- A fixed batch missing from the terminal diagonal core pays its complete
adaptive family-closure energy. -/
theorem measure_terminal_absent_batch_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (U A : Finset (Molecule n)) (hUA : U ⊆ A) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength Cat (A, A) k
      crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
        Disjoint U S.1 ∧ b ≤ S.2.card ∧
        ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (b * (d * U.card)) := by
  have hprob := measure_adaptive_preclosed_familiesClosed_le
    (foodLength := foodLength) (k := k) (b := b) (d := d)
    lambda ∅ U (A, A)
  refine (measure_mono ?_).trans hprob
  intro ω hω
  let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
  let S := crossPoolIter foodLength Cat (A, A) k
  have heq := crossPoolIter_close_terminalAbsent_eq Cat A U hω.1 hω.2.1
  have hclosed := terminal_absent_familiesClosed Cat A U hω.1 hUA hω.2.1
  have hgoal :
      b ≤ (crossPoolIter foodLength (closeTargetBlocks Cat U) (A, A) k).2.card ∧
      (∀ x ∈ U, d ≤ (crossViableReactions
        (crossPoolIter foodLength (closeTargetBlocks Cat U) (A, A) k).1
        (crossPoolIter foodLength (closeTargetBlocks Cat U) (A, A) k).2 x).card) ∧
      catalystPoolFamiliesClosed (fun z => Cat z.1 z.2)
        (crossPoolIter foodLength (closeTargetBlocks Cat U) (A, A) k).2 U
        (crossViableReactions
          (crossPoolIter foodLength (closeTargetBlocks Cat U) (A, A) k).1
          (crossPoolIter foodLength (closeTargetBlocks Cat U) (A, A) k).2) := by
    rw [heq]
    exact ⟨hω.2.2.1, hω.2.2.2, hclosed⟩
  simpa only [Finset.empty_union, Cat] using hgoal

/-- Exact binomial union over candidate terminal-hole batches. -/
theorem measure_exists_terminal_absent_batch_good_exact_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (W A : Finset (Molecule n)) (hWA : W ⊆ A) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
        let S := crossPoolIter foodLength Cat (A, A) k
        crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
          Disjoint U S.1 ∧ b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  classical
  let Candidates := W.powersetCard t
  let E : Finset (Molecule n) → Set (AmbientCoord n → Prop) := fun U =>
    {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength Cat (A, A) k
      crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
        Disjoint U S.1 ∧ b ≤ S.2.card ∧
        ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card}
  rw [show {ω : AmbientCoord n → Prop |
      ∃ U ∈ W.powersetCard t,
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
        let S := crossPoolIter foodLength Cat (A, A) k
        crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
          Disjoint U S.1 ∧ b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} =
      ⋃ U ∈ Candidates, E U by
    ext ω
    constructor
    · rintro ⟨U, hUC, hUE⟩
      exact Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr
        ⟨by simpa [Candidates] using hUC, hUE⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨U, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hUC, hUE⟩
      exact ⟨U, by simpa [Candidates] using hUC, hUE⟩]
  calc
    ambientPiMeasure n lambda (⋃ U ∈ Candidates, E U) ≤
        ∑ U ∈ Candidates, ambientPiMeasure n lambda (E U) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _U ∈ Candidates,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hdata := Finset.mem_powersetCard.mp hU
      have hUA : U ⊆ A := hdata.1.trans hWA
      simpa only [E, hdata.2] using
        (measure_terminal_absent_batch_good_le
          (foodLength := foodLength) (k := k) (b := b) (d := d)
          lambda U A hUA)
    _ = (Candidates.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by simp
    _ = (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      rw [show Candidates.card = Nat.choose W.card t by
        change (W.powersetCard t).card = Nat.choose W.card t
        rw [Finset.card_powersetCard]]

/-- Terminal-hole tail allowing `r` targets with too few viable reactions. -/
theorem measure_terminal_missing_large_of_few_lowViable_exact_le
    {n foodLength k b d r t : Nat} (lambda : ℝ)
    (W A : Finset (Molecule n)) (hWA : W ⊆ A) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y z => ω (y, z)
      let S := crossPoolIter foodLength Cat (A, A) k
      crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
        b ≤ S.2.card ∧
        r + t ≤ (W \ S.1).card ∧
        (W.filter fun x =>
          (crossViableReactions S.1 S.2 x).card < d).card ≤ r} ≤
      (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  have hprob := measure_exists_terminal_absent_batch_good_exact_le
    (foodLength := foodLength) (k := k) (b := b) (d := d) (t := t)
    lambda W A hWA
  refine (measure_mono ?_).trans hprob
  intro ω hω
  let Cat : Catalysis (Molecule n) (Reaction n) := fun y z => ω (y, z)
  let S := crossPoolIter foodLength Cat (A, A) k
  let D := W \ S.1
  let Bad := W.filter fun x => (crossViableReactions S.1 S.2 x).card < d
  have hcardD : r + t ≤ D.card := by simpa [D] using hω.2.2.1
  have hcardBad : Bad.card ≤ r := by simpa [Bad, S] using hω.2.2.2
  have hsplit : D.card ≤ (D \ Bad).card + Bad.card :=
    Finset.card_le_card_sdiff_add_card
  have ht : t ≤ (D \ Bad).card := by omega
  obtain ⟨U, hUD, hUcard⟩ := Finset.exists_subset_card_eq ht
  have hUW : U ∈ W.powersetCard t := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨hUD.trans (Finset.sdiff_subset.trans Finset.sdiff_subset), hUcard⟩
  refine ⟨U, hUW, hω.1, ?_, hω.2.1, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxU hxS
    have hxD : x ∈ D := Finset.sdiff_subset (hUD hxU)
    exact (Finset.mem_sdiff.mp hxD).2 hxS
  · intro x hxU
    apply Nat.le_of_not_gt
    intro hxlow
    have hxNotBad := (Finset.mem_sdiff.mp (hUD hxU)).2
    apply hxNotBad
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_powersetCard.mp hUW).1 hxU, by simpa [S] using hxlow⟩

/-- Exact terminal missing-layer Peierls tail.  The only exceptional targets
are those in the overlap-safe split-profile tail of the terminal core itself. -/
theorem measure_terminal_layer_missing_large_of_splitTail_le
    {n foodLength k b m delta r t : Nat} (lambda : ℝ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (A : Finset (Molecule n))
    (hLayer : layerMolecules (by omega) hmn ⊆ A) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y z => ω (y, z)
      let S := crossPoolIter foodLength Cat (A, A) k
      crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
        b ≤ S.2.card ∧
        r + t ≤ (layerMolecules (by omega) hmn \ S.1).card ∧
        (splitMissingTail
          (layerSplitViableTargets hm hmn S.1 S.2) delta).card ≤ r} ≤
      (Nat.choose (2 ^ m) t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * ((m - delta) * t)) := by
  have hprob := measure_terminal_missing_large_of_few_lowViable_exact_le
    (foodLength := foodLength) (k := k) (b := b) (d := m - delta)
    (r := r) (t := t) lambda (layerMolecules (by omega) hmn) A hLayer
  calc
    ambientPiMeasure n lambda {ω |
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y z => ω (y, z)
        let S := crossPoolIter foodLength Cat (A, A) k
        crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
          b ≤ S.2.card ∧
          r + t ≤ (layerMolecules (by omega) hmn \ S.1).card ∧
          (splitMissingTail
            (layerSplitViableTargets hm hmn S.1 S.2) delta).card ≤ r} ≤
      ambientPiMeasure n lambda {ω |
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y z => ω (y, z)
        let S := crossPoolIter foodLength Cat (A, A) k
        crossPoolIter foodLength Cat (A, A) (k + 1) = S ∧
          b ≤ S.2.card ∧
          r + t ≤ (layerMolecules (by omega) hmn \ S.1).card ∧
          ((layerMolecules (by omega) hmn).filter fun x =>
            (crossViableReactions S.1 S.2 x).card < m - delta).card ≤ r} := by
        apply measure_mono
        intro ω hω
        refine ⟨hω.1, hω.2.1, hω.2.2.1, ?_⟩
        exact (card_layer_lowViable_le_splitMissingTail hm hmn
          (crossPoolIter foodLength (fun y z => ω (y, z)) (A, A) k).1
          (crossPoolIter foodLength (fun y z => ω (y, z)) (A, A) k).2).trans
            hω.2.2.2
    _ ≤ (Nat.choose (2 ^ m) t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * ((m - delta) * t)) := by
      simpa only [card_layerMolecules] using hprob

end HordijkSteelThreshold
