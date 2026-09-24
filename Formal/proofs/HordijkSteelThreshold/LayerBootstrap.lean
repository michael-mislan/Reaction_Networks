import proofs.HordijkSteelThreshold.AdaptiveTargetFamilyTail

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Exact adaptive one-layer bootstrap.  The conclusion counts survivors in
the newly exposed length-`m` layer, while every state variable on the right is
computed in the cavity where that entire target layer was closed. -/
theorem measure_crossPoolIter_left_layer_survivors_barrier
    {n m foodLength k delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (lambda : ℝ) (P : Finset (Molecule n) × Finset (Molecule n))
    (hLayer : layerMolecules (by omega) hmn ⊆ P.1)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let T := layerMolecules (by omega) hmn
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      ((((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
        ((2 ^ m - (splitMissingTail
          (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta))) - c)} ≤
      ENNReal.ofReal ((((2 ^ m : Nat) : ℝ) / 4) / c ^ 2) := by
  classical
  let T := layerMolecules (by omega) hmn
  calc
    _ ≤ ambientPiMeasure n lambda {ω |
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
        let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
        (((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
          ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (S.2.card * (m - delta))) - c} := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      have hG := card_closedTargetGoodTargets_layer_ge
        (delta := delta) hm hmn S.1 S.2
      have hq0 : 0 ≤ (toNNReal (σ (catalysisP n lambda)) : ℝ) := by positivity
      have hq1 : (toNNReal (σ (catalysisP n lambda)) : ℝ) ≤ 1 := by
        exact_mod_cast (σ (catalysisP n lambda)).2.2
      have hp : 0 ≤ 1 -
          (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta)) := by
        have hpw := pow_le_one₀ (n := S.2.card * (m - delta)) hq0 hq1
        linarith
      have hmul :
          (((2 ^ m - (splitMissingTail
            (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta)))) ≤
            ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta))) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hG
        · exact hp
      exact hω.trans (sub_le_sub_right hmul c)
    _ ≤ _ := by
      simpa [T, card_layerMolecules] using
        (measure_target_inter_crossPoolIter_left_card_le_adaptive_bound
          (foodLength := foodLength) (k := k) (d := m - delta)
          lambda T P hLayer hc)

/-- Sharp one-layer bootstrap on the event that the closed-cavity right pool
has at least `b` catalysts.  Its error cost decays as
`2^m * q^(b * (m - delta))`, which is the summable high-window replacement
for the earlier non-decaying `2^m / (4*c^2)` bound. -/
theorem measure_crossPoolIter_left_layer_survivors_and_poolFloor_barrier_sharp
    {n m foodLength k delta b : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (lambda : ℝ) (P : Finset (Molecule n) × Finset (Molecule n))
    (hLayer : layerMolecules (by omega) hmn ⊆ P.1)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let T := layerMolecules (by omega) hmn
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      b ≤ S.2.card ∧
      ((((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
        ((2 ^ m - (splitMissingTail
          (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta))) - c)} ≤
      ENNReal.ofReal ((((2 ^ m : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (b * (m - delta))) / c ^ 2) := by
  classical
  let T := layerMolecules (by omega) hmn
  calc
    _ ≤ ambientPiMeasure n lambda {ω |
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
        let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
        b ≤ S.2.card ∧
        (((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
          ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (S.2.card * (m - delta))) - c} := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      have hG := card_closedTargetGoodTargets_layer_ge
        (delta := delta) hm hmn S.1 S.2
      have hq0 : 0 ≤ (toNNReal (σ (catalysisP n lambda)) : ℝ) := by
        positivity
      have hq1 : (toNNReal (σ (catalysisP n lambda)) : ℝ) ≤ 1 := by
        exact_mod_cast (σ (catalysisP n lambda)).2.2
      have hp : 0 ≤ 1 -
          (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta)) := by
        have hpw := pow_le_one₀ (n := S.2.card * (m - delta)) hq0 hq1
        linarith
      have hmul :
          (((2 ^ m - (splitMissingTail
            (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta)))) ≤
            ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta))) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hG
        · exact hp
      exact ⟨hω.1, hω.2.trans (sub_le_sub_right hmul c)⟩
    _ ≤ _ := by
      simpa [T, card_layerMolecules] using
        (measure_target_inter_crossPoolIter_left_card_and_poolFloor_le_sharp
          (foodLength := foodLength) (k := k) (d := m - delta) (b := b)
          lambda T P hLayer hc)

/-- Block-local form of the adaptive one-layer bootstrap.  Unlike the older
whole-pool word-block barrier, the random count in the conclusion is the
literal intersection of the selected word block with the ordinary pruning
iterate.  This is the concentration interface needed to propagate
prefix/suffix cylinder discrepancies through a fresh product layer. -/
theorem measure_crossPoolIter_left_layerWordTargets_survivors_barrier
    {n m foodLength k delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (lambda : ℝ) (W : Finset (Word m))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hWP : layerWordTargets (by omega) hmn W ⊆ P.1)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let T := layerWordTargets (by omega) hmn W
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      ((((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
        ((W.card - (splitMissingTail
          (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta))) - c)} ≤
      ENNReal.ofReal (((W.card : ℝ) / 4) / c ^ 2) := by
  classical
  let T := layerWordTargets (by omega) hmn W
  calc
    _ ≤ ambientPiMeasure n lambda {ω |
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
        let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
        (((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
          ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (S.2.card * (m - delta))) - c} := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      have hG := card_closedTargetGoodTargets_layerWordTargets_ge
        (delta := delta) hm hmn S.1 S.2 W
      have hq0 : 0 ≤ (toNNReal (σ (catalysisP n lambda)) : ℝ) := by positivity
      have hq1 : (toNNReal (σ (catalysisP n lambda)) : ℝ) ≤ 1 := by
        exact_mod_cast (σ (catalysisP n lambda)).2.2
      have hp : 0 ≤ 1 -
          (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta)) := by
        have hpw := pow_le_one₀ (n := S.2.card * (m - delta)) hq0 hq1
        linarith
      have hmul :
          ((W.card - (splitMissingTail
            (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta))) ≤
            ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta))) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hG
        · exact hp
      exact hω.trans (sub_le_sub_right hmul c)
    _ ≤ _ := by
      simpa [T] using
        (measure_target_inter_crossPoolIter_left_card_le_adaptive_bound
          (foodLength := foodLength) (k := k) (d := m - delta)
          lambda T P hWP hc)

end HordijkSteelThreshold
