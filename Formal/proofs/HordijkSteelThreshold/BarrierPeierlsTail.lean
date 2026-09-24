import proofs.HordijkSteelThreshold.TwoPoolPruning
import proofs.HordijkSteelThreshold.TargetBlockCavityIndependence
import Mathlib.Data.Nat.Choose.Bounds

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Targets from `U` deleted in one fixed cross-pool pruning step. -/
noncomputable def crossPoolStepLeftDeleted {n : Nat} (foodLength : Nat)
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A B U : Finset (Molecule n)) : Finset (Molecule n) := by
  classical
  exact U.filter fun x => x ∉ (crossPoolStep foodLength Cat (A, B)).1

/-- Peierls tail for a fixed pruning state.  Unlike the variance bound, this
charges the simultaneous deletion of `t` targets by its full closed-coordinate
energy, and loses only the number of candidate `t`-subsets. -/
theorem measure_fixed_crossPoolStep_left_deleted_card_ge_le
    {n foodLength d t : Nat} (lambda : ℝ)
    (A B U : Finset (Molecule n)) (hUA : U ⊆ A)
    (hlen : ∀ x ∈ U, foodLength < molLength x)
    (hcard : ∀ x ∈ U, d ≤ (crossViableReactions A B x).card) :
    ambientPiMeasure n lambda {ω |
        t ≤ (crossPoolStepLeftDeleted foodLength
          (fun y r => ω (y, r)) A B U).card} ≤
      (2 ^ U.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (B.card * (d * t)) := by
  classical
  let Candidates := U.powersetCard t
  let E : Finset (Molecule n) → Set (AmbientCoord n → Prop) := fun T =>
    {ω | ∀ x ∈ T,
      x ∉ (crossPoolStep foodLength (fun y r => ω (y, r)) (A, B)).1}
  have hbad : {ω |
        t ≤ (crossPoolStepLeftDeleted foodLength
          (fun y r => ω (y, r)) A B U).card} ⊆
      ⋃ T ∈ Candidates, E T := by
    intro ω hω
    obtain ⟨T, hTsub, hTcard⟩ :=
      Finset.exists_subset_card_eq hω
    have hTU : T ⊆ U := fun x hx =>
      (Finset.mem_filter.mp (hTsub hx)).1
    have hTI : T ∈ Candidates := by
      exact Finset.mem_powersetCard.mpr ⟨hTU, hTcard⟩
    simp only [Set.mem_iUnion]
    refine ⟨T, ⟨hTI, ?_⟩⟩
    intro x hx
    exact (Finset.mem_filter.mp (hTsub hx)).2
  calc
    ambientPiMeasure n lambda {ω |
          t ≤ (crossPoolStepLeftDeleted foodLength
            (fun y r => ω (y, r)) A B U).card} ≤
        ambientPiMeasure n lambda (⋃ T ∈ Candidates, E T) := measure_mono hbad
    _ ≤ ∑ T ∈ Candidates, ambientPiMeasure n lambda (E T) :=
      measure_biUnion_finset_le Candidates E
    _ ≤ ∑ _T ∈ Candidates,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (B.card * (d * t)) := by
      exact Finset.sum_le_sum fun T hTI => by
        have hTU := (Finset.mem_powersetCard.mp hTI).1
        have hTcard := (Finset.mem_powersetCard.mp hTI).2
        simpa [E, hTcard] using
          (measure_fixed_crossPoolStep_left_barrier_le
            (foodLength := foodLength) (d := d) lambda A B T
            (hTU.trans hUA) (fun x hx => hlen x (hTU hx))
            (fun x hx => hcard x (hTU hx)))
    _ = (Candidates.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (B.card * (d * t)) := by simp
    _ ≤ (2 ^ U.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (B.card * (d * t)) := by
      gcongr
      exact_mod_cast (show Candidates.card ≤ 2 ^ U.card by
        change (U.powersetCard t).card ≤ 2 ^ U.card
        rw [Finset.card_powersetCard]
        exact Nat.choose_le_two_pow U.card t)

/-- The good targets of a fixed cavity state for the Peierls reveal. -/
noncomputable def peierlsGoodTargets {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n)) :
    Finset (Molecule n) := by
  classical
  exact T.filter fun x =>
    d ≤ (crossViableReactions (S.1 ∪ T) S.2 x).card

@[simp] theorem mem_peierlsGoodTargets {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n)) (x : Molecule n) :
    x ∈ peierlsGoodTargets (d := d) T S ↔
      x ∈ T ∧ d ≤ (crossViableReactions (S.1 ∪ T) S.2 x).card := by
  classical
  simp [peierlsGoodTargets]

/-- Reconstructing a held-out target block does not change one-step deletion
of a target in that block. -/
theorem mem_crossPoolStep_left_fromTargetRestriction_iff
    {n foodLength : Nat} (T A B : Finset (Molecule n))
    (v : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) T → Prop)
    (ω : AmbientCoord n → Prop) {x : Molecule n} (hxA : x ∈ A)
    (hxT : x ∈ T)
    (hv : ∀ z : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) T, v z ↔ ω z) :
    x ∈ (crossPoolStep foodLength
        (catalysisFromTargetRestriction T v) (A, B)).1 ↔
      x ∈ (crossPoolStep foodLength
        (fun y r => ω (y, r)) (A, B)).1 := by
  classical
  have hopen : catalystPoolFamilyOpen
        (fun z => catalysisFromTargetRestriction T v z.1 z.2) B
          (crossViableReactions A B x) ↔
      catalystPoolFamilyOpen ω B (crossViableReactions A B x) := by
      constructor
      · rintro ⟨r, hr, y, hy, hcat⟩
        refine ⟨r, hr, y, hy, ?_⟩
        have hprod := (mem_crossViableReactions A B x r).mp hr |>.1
        have htarget : reactionProduct r ∈ T := hprod.symm ▸ hxT
        have hcat' : v ⟨(y, r), by
            simp [catalystPoolTargetBlock, htarget]⟩ := by
          simpa [catalysisFromTargetRestriction, htarget] using hcat
        exact (hv _).mp hcat'
      · rintro ⟨r, hr, y, hy, hcat⟩
        refine ⟨r, hr, y, hy, ?_⟩
        have hprod := (mem_crossViableReactions A B x r).mp hr |>.1
        have htarget : reactionProduct r ∈ T := hprod.symm ▸ hxT
        have hvcat : v ⟨(y, r), by
            simp [catalystPoolTargetBlock, htarget]⟩ := (hv _).mpr hcat
        simpa [catalysisFromTargetRestriction, htarget] using hvcat
  have hnot :
      (x ∉ (crossPoolStep foodLength
          (catalysisFromTargetRestriction T v) (A, B)).1) ↔
        x ∉ (crossPoolStep foodLength
          (fun y r => ω (y, r)) (A, B)).1 := by
    rw [not_mem_crossPoolStep_left_iff
      (catalysisFromTargetRestriction T v) A B hxA,
      not_mem_crossPoolStep_left_iff (fun y r => ω (y, r)) A B hxA,
      hopen]
  simpa only [not_not] using not_congr hnot

/-- Exponential Peierls tail after the pruning state is selected by the
independent closed-target cavity.  No history-count factor is paid. -/
theorem measure_adaptive_closedTarget_step_deleted_card_ge_le
    {n foodLength k d t b : Nat} (lambda : ℝ)
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hlen : ∀ x ∈ T, foodLength < molLength x) :
    ambientPiMeasure n lambda {ω |
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) T) P k
      b ≤ S.2.card ∧
        t ≤ (crossPoolStepLeftDeleted foodLength
          (catalysisFromTargetRestriction T
            (fun z : catalystPoolTargetBlock
              (Finset.univ : Finset (Molecule n)) T => ω z))
          (S.1 ∪ T) S.2 (peierlsGoodTargets (d := d) T S)).card} ≤
      (2 ^ T.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  classical
  let H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) T → Prop) → Prop :=
    fun S v => b ≤ S.2.card ∧
      t ≤ (crossPoolStepLeftDeleted foodLength
        (catalysisFromTargetRestriction T v) (S.1 ∪ T) S.2
          (peierlsGoodTargets (d := d) T S)).card
  have hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤
        (2 ^ T.card : ENNReal) *
          (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
            (b * (d * t)) := by
    intro S
    by_cases hbS : b ≤ S.2.card
    · let U := peierlsGoodTargets (d := d) T S
      let A := S.1 ∪ T
      have hUA : U ⊆ A := by
        intro x hx
        exact Finset.mem_union_right _
          ((mem_peierlsGoodTargets T S x).mp hx |>.1)
      have hlenU : ∀ x ∈ U, foodLength < molLength x := by
        intro x hx
        exact hlen x ((mem_peierlsGoodTargets T S x).mp hx |>.1)
      have hcardU : ∀ x ∈ U,
          d ≤ (crossViableReactions A S.2 x).card := by
        intro x hx
        exact (mem_peierlsGoodTargets T S x).mp hx |>.2
      have hdeleted (ω : AmbientCoord n → Prop) :
          crossPoolStepLeftDeleted foodLength
            (catalysisFromTargetRestriction T (fun z => ω z))
            A S.2 U =
          crossPoolStepLeftDeleted foodLength
            (fun y r => ω (y, r)) A S.2 U := by
        ext x
        simp only [crossPoolStepLeftDeleted, Finset.mem_filter]
        constructor
        · rintro ⟨hxU, hxnot⟩
          refine ⟨hxU, ?_⟩
          intro hxmem
          exact hxnot ((mem_crossPoolStep_left_fromTargetRestriction_iff
            T A S.2 (fun z => ω z) ω (hUA hxU)
            ((mem_peierlsGoodTargets T S x).mp hxU |>.1)
            (fun _ => Iff.rfl)).mpr hxmem)
        · rintro ⟨hxU, hxnot⟩
          refine ⟨hxU, ?_⟩
          intro hxmem
          exact hxnot ((mem_crossPoolStep_left_fromTargetRestriction_iff
            T A S.2 (fun z => ω z) ω (hUA hxU)
            ((mem_peierlsGoodTargets T S x).mp hxU |>.1)
            (fun _ => Iff.rfl)).mp hxmem)
      have hevent : {ω : AmbientCoord n → Prop | H S (fun z => ω z)} =
        {ω : AmbientCoord n → Prop |
          t ≤ (crossPoolStepLeftDeleted foodLength
            (fun y r => ω (y, r)) A S.2 U).card} := by
        ext ω
        simp only [Set.mem_setOf_eq, H, hbS, true_and]
        rw [hdeleted ω]
      rw [hevent]
      calc
        _ ≤ (2 ^ U.card : ENNReal) *
            (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
              (S.2.card * (d * t)) :=
          measure_fixed_crossPoolStep_left_deleted_card_ge_le
            lambda A S.2 U hUA hlenU hcardU
        _ ≤ (2 ^ T.card : ENNReal) *
            (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
              (b * (d * t)) := by
          apply mul_le_mul
          · exact_mod_cast (Nat.pow_le_pow_right (by omega)
              (Finset.card_le_card
                (fun x hx => (mem_peierlsGoodTargets T S x).mp hx |>.1)))
          · apply pow_le_pow_right_of_le_one'
            · exact_mod_cast (σ (catalysisP n lambda)).2.2
            · exact Nat.mul_le_mul_right (d * t) hbS
          · positivity
          · positivity
    · simp [H, hbS]
  exact measure_adaptive_closedTargetIter_le lambda T P H
    (fun _ => MeasurableSet.of_discrete) hsec

end HordijkSteelThreshold
