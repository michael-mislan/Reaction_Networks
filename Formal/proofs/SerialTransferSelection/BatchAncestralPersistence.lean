import proofs.SerialTransferSelection.BatchAncestralBinding
import proofs.ResourceLimitedCompetition.AncestralPersistence
import proofs.FiniteCopy.UniformizedBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
open scoped NNReal

noncomputable local instance AncestralPersistenceDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem phase_stopped_ancestral_monotone (N W0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (tag : Bool) (x : StoppedPopulation D) (e : PopulationEvent D) :
    ancestralMembrane tag (physicalState N x).live ≤
      ancestralMembrane tag (physicalState N (phaseStoppedNext N W0 zL zH D x e)).live := by
  classical
  cases x with
  | inr t => exact le_rfl
  | inl s =>
    by_cases he : e.1=s
    · subst s
      rw [phase_physical_next_chosen]
      change ancestralMembrane tag e.1.val.live ≤ ancestralMembrane tag (eventOutcome N e).live
      have h := event_ancestral_membrane N tag D e.1 e.2
      rw [h]
      exact Nat.le_add_right _ _
    · simp only [phaseStoppedNext,he,if_false]
      exact le_rfl

theorem phase_ancestry_below_generator (γ : ℝ) (hγ : 0 ≤ γ) (Ω N W0 K : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (tag : Bool) (x : StoppedPopulation D) :
    (phaseStoppedModel γ hγ Ω N W0 zL zH D).generator
      (FiniteKernel.eventIndicator (ancestryBelowSet N K tag D)) x ≤ 0 := by
  classical
  unfold FiniteJumpModel.generator
  apply Finset.sum_nonpos
  intro e _
  apply mul_nonpos_of_nonneg_of_nonpos ((phaseStoppedModel γ hγ Ω N W0 zL zH D).nonneg x e)
  apply sub_nonpos.mpr
  have hm := phase_stopped_ancestral_monotone N W0 zL zH D tag x e
  simp only [FiniteKernel.eventIndicator,ancestryBelowSet,Set.mem_setOf_eq,phaseStoppedModel]
  split_ifs <;> norm_num
  omega

theorem phase_ancestry_below_probability (γ : ℝ) (hγ : 0 ≤ γ) (Ω N W0 K : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (tag : Bool)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (phaseStoppedModel γ hγ Ω N W0 zL zH D).total x ≤ q)
    (x : StoppedPopulation D) (hx : K ≤ ancestralMembrane tag (physicalState N x).live) :
    ((phaseStoppedModel γ hγ Ω N W0 zL zH D).uniformize q hq hbound).poissonized (q*t)
      (FiniteKernel.eventIndicator (ancestryBelowSet N K tag D)) x ≤ 0 := by
  classical
  have h := (phaseStoppedModel γ hγ Ω N W0 zL zH D).uniformized_event_bound q t hq hbound
    (ancestryBelowSet N K tag D) (FiniteKernel.eventIndicator (ancestryBelowSet N K tag D)) 1 0
    (by intro y; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (by intro y hy; simp only [FiniteKernel.eventIndicator,if_pos hy,le_refl])
    (phase_ancestry_below_generator γ hγ Ω N W0 K zL zH D tag) x
  simpa [FiniteKernel.eventIndicator,ancestryBelowSet,not_lt.mpr hx] using h

end SerialTransferSelection
