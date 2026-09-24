import proofs.ResourceLimitedCompetition.AncestralGenerator
import proofs.FiniteCopy.UniformizedBounds

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy
open scoped NNReal

noncomputable local instance AncestralPersistenceDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem stopped_ancestral_monotone (N M : ℕ) (zL zH : ℝ) (D : Finset PopulationState)
    (tag : Bool) (x : StoppedPopulation D) (e : PopulationEvent D) :
    ancestralMembrane tag (physicalState N x).live ≤
      ancestralMembrane tag (physicalState N (stoppedNext N M zL zH D x e)).live := by
  classical
  cases x with
  | inr t => exact le_rfl
  | inl s =>
    by_cases he : e.1=s
    · subst s
      rw [physical_next_chosen]
      change ancestralMembrane tag e.1.val.live ≤ ancestralMembrane tag (eventOutcome N e).live
      have h := event_ancestral_membrane N tag D e.1 e.2
      rw [h]
      exact Nat.le_add_right _ _
    · simp only [stoppedNext,he,if_false]
      exact le_rfl

def ancestryBelowSet (N K : ℕ) (tag : Bool) (D : Finset PopulationState) : Set (StoppedPopulation D) :=
  {x | ancestralMembrane tag (physicalState N x).live < K}

theorem ancestry_below_generator (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M K : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (tag : Bool) (x : StoppedPopulation D) :
    (stoppedPopulationModel γ hγ Ω N M zL zH D).generator
      (FiniteKernel.eventIndicator (ancestryBelowSet N K tag D)) x ≤ 0 := by
  classical
  unfold FiniteJumpModel.generator
  apply Finset.sum_nonpos
  intro e _
  apply mul_nonpos_of_nonneg_of_nonpos ((stoppedPopulationModel γ hγ Ω N M zL zH D).nonneg x e)
  apply sub_nonpos.mpr
  have hm := stopped_ancestral_monotone N M zL zH D tag x e
  simp only [FiniteKernel.eventIndicator,ancestryBelowSet,Set.mem_setOf_eq,stoppedPopulationModel]
  split_ifs <;> norm_num
  omega

theorem ancestry_below_probability (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M K : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (tag : Bool)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ Ω N M zL zH D).total x ≤ q)
    (x : StoppedPopulation D) (hx : K ≤ ancestralMembrane tag (physicalState N x).live) :
    ((stoppedPopulationModel γ hγ Ω N M zL zH D).uniformize q hq hbound).poissonized (q*t)
      (FiniteKernel.eventIndicator (ancestryBelowSet N K tag D)) x ≤ 0 := by
  classical
  have h := (stoppedPopulationModel γ hγ Ω N M zL zH D).uniformized_event_bound q t hq hbound
    (ancestryBelowSet N K tag D) (FiniteKernel.eventIndicator (ancestryBelowSet N K tag D)) 1 0
    (by intro y; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (by intro y hy; simp only [FiniteKernel.eventIndicator,if_pos hy,le_refl])
    (ancestry_below_generator γ hγ Ω N M K zL zH D tag) x
  simpa [FiniteKernel.eventIndicator,ancestryBelowSet,not_lt.mpr hx] using h

end ResourceLimitedCompetition
