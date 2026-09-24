import proofs.ProductiveMemory.ExtractionAncestralBinding
import proofs.ResourceLimitedCompetition.AncestralPersistence
import proofs.FiniteCopy.UniformizedBounds

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
open scoped NNReal

noncomputable local instance ProductivePersistenceDecEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) :=
  Classical.decEq _

def productiveAncestryBelowSet (N K : ℕ) (tag : Bool) (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | ancestralMembrane tag (productivePhysical N x).population.live < K}

theorem productive_stopped_ancestral_monotone (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (tag : Bool) (x : ProductiveStopped D) (e : ProductivePopulationEvent D) :
    ancestralMembrane tag (productivePhysical N x).population.live ≤
      ancestralMembrane tag (productivePhysical N (productiveStoppedNext N W0 J rho zL zH D x e)).population.live := by
  classical
  cases x with
  | inr t => exact le_rfl
  | inl s =>
    by_cases he : e.1=s
    · subst s
      rw [productive_physical_chosen]
      change ancestralMembrane tag e.1.val.population.live ≤ ancestralMembrane tag (productiveOutcome N e.1.val e.2).population.live
      cases hevent : e.2 with
      | inl ec =>
        rw [productive_legacy_ancestral]
        exact Nat.le_add_right _ _
      | inr i => rw [productive_extraction_ancestral]
    · simp only [productiveStoppedNext,he,if_false]
      exact le_rfl

theorem productive_ancestry_below_generator (rho γ : ℝ) (hγ : 0 ≤ γ) (hrho : 0 ≤ rho) (Ω N W0 J K : ℕ)
    (zL zH : ℝ) (D : Finset ProductiveState) (tag : Bool) (x : ProductiveStopped D) :
    (productiveStoppedModel rho γ hrho hγ Ω N W0 J zL zH D).generator
      (FiniteKernel.eventIndicator (productiveAncestryBelowSet N K tag D)) x ≤ 0 := by
  classical
  unfold FiniteJumpModel.generator
  apply Finset.sum_nonpos
  intro e _
  apply mul_nonpos_of_nonneg_of_nonpos ((productiveStoppedModel rho γ hrho hγ Ω N W0 J zL zH D).nonneg x e)
  apply sub_nonpos.mpr
  have hm := productive_stopped_ancestral_monotone N W0 J rho zL zH D tag x e
  simp only [FiniteKernel.eventIndicator,productiveAncestryBelowSet,Set.mem_setOf_eq,productiveStoppedModel]
  split_ifs <;> norm_num
  omega

theorem productive_ancestry_below_probability (rho γ : ℝ) (hγ : 0 ≤ γ) (hrho : 0 ≤ rho) (Ω N W0 J K : ℕ)
    (zL zH : ℝ) (D : Finset ProductiveState) (tag : Bool)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (productiveStoppedModel rho γ hrho hγ Ω N W0 J zL zH D).total x ≤ q)
    (x : ProductiveStopped D) (hx : K ≤ ancestralMembrane tag (productivePhysical N x).population.live) :
    ((productiveStoppedModel rho γ hrho hγ Ω N W0 J zL zH D).uniformize q hq hbound).poissonized (q*t)
      (FiniteKernel.eventIndicator (productiveAncestryBelowSet N K tag D)) x ≤ 0 := by
  classical
  have h := (productiveStoppedModel rho γ hrho hγ Ω N W0 J zL zH D).uniformized_event_bound q t hq hbound
    (productiveAncestryBelowSet N K tag D) (FiniteKernel.eventIndicator (productiveAncestryBelowSet N K tag D)) 1 0
    (by intro y; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (by intro y hy; simp only [FiniteKernel.eventIndicator,if_pos hy,le_refl])
    (productive_ancestry_below_generator rho γ hγ hrho Ω N W0 J K zL zH D tag) x
  simpa [FiniteKernel.eventIndicator,productiveAncestryBelowSet,not_lt.mpr hx] using h

end ProductiveMemory
