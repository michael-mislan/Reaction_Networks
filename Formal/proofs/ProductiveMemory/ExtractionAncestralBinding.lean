import proofs.ProductiveMemory.ExtractionSupport
import proofs.ResourceLimitedCompetition.DeadlineValue

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
noncomputable section
set_option Elab.async false

def productiveAncestralObservable (N : ℕ) {D : Finset ProductiveState}
    (f : ℕ → ℕ → ℝ) (x : ProductiveStopped D) : ℝ :=
  f (ancestralMembrane true (productivePhysical N x).population.live)
    (ancestralMembrane false (productivePhysical N x).population.live)

def productiveActiveAncestralObservable (N : ℕ) {D : Finset ProductiveState}
    (f : ℕ → ℕ → ℝ) : ProductiveStopped D → ℝ
  | .inl s => productiveAncestralObservable N f (.inl s)
  | .inr _ => 0

theorem productive_legacy_ancestral (N : ℕ) (tag : Bool) (s : ProductiveState)
    (e : CellEvent s.population) :
    ancestralMembrane tag (productiveOutcome N s (.inl e)).population.live =
      ancestralMembrane tag s.population.live+
        (match e.2 with | .inl _ => 0 | .inr _ => if (selectedCell s.population e.1).high=tag then 1 else 0) := by
  classical
  let a : ActiveState ({s.population} : Finset PopulationState) := ⟨s.population,Finset.mem_singleton_self _⟩
  have h := event_ancestral_membrane N tag _ a e
  convert h using 1
  · rcases e with ⟨i,r | d⟩ <;> rfl
  · rcases e with ⟨i,r | d⟩ <;> rfl

theorem productive_extraction_ancestral (N : ℕ) (tag : Bool) (s : ProductiveState)
    (i : Fin s.population.live.length) :
    ancestralMembrane tag (productiveOutcome N s (.inr i)).population.live = ancestralMembrane tag s.population.live := by
  have h := congrArg (ancestralMembrane tag) (selected_decomposition s.population i)
  simpa only [productiveOutcome,extractionAt,ancestralMembrane_append,ancestralMembrane_cons] using h

theorem productive_ancestral_generator_binding (rho γ : ℝ) (hr : 0 ≤ rho) (hγ : 0 ≤ γ) (Ω N W0 J : ℕ)
    (zL zH : ℝ) (D : Finset ProductiveState) (f : ℕ → ℕ → ℝ) (s : ProductiveActive D) :
    (productiveStoppedModel rho γ hr hγ Ω N W0 J zL zH D).generator (productiveAncestralObservable N f) (.inl s)=
      resourceCoefficient γ s.val.population.resource Ω*
        (ancestralZ true s.val.population.live*
          (f (ancestralMembrane true s.val.population.live+1) (ancestralMembrane false s.val.population.live)-
            f (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live))+
        ancestralZ false s.val.population.live*
          (f (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live+1)-
            f (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live))) := by
  classical
  have hnext (e : ProductiveEvent s.val) :
      productivePhysical N (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩) =
        productiveOutcome N s.val e := productive_physical_chosen N W0 J rho zL zH D ⟨s,e⟩
  rw [productive_active_generator,Fintype.sum_sum_type]
  simp only [productiveAncestralObservable]
  simp only [hnext]
  simp only [productivePhysical]
  simp only [productive_extraction_ancestral,sub_self,mul_zero,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_sigma]
  simp only [productive_legacy_ancestral]
  simp_rw [Fintype.sum_sum_type]
  simp only [productiveRate,add_zero,sub_self,mul_zero,Finset.sum_const_zero,zero_add]
  have hdraw (i : Fin s.val.population.live.length) := daughter_constant_sum
    (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1
    (propensity (resourceCoefficient γ s.val.population.resource Ω) (selectedCell s.val.population i).compartment (.inr ()))
    (f (ancestralMembrane true s.val.population.live+(if (selectedCell s.val.population i).high=true then 1 else 0))
      (ancestralMembrane false s.val.population.live+(if (selectedCell s.val.population i).high=false then 1 else 0))-
      f (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live))
  simp_rw [hdraw]
  rw [ancestralZ_sum_selected,ancestralZ_sum_selected,Finset.sum_mul,Finset.sum_mul,
    ← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases (selectedCell s.val.population i).high <;> simp [propensity] <;> ring

theorem productive_active_ancestral_generator_le (rho γ : ℝ) (hr : 0 ≤ rho) (hγ : 0 ≤ γ) (Ω N W0 J : ℕ)
    (zL zH : ℝ) (D : Finset ProductiveState) (f : ℕ → ℕ → ℝ)
    (hf : ∀ H L, 0 ≤ f H L) (s : ProductiveActive D) :
    (productiveStoppedModel rho γ hr hγ Ω N W0 J zL zH D).generator (productiveActiveAncestralObservable N f) (.inl s) ≤
      (productiveStoppedModel rho γ hr hγ Ω N W0 J zL zH D).generator (productiveAncestralObservable N f) (.inl s) := by
  classical
  rw [productive_active_generator,productive_active_generator]
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (productive_rate_nonneg rho γ hr hγ Ω s.val e)
  apply sub_le_sub_right
  generalize productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩=x
  cases x with
  | inl t => exact le_rfl
  | inr e => exact hf _ _

end
end ProductiveMemory
