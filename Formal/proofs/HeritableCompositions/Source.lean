import proofs.FiniteCopy.CountSource
import proofs.HeritableCompositions.GrowthDrift

namespace HeritableCompositions
open FiniteCopy

abbrev Compartment := Counts × ℕ
abbrev Channel := Fin 13 ⊕ Unit

def nextCompartment (s : Compartment) : Channel → Compartment
  | .inl r => (nextCounts s.1 r, s.2)
  | .inr _ => (Function.update s.1 2 (s.1 2-1), s.2+1)

noncomputable def propensity (γ : ℝ) (s : Compartment) : Channel → ℝ
  | .inl r => (s.2 : ℝ)*densityRates (1/100000) (1/(s.2 : ℝ))
      (concentration s.2 s.1) r
  | .inr _ => γ*(s.1 2 : ℝ)

theorem propensity_nonneg (γ : ℝ) (hγ : 0 ≤ γ) (s : Compartment) (r : Channel) :
    0 ≤ propensity γ s r := by
  cases r with
  | inl r => exact mul_nonneg (Nat.cast_nonneg _) (lattice_rates_nonneg _ (by norm_num) _ _ r)
  | inr r => exact mul_nonneg hγ (Nat.cast_nonneg _)

theorem disabled_membrane (γ : ℝ) (s : Compartment) (h : s.1 2 = 0) :
    propensity γ s (.inr ()) = 0 := by simp [propensity, h]

theorem membrane_count_update (s : Compartment) (h : 1 ≤ s.1 2) (i : Fin 4) :
    ((nextCompartment s (.inr ())).1 i : ℝ) = (s.1 i : ℝ)-membraneDirection i := by
  fin_cases i <;> simp [nextCompartment, membraneDirection]
  have hn : ((s.1 2-1 : ℕ) : ℝ) = (s.1 2 : ℝ)-(1 : ℝ) := by
    rw [Nat.cast_sub h, Nat.cast_one]
  exact hn

theorem membrane_concentration_update (s : Compartment)
    (hm : 0 < s.2) (h : 1 ≤ s.1 2) (i : Fin 4) :
    concentration (nextCompartment s (.inr ())).2 (nextCompartment s (.inr ())).1 i -
      concentration s.2 s.1 i =
    -(concentration s.2 s.1 i+membraneDirection i)/((s.2 : ℝ)+1) := by
  simp only [concentration, membrane_count_update s h i]
  change ((s.1 i : ℝ)-membraneDirection i)/((s.2+1 : ℕ) : ℝ)-(s.1 i : ℝ)/(s.2 : ℝ) = _
  rw [Nat.cast_add, Nat.cast_one]
  exact membrane_jump _ _ _ (by exact_mod_cast hm)

end HeritableCompositions
