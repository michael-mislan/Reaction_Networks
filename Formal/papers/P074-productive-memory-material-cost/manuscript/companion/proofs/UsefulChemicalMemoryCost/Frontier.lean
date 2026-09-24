import proofs.UsefulChemicalMemoryCost.RobustEnvelope
import proofs.UsefulChemicalMemoryCost.MaterialBound

namespace UsefulChemicalMemoryCost

/-- Exact margins only; external recurrence numerators are NOT imported as axioms. -/
theorem exact_frontier_margins :
    (2145514420 : ℚ)/2147483648 > 999/1000 ∧
    (2144298834 : ℚ)/2147483648 < 999/1000 ∧
    (511 : ℚ)/512 < 999/1000 := by norm_num

theorem ten_cycle_margin : ((2145514420 : ℚ)/2147483648)^10 > 99/100 := by
  norm_num

/-- A witness at one admitted parameter excludes a robust guarantee. -/
theorem robust_exclusion {β : Type*} (A : Set β) (p : ℕ → β → ℝ)
    (θ : β) (hθ : θ∈A) (K : ℕ) (target : ℝ) (h : p K θ < target) :
    ¬ (∀ t∈A, target ≤ p K t) := by
  intro hall
  exact (not_lt_of_ge (hall θ hθ)) h

/-- Explicit finite coverage, not monotonicity in material budget. -/
theorem exact_minimum_from_coverage (good : ℕ → Prop)
    (h32 : good 32) (hsmall : ∀ K, 2 ≤ K → K ≤ 14 → ¬good K)
    (hfinite : ∀ K, 15 ≤ K → K ≤ 31 → ¬good K) :
    good 32 ∧ ∀ K, 2 ≤ K → good K → 32 ≤ K := by
  refine ⟨h32, ?_⟩
  intro K hK hg
  by_contra h
  by_cases hs : K ≤ 14
  · exact hsmall K hK hs hg
  · exact hfinite K (by omega) (by omega) hg

end UsefulChemicalMemoryCost
