import Mathlib
namespace PhenotypeMemory
/-- Algebra after the strong-Markov extinction identity. -/
theorem threshold_bounds (s p a : ℝ) (ha : a < 1)
    (hl : s ≤ p) (hu : (1-a)*p ≤ s) : s ≤ p ∧ p ≤ s/(1-a) := by
  refine ⟨hl, ?_⟩
  apply (le_div_iff₀ (by linarith : 0 < 1-a)).2
  nlinarith
theorem pgf_enclosure (u0 uz lower upper factor : ℝ)
    (h0 : lower ≤ u0) (hz : uz ≤ upper) (hf : 1 ≤ factor) :
    1-lower-factor*(upper-lower) ≤ 1-u0-factor*(uz-u0) := by
  have h1 := mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr h0)
  have h2 := mul_nonneg (by linarith : 0 ≤ factor) (sub_nonneg.mpr hz)
  nlinarith
end PhenotypeMemory
