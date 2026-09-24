import proofs.ThermoCoreCompatibility.Hypergraph.MonomialTripleWindow

namespace ThermoCoreCompatibility.Hypergraph.MonomialTriple

/-- Uniform separation: tau is any lower bound for the nine original residuals. -/
theorem negative_margin {A B u l τ : ℝ} (hA : 0 ≤ A)
    (hu : u ≤ 89/125) (hl : 81/125 ≤ l)
    (h₀ : 5*B ≤ A+4*u-τ) (h₁ : 3*l+2*τ ≤ B+2*A^4)
    (h₂ : 5*τ ≤ 5*B-2*A-3*A^3) : τ ≤ -3/500 := by
  by_cases ha : A ≤ 7/8
  · have hp := pow_le_pow_left₀ hA ha 4
    norm_num at hp
    linarith
  · have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/8) (le_of_lt (lt_of_not_ge ha)) 3
    norm_num at hp
    linarith

/-- Scalar transfer used for every production residual. -/
theorem residual_transfer {p q ρ : ℝ} (h : |q-p| ≤ 5*ρ) : p-5*ρ ≤ q ∧ q ≤ p+5*ρ := by
  rw [abs_le] at h
  constructor <;> linarith

theorem robust_negative {p q : ℝ} (hp : p ≤ -3/500)
    (h : |q-p| ≤ 5*(1/1000000)) : q < 0 := by
  have ht := residual_transfer h
  linarith

theorem robust_positive {p q : ℝ} (hp : 9/100000 < p)
    (h : |q-p| ≤ 5*(1/1000000)) : 0 < q := by
  have ht := residual_transfer h
  linarith

end ThermoCoreCompatibility.Hypergraph.MonomialTriple
