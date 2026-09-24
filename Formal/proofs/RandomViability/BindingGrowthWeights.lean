import Mathlib.Tactic

namespace RandomViability.Binding

noncomputable section

def weighted (x c₁ c₂ z : ℝ) : ℝ := x + 9/8*c₁ + 7/5*c₂ + 9/5*z

/-- Columnwise certificate for the literal four binding phases. -/
theorem growth_columns (u w K r : ℝ) (hu : 4/5 ≤ u) (hw : 4/5 ≤ w)
    (hK : 8 ≤ K) (hr : 18 ≤ r) :
    (2/5 : ℝ) ≤ (-20*u-1) + 9/8*(20*u) ∧
    (2/5 : ℝ)*(9/8) ≤ 20 + 9/8*(-21-20*w) + 7/5*(20*w) ∧
    (2/5 : ℝ)*(7/5) ≤ 9/8*20 + 7/5*(-41) + 9/5*20 ∧
    (2/5 : ℝ)*(9/5) ≤ 2*r + 7/5*(20/K) + 9/5*(-20/K-r-1) := by
  have hK0 : 0 < K := by linarith
  have hi : 20/K ≤ (5/2 : ℝ) := (div_le_iff₀ hK0).2 (by linarith)
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · norm_num
  · simp only [neg_div] at *
    linarith

/-- Positive reproduction accounts for free and bound catalyst together. -/
theorem weighted_linear_growth (u w K r x c₁ c₂ z : ℝ)
    (hu : 4/5 ≤ u) (hw : 4/5 ≤ w) (hK : 8 ≤ K) (hr : 18 ≤ r)
    (hx : 0 ≤ x) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hz : 0 ≤ z) :
    (2/5 : ℝ)*weighted x c₁ c₂ z ≤
      weighted ((-20*u-1)*x+20*c₁+2*r*z)
        (20*u*x+(-21-20*w)*c₁+20*c₂)
        (20*w*c₁-41*c₂+20/K*z) (20*c₂+(-20/K-r-1)*z) := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := growth_columns u w K r hu hw hK hr
  have a := mul_le_mul_of_nonneg_right h₀ hx
  have b := mul_le_mul_of_nonneg_right h₁ hc₁
  have c := mul_le_mul_of_nonneg_right h₂ hc₂
  have d := mul_le_mul_of_nonneg_right h₃ hz
  dsimp [weighted]
  nlinarith

/-- Young certificate used by the nonlinear food correction. -/
theorem food_penalty (a b : ℝ) :
    (5/2 : ℝ)*a + 44/9*b ≤ 1/5 + 48845/1296*(a^2+b^2) := by
  nlinarith [sq_nonneg (a-1620/48845), sq_nonneg (b-3168/48845)]

/-- Exact algebra after the literal mechanism's two drift estimates. -/
theorem corrected_drift (a b eps M dlog dS : ℝ)
    (hy : 2/5-5/2*a-44/9*b-eps/8-11/10*M ≤ dlog)
    (hs : dS ≤ -2*(a^2+b^2)+2*eps+5*M) :
    1/5-49007/1296*eps-1235381/12960*M ≤ dlog-48845/2592*dS := by
  have h := food_penalty a b
  linarith

theorem positive_average_margin :
    (1/500 : ℝ) < (1/5-49007/1296*(1/500000000))/(1235381/12960)
      -4*(1/500000000) := by norm_num

end
end RandomViability.Binding
