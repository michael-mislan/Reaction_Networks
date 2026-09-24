import proofs.RandomViability.BindingGrowthWeights

namespace RandomViability.Binding
noncomputable section

/-- Concentration-normalized quadratic variation upper expression. The actual
2X propensity is smaller because its falling factorial is N_X(N_X-1). -/
def varianceEnvelope (u w x c₁ c₂ z eps k r : ℝ) : ℝ :=
  eps*u*w + eps*k*x + (20*x*u+20*c₁)*(1/8)^2 +
  (20*c₁*w+20*c₂)*(11/40)^2 + (20*c₂+20*k*z)*(2/5)^2 +
  (r*z+r*x*x)*(1/5)^2 + x+(9/8)^2*c₁+(7/5)^2*c₂+(9/5)^2*z

theorem variance_envelope_bound (u w x c₁ c₂ z eps k r : ℝ)
    (hu : u ≤ 5/2) (hw : w ≤ 5/2) (huw : u*w ≤ 25/16)
    (hx : 0 ≤ x) (hxx : x ≤ 5/4)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hz : 0 ≤ z)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr1 : r ≤ 22) :
    varianceEnvelope u w x c₁ c₂ z eps k r ≤
      5*weighted x c₁ c₂ z+(25/16)*eps := by
  have b₀ := mul_le_mul_of_nonneg_left huw heps
  have b₁ : eps*k*x ≤ (1/8)*x := by
    have he : eps*k ≤ 1/8 := (mul_le_mul_of_nonneg_right heps1 hk).trans (by simpa using hk1)
    exact mul_le_mul_of_nonneg_right he hx
  have b₂ := mul_le_mul_of_nonneg_left hu hx
  have b₃ := mul_le_mul_of_nonneg_left hw hc₁
  have b₄ := mul_le_mul_of_nonneg_right hk1 hz
  have b₅ := mul_le_mul_of_nonneg_right hr1 hz
  have b₆ : r*x*x ≤ (55/2)*x := by
    have hb : r*x ≤ 55/2 := (mul_le_mul_of_nonneg_left hxx hr).trans
      (by nlinarith)
    exact mul_le_mul_of_nonneg_right hb hx
  dsimp [varianceEnvelope,weighted]
  nlinarith

theorem copy_noise_specialization :
    (2 : ℝ)*(5*1000+(25/16)*(1/500000000)*100000000)/1000^2 < 11/1000 := by
  norm_num

end
end RandomViability.Binding
