import proofs.RAF1519.Refinement.CountConcentration

namespace RAF1519.Refinement
noncomputable section

def countTolerance (Δ : ℝ) : ℝ := 1/(100000*(1+Δ))
def countThreshold (Δ : ℝ) : ℝ := (19/20)*countTolerance Δ
def countTilt (V Δ : ℝ) : ℝ := V*countThreshold Δ/(6400*(1+Δ))

theorem count_tolerance_positive (Δ : ℝ) (hΔ : 0 ≤ Δ) : 0 < countTolerance Δ := by
  unfold countTolerance
  positivity

theorem count_threshold_bounds (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    0 ≤ countThreshold Δ ∧ countThreshold Δ ≤ 1 := by
  have he := count_tolerance_positive Δ hΔ
  have he1 : countTolerance Δ ≤ 1 := by
    unfold countTolerance
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  unfold countThreshold
  constructor <;> nlinarith

theorem count_tilt_small (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ) :
    0 ≤ countTilt V Δ ∧ countTilt V Δ*(2/V) ≤ 1 := by
  have hd := count_threshold_bounds Δ hΔ
  have ha : 0 < 1+Δ := by positivity
  constructor
  · unfold countTilt
    exact div_nonneg (mul_nonneg hV.le hd.1) (by positivity)
  · have he : countTilt V Δ*(2/V) = countThreshold Δ/(3200*(1+Δ)) := by
      unfold countTilt
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [hd.2]

theorem count_interval_reserve (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hlarge : 40/countTolerance Δ ≤ V) :
    countThreshold Δ+2/V ≤ countTolerance Δ := by
  have he := count_tolerance_positive Δ hΔ
  have hm : 40 ≤ V*countTolerance Δ := (div_le_iff₀ he).mp hlarge
  have hj : 2/V ≤ countTolerance Δ/20 := by
    apply (div_le_iff₀ hV).mpr
    nlinarith
  unfold countThreshold
  linarith

theorem count_optimized_exponent (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ) :
    -countTilt V Δ*countThreshold Δ+(countTilt V Δ)^2*(800*(1+Δ)/V)*4 =
      -(361/51200000000000000)*V/(1+Δ)^3 := by
  have ha : 0 < 1+Δ := by positivity
  unfold countTilt countThreshold countTolerance
  field_simp
  ring

theorem count_exponent_margin (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ) :
    -countTilt V Δ*countThreshold Δ+(countTilt V Δ)^2*(800*(1+Δ)/V)*4 ≤
      -V/(200000000000000*(1+Δ)^3) := by
  rw [count_optimized_exponent V Δ hV hΔ]
  have hq : 0 ≤ V/(1+Δ)^3 := by positivity
  have he : -V/(200000000000000*(1+Δ)^3) = -(1/200000000000000)*(V/(1+Δ)^3) := by
    rw [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  rw [mul_div_assoc]
  nlinarith

theorem count_small_volume_trivial (V Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hsmall : V ≤ 40/countTolerance Δ) :
    1 ≤ 2*ENNReal.ofReal (Real.exp (-V/(200000000000000*(1+Δ)^3))) := by
  have ha : 0 < 1+Δ := by positivity
  have he : 40/countTolerance Δ = 4000000*(1+Δ) := by
    unfold countTolerance
    field_simp
    ring
  rw [he] at hsmall
  have hs : 1 ≤ (1+Δ)^2 := by nlinarith
  have hc : 1+Δ ≤ (1+Δ)^3 := by
    have hh := mul_le_mul_of_nonneg_right hs ha.le
    nlinarith
  have hx : V/(200000000000000*(1+Δ)^3) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hex : (1:ℝ) ≤ 2*Real.exp (-V/(200000000000000*(1+Δ)^3)) := by
    have hh := Real.add_one_le_exp (-V/(200000000000000*(1+Δ)^3))
    simp only [neg_div] at hh ⊢
    linarith
  have hh := ENNReal.ofReal_le_ofReal hex
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] using hh

end
end RAF1519.Refinement
