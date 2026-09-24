import Mathlib.Tactic

namespace RAF1519.Refinement
noncomputable section

theorem pulse_material_center_count (V q e M R : ℝ) (hV : 0 ≤ V)
    (hq : 1/4 ≤ q ∧ q ≤ 3/4) (he : -(1/200) ≤ e ∧ e ≤ 1/200)
    (hM : (159/160)*V ≤ M ∧ M ≤ (161/160)*V)
    (hR : (49/50)*q*M ≤ R ∧ R ≤ q*M) :
    (31213/32000)*V ≤ R+V*(1-q+e) ∧ R+V*(1-q+e) ≤ (3231/3200)*V := by
  have hq0 : 0 ≤ q := by linarith
  have hL := mul_le_mul_of_nonneg_left hM.1 (show 0 ≤ (49/50)*q by positivity)
  have hU := mul_le_mul_of_nonneg_left hM.2 hq0
  have hqL := mul_le_mul_of_nonneg_right hq.1 hV
  have hqU := mul_le_mul_of_nonneg_right hq.2 hV
  have heL := mul_le_mul_of_nonneg_right he.1 hV
  have heU := mul_le_mul_of_nonneg_right he.2 hV
  constructor <;> nlinarith

theorem pulse_stock_mean_lower (V q Y R : ℝ) (hV : 0 ≤ V)
    (hq : 1/4 ≤ q) (hY : V/20 ≤ Y) (hR : (49/50)*q*Y ≤ R) :
    (49/4000)*V ≤ R := by
  have hq0 : 0 ≤ q := by linarith
  have hL := mul_le_mul_of_nonneg_left hY (show 0 ≤ (49/50)*q by positivity)
  have hqV := mul_le_mul_of_nonneg_right hq hV
  nlinarith

/-- Floor refill is included; a material deviation of V/100 leaves a strict margin. -/
theorem pulse_material_prepared (V R F D X : ℝ) (hV : 10000 ≤ V)
    (hcenter : (31213/32000)*V ≤ R+F ∧ R+F ≤ (3231/3200)*V)
    (hdose : F-1 < D ∧ D ≤ F) (hdev : |X-R| < V/100) :
    |(X+D)/V-1| ≤ 1/25 := by
  have hV0 : 0 < V := by linarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hdev
  apply abs_le.mpr
  constructor
  · have hb : (24/25)*V ≤ X+D := by linarith [hcenter.1,hdose.1]
    have hn := (le_div_iff₀ hV0).mpr hb
    linarith
  · have hb : X+D ≤ (26/25)*V := by linarith [hcenter.2,hdose.2]
    have hn := (div_le_iff₀ hV0).mpr hb
    linarith

theorem pulse_stock_prepared (V R X : ℝ) (hV : 0 < V)
    (hmean : (49/4000)*V ≤ R) (hdev : -(X-R) < V/4000) : 3/250 ≤ X/V := by
  apply (le_div_iff₀ hV).mpr
  linarith

end
end RAF1519.Refinement
