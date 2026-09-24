import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ResourceLimitedCompetition

theorem membrane_log_bounds (B : ℝ) (hB : 1000 ≤ B) :
    (999/1000 : ℝ) ≤ B*Real.log (1+1/B) ∧
      B*Real.log (1+1/B) ≤ 1 ∧ 0 ≤ Real.log (1+1/B) := by
  have hpos : 0 < B := by linarith only [hB]
  have hx : 0 ≤ 1/B := (one_div_pos.mpr hpos).le
  have hlo := Real.le_log_one_add_of_nonneg hx
  have hhi := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+1/B)
  have hmul := mul_le_mul_of_nonneg_left hlo hpos.le
  have hid : B*(2*(1/B)/(1/B+2))=2*B/(1+2*B) := by
    field_simp
  rw [hid] at hmul
  have hrat : (999/1000 : ℝ) ≤ 2*B/(1+2*B) := by
    apply (le_div_iff₀ (by linarith only [hpos])).mpr
    linarith only [hB]
  refine ⟨hrat.trans hmul,?_,Real.log_nonneg (by linarith only [hx])⟩
  have htop := mul_le_mul_of_nonneg_left hhi hpos.le
  have hcancel : B*(1+1/B-1)=1 := by field_simp; ring
  rwa [hcancel] at htop

theorem population_log_drift (BH BL aH aL : ℝ) (hBH : 1000 ≤ BH) (hBL : 1000 ≤ BL)
    (haH : (297/100 : ℝ) ≤ aH ∧ aH ≤ 3)
    (haL : (99/100 : ℝ) ≤ aL ∧ aL ≤ 101/100) :
    (39/20 : ℝ) ≤ aH*BH*Real.log (1+1/BH)-aL*BL*Real.log (1+1/BL) ∧
      (aH*BH+aL*BL)*Real.log (1+1/(BH+BL)) ≤ 3 ∧
      (49/50 : ℝ) ≤ (aH*BH+aL*BL)*Real.log (1+1/(BH+BL)) := by
  obtain ⟨hh,hhmax,_⟩ := membrane_log_bounds BH hBH
  obtain ⟨_,hlmax,hlnon⟩ := membrane_log_bounds BL hBL
  obtain ⟨hw,hwmax,hwnon⟩ := membrane_log_bounds (BH+BL) (by linarith only [hBH,hBL])
  have hBhpos : 0 ≤ BH := by linarith only [hBH]
  have hBlpos : 0 ≤ BL := by linarith only [hBL]
  have hH := mul_le_mul haH.1 hh (by norm_num : (0:ℝ) ≤ 999/1000) (by linarith only [haH.1])
  have hL := mul_le_mul haL.2 hlmax (mul_nonneg hBlpos hlnon) (by norm_num : (0:ℝ) ≤ 101/100)
  have hupper : aH*BH+aL*BL ≤ 3*(BH+BL) := by
    have h1 := mul_le_mul_of_nonneg_right haH.2 hBhpos
    have h2 := mul_le_mul_of_nonneg_right haL.2 hBlpos
    nlinarith only [h1,h2,hBlpos]
  have hlower : (99/100 : ℝ)*(BH+BL) ≤ aH*BH+aL*BL := by
    have h1 := mul_le_mul_of_nonneg_right haH.1 hBhpos
    have h2 := mul_le_mul_of_nonneg_right haL.1 hBlpos
    nlinarith only [h1,h2,hBhpos]
  have hWU := mul_le_mul_of_nonneg_right hupper hwnon
  have hWL := mul_le_mul_of_nonneg_right hlower hwnon
  constructor
  · nlinarith only [hH,hL]
  constructor
  · nlinarith only [hWU,hwmax]
  · nlinarith only [hWL,hw]

end ResourceLimitedCompetition
