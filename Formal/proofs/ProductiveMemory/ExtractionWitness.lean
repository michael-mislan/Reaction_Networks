import proofs.ProductiveMemory.ExtractionReady

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

def recoveryCount : ℕ := 65536000000000000000000

theorem recovery_count_large : 480*100000000 ≤ (recoveryCount:ℝ)*readyLevel := by
  norm_num [recoveryCount,readyLevel,outerLevel]

theorem recovery_count_exponent : (recoveryCount:ℝ)*localAlpha*readyLevel = 128 := by
  norm_num [recoveryCount,localAlpha,readyLevel,outerLevel]

theorem exp_tail_64 (x : ℝ) (hx : 64 ≤ x) : Real.exp (-x) ≤ 1/(2:ℝ)^64 := by
  have h1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 64
  have he : (Real.exp 1)^64 = Real.exp 64 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he] at hp
  calc
    Real.exp (-x) ≤ Real.exp (-64) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1/(2:ℝ)^64 := by
      rw [Real.exp_neg,inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) hp

theorem recovery_error_evaluated :
    (Real.exp (-((recoveryCount:ℝ)*localAlpha*readyLevel))+
      2*Real.exp (-((recoveryCount:ℝ)*localAlpha*readyLevel)/2))+
    (Real.exp (8*((recoveryCount:ℝ)*localAlpha*readyLevel))+5376*extractionCeiling)/
      Real.exp ((recoveryCount:ℝ)*localAlpha*outerLevel) ≤ 1/10^18 := by
  rw [recovery_count_exponent]
  have hb : (recoveryCount:ℝ)*localAlpha*outerLevel = 2048 := by
    norm_num [recoveryCount,localAlpha,outerLevel]
  rw [hb]
  have hid : (Real.exp (8*(128:ℝ))+5376*extractionCeiling)/Real.exp 2048 =
      Real.exp (-1024)+(336/625)*Real.exp (-(511997/250)) := by
    unfold extractionCeiling localAlpha
    rw [add_div]
    have h1 : Real.exp (8*(128:ℝ))/Real.exp 2048 = Real.exp (-1024) := by
      rw [← Real.exp_sub]; norm_num
    rw [h1]
    have h2 : 5376*((1/1000000000000:ℝ)*100000000*Real.exp (120*(1/1000000000000)*100000000))/Real.exp 2048 =
        (336/625)*(Real.exp (3/250)/Real.exp 2048) := by norm_num; ring
    rw [h2,← Real.exp_sub]
    norm_num
  rw [hid]
  have h1 := exp_tail_64 128 (by norm_num)
  have h2 := exp_tail_64 64 (by norm_num)
  have h3 := exp_tail_64 1024 (by norm_num)
  have h4 := exp_tail_64 (511997/250) (by norm_num)
  norm_num at h1 h2 h3 h4 ⊢
  linarith only [h1,h2,h3,h4]

end
end ProductiveMemory
