import proofs.ProductiveMemory.ExtractionWitness

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

def recoveryError (N : ℕ) : ℝ :=
  (Real.exp (-((N:ℝ)*localAlpha*readyLevel))+2*Real.exp (-((N:ℝ)*localAlpha*readyLevel)/2))+
    (Real.exp (8*((N:ℝ)*localAlpha*readyLevel))+5376*extractionCeiling)/
      Real.exp ((N:ℝ)*localAlpha*outerLevel)

theorem recovery_error_expanded (N : ℕ) :
    recoveryError N = Real.exp (-((N:ℝ)*localAlpha*readyLevel))+
      2*Real.exp (-((N:ℝ)*localAlpha*readyLevel)/2)+
      Real.exp (-8*((N:ℝ)*localAlpha*readyLevel))+
      (336/625)*Real.exp (3/250-16*((N:ℝ)*localAlpha*readyLevel)) := by
  have ho : (N:ℝ)*localAlpha*outerLevel = 16*((N:ℝ)*localAlpha*readyLevel) := by
    unfold readyLevel; ring
  unfold recoveryError extractionCeiling
  rw [ho, add_div]
  have h1 : Real.exp (8*((N:ℝ)*localAlpha*readyLevel))/Real.exp (16*((N:ℝ)*localAlpha*readyLevel)) =
      Real.exp (-8*((N:ℝ)*localAlpha*readyLevel)) := by rw [← Real.exp_sub]; congr 1; ring
  rw [h1]
  have h2 : 5376*(localAlpha*100000000*Real.exp (120*localAlpha*100000000))/
        Real.exp (16*((N:ℝ)*localAlpha*readyLevel)) =
      (336/625)*(Real.exp (3/250)/Real.exp (16*((N:ℝ)*localAlpha*readyLevel))) := by
    norm_num [localAlpha]; ring
  rw [h2,← Real.exp_sub]
  ring

theorem recovery_error_antitone {N m : ℕ} (h : N ≤ m) : recoveryError m ≤ recoveryError N := by
  have hu : (N:ℝ)*localAlpha*readyLevel ≤ (m:ℝ)*localAlpha*readyLevel := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h)
      (by norm_num [localAlpha])) (by norm_num [readyLevel,outerLevel])
  rw [recovery_error_expanded, recovery_error_expanded]
  have h1 := Real.exp_le_exp.mpr (show -((m:ℝ)*localAlpha*readyLevel) ≤ -((N:ℝ)*localAlpha*readyLevel) by linarith)
  have h2 := Real.exp_le_exp.mpr (show -((m:ℝ)*localAlpha*readyLevel)/2 ≤ -((N:ℝ)*localAlpha*readyLevel)/2 by linarith)
  have h3 := Real.exp_le_exp.mpr (show -8*((m:ℝ)*localAlpha*readyLevel) ≤ -8*((N:ℝ)*localAlpha*readyLevel) by linarith)
  have h4 := Real.exp_le_exp.mpr (show 3/250-16*((m:ℝ)*localAlpha*readyLevel) ≤ 3/250-16*((N:ℝ)*localAlpha*readyLevel) by linarith)
  linarith only [h1,h2,h3,h4]

theorem recovery_error_uniform (m : ℕ) (hm : recoveryCount ≤ m) : recoveryError m ≤ 1/10^18 :=
  (recovery_error_antitone hm).trans recovery_error_evaluated

end
end ProductiveMemory
