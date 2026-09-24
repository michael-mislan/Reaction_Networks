import proofs.CompositionalMemory.LineageNecessity

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem capped_survival_exponential (N m : ℕ) :
    (1-(1/2 : ℝ)^(280*N))^m ≤ Real.exp (-(m : ℝ)*(1/2 : ℝ)^(280*N)) := by
  have hb : 0 ≤ 1-(1/2 : ℝ)^(280*N) :=
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  have he : 1-(1/2 : ℝ)^(280*N) ≤ Real.exp (-((1/2 : ℝ)^(280*N))) := by
    have h := Real.add_one_le_exp (-((1/2 : ℝ)^(280*N)))
    linarith only [h]
  have h := pow_le_pow_left₀ hb he m
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 1
  ring

theorem necessary_copy_budget (N m : ℕ) (hm : 1 ≤ m) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1)
    (hs : 1-η ≤ (1-(1/2 : ℝ)^(280*N))^m) :
    Real.log ((m : ℝ)/(-Real.log (1-η)))/(280*Real.log 2) ≤ N := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hbase : 0 < 1-η := by linarith only [hη1]
  have hL : 0 < -Real.log (1-η) := neg_pos.mpr (Real.log_neg hbase (by linarith only [hη]))
  have hl := Real.log_le_log hbase (hs.trans (capped_survival_exponential N m))
  rw [Real.log_exp] at hl
  have hproduct : (m : ℝ)*(1/2 : ℝ)^(280*N) ≤ -Real.log (1-η) := by linarith only [hl]
  have hp : (0 : ℝ) < (1/2 : ℝ)^(280*N) := by positivity
  have hh := Real.log_le_log (mul_pos hmp hp) hproduct
  rw [Real.log_mul hmp.ne' hp.ne',Real.log_pow] at hh
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [Real.log_div (by norm_num) (by norm_num),Real.log_one]; ring
  rw [hhalf] at hh
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 280) (Real.log_pos (by norm_num)))).mpr
  rw [Real.log_div hmp.ne' hL.ne']
  push_cast at hh
  nlinarith only [hh]

end CompositionalMemory
