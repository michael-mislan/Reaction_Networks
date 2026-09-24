import proofs.RAF1519.Refinement.PhaseCoefficients

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

theorem phase_exp_upper : Real.exp (6/7) ≤ 2357/1000 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 6/7) (by norm_num : (6/7:ℝ) ≤ 1)
    (by norm_num : 0 < (8:ℕ))
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem phase_exp_double_upper : Real.exp (12/7) ≤ 8*(961355/1382976) := by
  have he : Real.exp (12/7) = Real.exp (6/7)*Real.exp (6/7) := by
    rw [← Real.exp_add]
    norm_num
  rw [he]
  nlinarith [phase_exp_upper,Real.exp_pos (6/7),phase_exponential_rational_margin]

/-- The exact initial adjoint row dominates one eighth of productive stock. -/
theorem phase_initial_weight_bound (p : Fin 4) :
    phaseWeight p/8 ≤ Real.exp (-(48*(1/28)))*
      (∑ j : Fin 5, phaseCoeff j p*(1/28)^(j:ℕ)/Nat.factorial (j:ℕ)) := by
  have hp : 0 ≤ phaseWeight p := by fin_cases p <;> norm_num [phaseWeight]
  have hm := mul_le_mul_of_nonneg_right phase_exp_double_upper hp
  have hrow := phase_taylor_row_lower p
  norm_num only [show (48*(1/28):ℝ)=12/7 by norm_num]
  rw [Real.exp_neg,inv_eq_one_div,one_div_mul_eq_div]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  nlinarith

end
end RAF1519.Refinement
