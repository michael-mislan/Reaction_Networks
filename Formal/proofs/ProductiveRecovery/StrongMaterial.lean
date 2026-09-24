import proofs.ProductiveRecovery.MaterialCoordinates
namespace ProductiveRecovery
noncomputable section
theorem strong_material_interior (a : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt a (1-a t) t)
    (h0 : 9/10 ≤ a 0 ∧ a 0 ≤ 11/10) :
    ∀ t, 3 ≤ t → 159/160 ≤ a t ∧ a t ≤ 161/160 := by
  intro t ht
  have he4 : 16 ≤ Real.exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  have het : 16 ≤ Real.exp t := he4.trans (Real.exp_le_exp.mpr ht)
  have hi : Real.exp (-t) ≤ 1/16 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos t)).2
    linarith
  have hpos : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hlo := mul_le_mul_of_nonneg_right h0.1 hpos
  have hup := mul_le_mul_of_nonneg_right h0.2 hpos
  rw [affine_material_solution a hd t (by linarith)]
  constructor <;> nlinarith

end
end ProductiveRecovery
