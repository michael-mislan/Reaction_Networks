import proofs.RandomViability.BindingOutputModel

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

theorem export_exp_half : Real.exp (-(1:ℝ)/2) ≤ 2/3 := by
  have h := Real.add_one_le_exp (1/2:ℝ)
  have he : Real.exp (-(1:ℝ)/2)*Real.exp ((1:ℝ)/2)=1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(1:ℝ)/2)]

theorem export_tilt_bound (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*(Real.exp (-(exportUnits j:ℝ)/8)-1)) ≤
      -(5/27)*weightedCount N := by
  have hhalf := export_exp_half
  have hone : Real.exp (-1) ≤ 2/3 :=
    (Real.exp_le_exp.mpr (by norm_num : (-1:ℝ) ≤ -1/2)).trans hhalf
  have hx := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) (N 2))
  have hc1 := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) (N 3))
  have hc2 := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) (N 4))
  have hz := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg (α := ℝ) (N 5))
  have hw := export_intensity_from_weight (N 2) (N 3) (N 4) (N 5)
    (by positivity) (by positivity) (by positivity)
  norm_num [countRate,exportUnits,Fin.sum_univ_succ]
  unfold weightedCount
  nlinarith

theorem export_tilt_floor (N : Counts) (V eps k r : ℝ) (h : 20000 ≤ weightedCount N) :
    (∑ j,countRate N V eps k r j*(Real.exp (-(exportUnits j:ℝ)/8)-1)) ≤ -(100000:ℝ)/27 := by
  have hb := export_tilt_bound N V eps k r
  linarith

theorem evaluated_export_budget : Real.exp (-(16250000:ℝ)/27) < 1/10000 := by
  have h := exp_neg_polynomial_upper (16250000/27) (by norm_num) 1
  norm_num at h
  linarith

end
end RandomViability.Binding
