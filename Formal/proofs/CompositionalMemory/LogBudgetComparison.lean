import proofs.CompositionalMemory.NecessaryCopies

namespace CompositionalMemory

theorem negative_log_failure_le (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1/2) :
    -Real.log (1-η) ≤ 2*η := by
  have hb : 0 < 1-η := by linarith only [hηhalf]
  have hi : (1-η)⁻¹ ≤ 1+2*η := by
    rw [← one_div]
    apply (div_le_iff₀ hb).mpr
    nlinarith only [mul_nonneg hη.le (show 0 ≤ 1-2*η by linarith only [hηhalf])]
  have hl := Real.one_sub_inv_le_log_of_pos hb
  linarith only [hi,hl]

theorem necessary_copy_budget_simple (N m : ℕ) (hm : 1 ≤ m) (η : ℝ)
    (hη : 0 < η) (hηhalf : η ≤ 1/2)
    (hs : 1-η ≤ (1-(1/2 : ℝ)^(280*N))^m) :
    Real.log ((m : ℝ)/(2*η))/(280*Real.log 2) ≤ N := by
  have hη1 : η < 1 := by linarith only [hηhalf]
  have hn := necessary_copy_budget N m hm η hη hη1 hs
  apply le_trans _ hn
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
  have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  apply Real.log_le_log (div_pos hmp (mul_pos (by norm_num) hη))
  exact div_le_div_of_nonneg_left hmp.le
    (neg_pos.mpr (Real.log_neg (by linarith only [hη1]) (by linarith only [hη])))
    (negative_log_failure_le η hη hηhalf)

end CompositionalMemory
