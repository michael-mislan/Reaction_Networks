import Mathlib.Tactic

namespace RandomViability
open Classical
noncomputable section
set_option maxHeartbeats 30000

def productiveWaitWidth (m : ℕ) : ℝ := 1/(2*(m : ℝ))

def productiveWaitLower (m i : ℕ) : ℝ :=
  if i < m then 0 else
  if i < 3*m then 45/(m : ℝ)+(if i=m then 1 else 0) else 100

theorem productive_wait_width_pos (m : ℕ) (hm : 0 < m) : 0 < productiveWaitWidth m := by
  unfold productiveWaitWidth
  positivity

theorem productive_wait_lower_nonneg (m i : ℕ) : 0 ≤ productiveWaitLower m i := by
  unfold productiveWaitLower
  split_ifs <;> positivity

theorem productive_wait_startup_sum (m : ℕ) :
    (∑ i ∈ Finset.range m, productiveWaitLower m i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact if_pos (Finset.mem_range.mp hi)

theorem productive_wait_operating_sum (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range (3*m), productiveWaitLower m i) = 91 := by
  have hval : ∀ j ∈ Finset.range (2*m), productiveWaitLower m (m+j) =
      45/(m : ℝ)+(if j=0 then 1 else 0) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [productiveWaitLower, if_neg (show ¬m+j<m by omega),
      if_pos (show m+j<3*m by omega)]
    congr 1
    simp
  rw [show 3*m=m+2*m by omega, Finset.sum_range_add, productive_wait_startup_sum, zero_add]
  simp_rw [Finset.sum_congr rfl hval]
  rw [Finset.sum_add_distrib]
  have hconst : (∑ _j ∈ Finset.range (2*m), 45/(m : ℝ)) = 90 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    field_simp
    ring
  rw [hconst]
  norm_num [show 0 < 2*m by omega]

theorem productive_wait_paid_sum (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range (3*m+1), productiveWaitLower m i) = 191 := by
  rw [Finset.sum_range_succ, productive_wait_operating_sum m hm]
  have he : productiveWaitLower m (3*m)=100 := by simp [productiveWaitLower]; omega
  rw [he]
  norm_num

theorem productive_wait_startup_upper (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m, (productiveWaitLower m i+productiveWaitWidth m)) = 1/2 := by
  rw [Finset.sum_add_distrib, productive_wait_startup_sum, zero_add]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, productiveWaitWidth]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

theorem productive_wait_operating_upper (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range (3*m), (productiveWaitLower m i+productiveWaitWidth m)) = 185/2 := by
  rw [Finset.sum_add_distrib, productive_wait_operating_sum m hm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, productiveWaitWidth,
    Nat.cast_mul, Nat.cast_ofNat]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp
  ring

theorem productive_wait_paid_upper (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range (3*m+1), (productiveWaitLower m i+productiveWaitWidth m)) < 200 := by
  rw [Finset.sum_range_succ, productive_wait_operating_upper m hm]
  have he : productiveWaitLower m (3*m)=100 := by simp [productiveWaitLower]; omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : productiveWaitWidth m ≤ 1/2 := by
    unfold productiveWaitWidth
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*m)).mpr
    linarith
  rw [he]
  linarith

end
end RandomViability
