import proofs.CompositionalMemory.Scaling
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CompositionalMemory
open Finset

theorem exchange_drift_bound {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (zi Z κ : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, 0 ≤ z j ∧ z j ≤ Z)
    (hzi : 0 ≤ zi ∧ zi ≤ Z) (hZ : 0 ≤ Z) (hs : ∑ j, w j ≤ κ) :
    |∑ j, w j*(z j-zi)| ≤ Z*κ := by
  calc
    _ ≤ ∑ j, |w j*(z j-zi)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, w j*Z := by
      apply sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hw j)]
      apply mul_le_mul_of_nonneg_left _ (hw j)
      apply abs_le.mpr
      constructor <;> linarith only [(hz j).1,(hz j).2,hzi.1,hzi.2]
    _ = (∑ j, w j)*Z := (sum_mul ..).symm
    _ ≤ κ*Z := mul_le_mul_of_nonneg_right hs hZ
    _ = Z*κ := by ring

theorem exchange_activity_bound {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (zi Z κ : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, z j ≤ Z)
    (hzi : zi ≤ Z) (hZ : 0 ≤ Z) (hs : ∑ j, w j ≤ κ) :
    ∑ j, w j*(zi+z j) ≤ 2*Z*κ := by
  calc
    _ ≤ ∑ j, w j*(2*Z) := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (by linarith only [hzi,hz j]) (hw j)
    _ = (∑ j, w j)*(2*Z) := (sum_mul ..).symm
    _ ≤ κ*(2*Z) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

theorem exchange_first_moment {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (zi Z κ v : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, z j ≤ Z)
    (hzi : zi ≤ Z) (hZ : 0 ≤ Z) (hs : ∑ j, w j ≤ κ) (hv : 0 < v) :
    (∑ j, (v*w j*zi)*(1/v))+(∑ j, (v*w j*z j)*(1/v)) ≤ 2*Z*κ := by
  rw [← sum_add_distrib]
  have hid (j) : (v*w j*zi)*(1/v)+(v*w j*z j)*(1/v) = w j*(zi+z j) := by
    field_simp
  simp_rw [hid]
  exact exchange_activity_bound w z zi Z κ hw hz hzi hZ hs

/-- Both real directions are included, so cancellation of drift cannot hide noise. -/
theorem exchange_second_moment {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (zi Z κ N v : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, z j ≤ Z)
    (hzi : zi ≤ Z) (hZ : 0 ≤ Z) (hκ : 0 ≤ κ)
    (hs : ∑ j, w j ≤ κ) (hN : 0 < N) (hv : N ≤ v) :
    ∑ j, (v*w j*zi+v*w j*z j)*(1/v)^2 ≤ 2*Z*κ/N := by
  have hvpos : 0 < v := lt_of_lt_of_le hN hv
  have hid (j) : (v*w j*zi+v*w j*z j)*(1/v)^2 = (w j*(zi+z j))/v := by
    field_simp
  simp_rw [hid]
  rw [← sum_div]
  calc
    _ ≤ (2*Z*κ)/v := div_le_div_of_nonneg_right
      (exchange_activity_bound w z zi Z κ hw hz hzi hZ hs) hvpos.le
    _ ≤ (2*Z*κ)/N := div_le_div_of_nonneg_left (by positivity) hN hv

end CompositionalMemory
