import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 30000

namespace CompositionalMemory

/-- One coordinate of the exact membrane jump, with consumption indicator b. -/
theorem membrane_jump (k m n b : ℝ) (hm : 0 < m) :
    k * (n-b)/(m+1) - k*n/m = -(k*n/m+k*b)/(m+1) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm1 : m+1 ≠ 0 := by positivity
  field_simp [hm0, hm1]
  ring

/-- The propensity identities cover all resident reaction orders in the source. -/
theorem physical_propensity_scaling (k m a n p : ℝ) (hk : 0 < k) (hm : 0 < m) :
    a/k^2*m = (1/k)*(a*(m/k)) ∧
    a/k*n = (1/k)*(a*n) ∧
    a*n*p/m = (1/k)*(a*n*p/(m/k)) := by
  have hk0 := ne_of_gt hk
  have hm0 := ne_of_gt hm
  constructor
  · field_simp [hk0]
  constructor
  · ring
  · field_simp [hk0, hm0]

theorem real_volume_pair_nonneg (v : ℝ) (hv : 0 ≤ v) (n : ℕ) :
    0 ≤ ((n : ℝ)/v)*((n : ℝ)/v-1/v) := by
  rcases n with _ | n
  · simp
  · have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact mul_nonneg (div_nonneg (by positivity) hv)
      (sub_nonneg.mpr (div_le_div_of_nonneg_right hn hv))

/-- This is the dimension cancellation in the exact membrane second moment. -/
theorem membrane_second_moment_scalar (k m N U : ℝ)
    (hk : 1 ≤ k) (hN : 0 < N) (hm : k*N ≤ m) (hU : 0 ≤ U) :
    m/(m+1)^2*(U^2+2*U+k) ≤ (U+1)^2/N := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (mul_pos hk0 hN) hm
  have hm1 : 0 < m+1 := by positivity
  have hpoly : U^2+2*U+k ≤ k*(U+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ U^2+2*U by positivity)]
  have hbase : m/(m+1)^2 ≤ 1/m := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hm1) hm0).mpr
    nlinarith
  have hpos : 0 ≤ U^2+2*U+k := by positivity
  calc
    m/(m+1)^2*(U^2+2*U+k) ≤ (1/m)*(U^2+2*U+k) :=
      mul_le_mul_of_nonneg_right hbase hpos
    _ ≤ (1/m)*(k*(U+1)^2) := mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = k*(U+1)^2/m := by ring
    _ ≤ (U+1)^2/N := by
      apply (div_le_div_iff₀ hm0 hN).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg (U+1))]

theorem source_deterministic_budget :
    (23856*(1/100000000000 : ℝ)+336*(1/1000000000 : ℝ))^2 ≤
      (59/200 : ℝ)^2*(1/512000000)/42 := by norm_num

/-- Annular decay is a scalar consequence of D1, D2 and energy coercivity. -/
theorem annular_decay (r E A f deriv : ℝ)
    (hr : 0 ≤ r) (hA : A ≤ E) (hE : E ≤ 42*r^2)
    (hbudget : f^2 ≤ (59/200 : ℝ)^2*A/42)
    (hdrift : deriv ≤ -(59/100 : ℝ)*r^2+f*r) :
    deriv ≤ -(59/8400 : ℝ)*E := by
  have hfr : f ≤ (59/200 : ℝ)*r := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hfr hr
  nlinarith only [hdrift,hmul,hE]

end CompositionalMemory
