import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace OptimalAffinityRealizability

theorem exp_tangent_gap_pos {q a : ℝ} (hq : 1 < q) (ha : a ≠ 0) :
    0 < Real.exp (q * a) - q * Real.exp a + q - 1 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hi : 0 < 1 / q := one_div_pos.mpr hq0
  have hj : 0 < 1 - 1 / q := by
    have := (div_lt_one hq0).mpr hq
    linarith
  have hn : q * a ≠ (0 : ℝ) := mul_ne_zero (ne_of_gt hq0) ha
  have hc := strictConvexOn_exp.2 (Set.mem_univ (q*a)) (Set.mem_univ 0)
    hn hi hj (show 1 / q + (1 - 1 / q) = 1 by ring)
  have hid : (1 / q) * (q * a) + (1 - 1 / q) * 0 = a := by
    field_simp
    ring
  simp only [smul_eq_mul, hid, Real.exp_zero, mul_one] at hc
  have hm := mul_lt_mul_of_pos_left hc hq0
  field_simp at hm
  nlinarith

theorem exp_tangent_gap_nonneg {q a : ℝ} (hq : 1 < q) :
    0 ≤ Real.exp (q * a) - q * Real.exp a + q - 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · exact le_of_lt (exp_tangent_gap_pos hq ha)

theorem exp_tangent_gap_eq_zero_iff {q a : ℝ} (hq : 1 < q) :
    Real.exp (q * a) - q * Real.exp a + q - 1 = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    have := exp_tangent_gap_pos hq ha
    linarith
  · rintro rfl
    simp

end OptimalAffinityRealizability
