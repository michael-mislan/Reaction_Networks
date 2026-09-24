import proofs.OptimalAffinity.Steady

namespace OptimalAffinity

def IsUniqueGlobalMaximum (N : Network) (xStar yStar : ℝ) : Prop :=
  0 < xStar ∧ 0 < yStar ∧ YSteady N xStar yStar ∧
  (∀ x y : ℝ, 0 < x → 0 < y → YSteady N x y →
    productionCurrent N x y ≤ productionCurrent N xStar yStar) ∧
  (∀ x y : ℝ, 0 < x → 0 < y → YSteady N x y →
    productionCurrent N x y = productionCurrent N xStar yStar →
    x = xStar ∧ y = yStar)

theorem oa2x2_polynomialCertificate (x y : ℝ) :
    12 * (3 * x - 2 * y - 7 * y ^ 2 + 6 * x ^ 2 * y) =
      (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) +
      (3 * x - 2 * y - 1) *
        (4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12) := by
  ring

theorem oa2x2_current_le_one
    (x y : ℝ) (hy : 0 < y) (hsteady : YSteady oa2x2 x y) :
    productionCurrent oa2x2 x y ≤ 1 := by
  rw [oa2x2_current_formula]
  have hsteady' := (oa2x2_ySteady_iff x y).mp hsteady
  have hzero : 3 * x - 2 * y - 7 * y ^ 2 + 6 * x ^ 2 * y = 0 := by
    linarith
  have hcert := oa2x2_polynomialCertificate x y
  have hrhs :
      (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) +
      (3 * x - 2 * y - 1) *
        (4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12) = 0 := by
    nlinarith
  by_contra hle
  have hJ : 1 < 3 * x - 2 * y := lt_of_not_ge hle
  have hs : 0 < 2 * y := by linarith
  have hlinear : 0 < 3 * x - 2 * y + 1 := by linarith
  have hfirst : 0 ≤ (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) := by
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have hinner :
      0 < 4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12 := by
    have hprod : 0 < 4 * (2 * y) * (3 * x - 2 * y + 1) := by positivity
    nlinarith [sq_nonneg (2 * y)]
  have hsecond :
      0 < (3 * x - 2 * y - 1) *
        (4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12) := by
    exact mul_pos (by linarith) hinner
  nlinarith

theorem oa2x2_current_eq_one_iff
    (x y : ℝ) (hy : 0 < y) (hsteady : YSteady oa2x2 x y) :
    productionCurrent oa2x2 x y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro hJ
    rw [oa2x2_current_formula] at hJ
    have hsteady' := (oa2x2_ySteady_iff x y).mp hsteady
    have hzero : 3 * x - 2 * y - 7 * y ^ 2 + 6 * x ^ 2 * y = 0 := by
      linarith
    have hcert := oa2x2_polynomialCertificate x y
    have hJzero : 3 * x - 2 * y - 1 = 0 := by linarith
    have hfirstzero : (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) = 0 := by
      rw [hzero, hJzero] at hcert
      norm_num only [mul_zero, zero_mul, add_zero] at hcert
      exact hcert.symm
    have hfactor : 4 * (2 * y) + 3 ≠ 0 := ne_of_gt (by linarith)
    have hsquare : (2 * y - 2) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hfirstzero with hsquare | hbad
      · exact hsquare
      · exact (hfactor hbad).elim
    have hy1 : y = 1 := by nlinarith [sq_nonneg (2 * y - 2)]
    constructor
    · nlinarith
    · exact hy1
  · rintro ⟨rfl, rfl⟩
    exact oa2x2_one_one_current

theorem oa2x2_uniqueGlobalMaximum : IsUniqueGlobalMaximum oa2x2 1 1 := by
  refine ⟨by norm_num, by norm_num, oa2x2_one_one_steady, ?_, ?_⟩
  · intro x y hx hy hsteady
    rw [oa2x2_one_one_current]
    exact oa2x2_current_le_one x y hy hsteady
  · intro x y hx hy hsteady heq
    rw [oa2x2_one_one_current] at heq
    exact (oa2x2_current_eq_one_iff x y hy hsteady).mp heq

end OptimalAffinity
