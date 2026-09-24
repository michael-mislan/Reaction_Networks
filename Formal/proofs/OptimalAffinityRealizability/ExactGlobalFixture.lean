import proofs.OptimalAffinityRealizability.GlobalRealizability

namespace OptimalAffinityRealizability

noncomputable section

/-- Exact noncontrolled drift of the audited two-species source after
reconstructed rates are substituted. -/
def twoByTwoFixtureDrift (x y : ℝ) : ℝ :=
  4 * x ^ 2 * y * (1 - x * y ^ 2)

/-- Exact controlled current of the same source. -/
def twoByTwoFixtureCurrent (x y : ℝ) : ℝ :=
  4 * x ^ 2 * y - 3 * x ^ 3 * y ^ 2

def TwoByTwoFixtureUniqueGlobal : Prop :=
  (∀ x y : ℝ, 0 < x → 0 < y → twoByTwoFixtureDrift x y = 0 →
    twoByTwoFixtureCurrent x y ≤ 1) ∧
  (∀ x y : ℝ, 0 < x → 0 < y → twoByTwoFixtureDrift x y = 0 →
    twoByTwoFixtureCurrent x y = 1 → x = 1 ∧ y = 1)

theorem twoByTwoFixture_stationary_elimination
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hstationary : twoByTwoFixtureDrift x y = 0) :
    x * y ^ 2 = 1 := by
  unfold twoByTwoFixtureDrift at hstationary
  have hprefactor : 4 * x ^ 2 * y ≠ 0 := by positivity
  have hfactor : 1 - x * y ^ 2 = 0 :=
    (mul_eq_zero.mp hstationary).resolve_left hprefactor
  linarith

theorem twoByTwoFixture_current_gap_factorization
    (x y : ℝ) (hy : 0 < y) (hxy : x * y ^ 2 = 1) :
    1 - twoByTwoFixtureCurrent x y =
      (y - 1) ^ 2 * (y ^ 2 + 2 * y + 3) / y ^ 4 := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hx : x = 1 / y ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hy0)).2
    simpa [mul_comm] using hxy
  rw [hx]
  unfold twoByTwoFixtureCurrent
  field_simp [hy0]
  ring

theorem twoByTwoFixture_current_le_one
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hstationary : twoByTwoFixtureDrift x y = 0) :
    twoByTwoFixtureCurrent x y ≤ 1 := by
  have hxy := twoByTwoFixture_stationary_elimination x y hx hy hstationary
  have hgap := twoByTwoFixture_current_gap_factorization x y hy hxy
  have hquad : 0 < y ^ 2 + 2 * y + 3 := by positivity
  have hden : 0 < y ^ 4 := pow_pos hy 4
  have hnonneg : 0 ≤ (y - 1) ^ 2 * (y ^ 2 + 2 * y + 3) / y ^ 4 := by positivity
  linarith

theorem twoByTwoFixture_current_eq_one_unique
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hstationary : twoByTwoFixtureDrift x y = 0)
    (hcurrent : twoByTwoFixtureCurrent x y = 1) :
    x = 1 ∧ y = 1 := by
  have hxy := twoByTwoFixture_stationary_elimination x y hx hy hstationary
  have hgap := twoByTwoFixture_current_gap_factorization x y hy hxy
  have hquad : 0 < y ^ 2 + 2 * y + 3 := by positivity
  have hden : 0 < y ^ 4 := pow_pos hy 4
  have hsquare : (y - 1) ^ 2 = 0 := by
    rw [hcurrent, sub_self] at hgap
    have hproduct : (y - 1) ^ 2 * (y ^ 2 + 2 * y + 3) = 0 :=
      (div_eq_zero_iff.mp hgap.symm).resolve_right (ne_of_gt hden)
    exact (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hquad)
  have hy1 : y = 1 := by nlinarith [sq_nonneg (y - 1)]
  constructor
  · rw [hy1] at hxy
    norm_num at hxy ⊢
    exact hxy
  · exact hy1

/-- The first new exact global witness produced by the root-audit campaign. -/
theorem twoByTwoFixture_uniqueGlobal : TwoByTwoFixtureUniqueGlobal := by
  constructor
  · exact twoByTwoFixture_current_le_one
  · exact twoByTwoFixture_current_eq_one_unique

end
end OptimalAffinityRealizability
