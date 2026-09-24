import Mathlib

/-! Exact Routh determinant for the explicitly specified two-stage policy.
The analytic Routh-Hurwitz implication is conventional, not asserted here. -/
namespace DynamicSequestration

def inventoryRouth (k theta t1 t2 : ℝ) : ℝ :=
  (t1 + t2 + k * theta * t1 * t2) * (1 + k * theta * t1) - k * t1 * t2

theorem inventory_routh_decomposition (k theta t1 t2 : ℝ) :
    inventoryRouth k theta t1 t2 =
      t1 * (1 + theta * (k*t1)) +
      t2 * ((1 - theta * (k*t1))^2 + (4*theta-1)*(k*t1)) := by
  unfold inventoryRouth
  ring

theorem upstream_quarter_suffices (k theta t1 t2 : ℝ)
    (hk : 0 < k) (htheta : 1/4 ≤ theta) (h1 : 0 < t1) (h2 : 0 < t2) :
    0 < inventoryRouth k theta t1 t2 := by
  rw [inventory_routh_decomposition]
  have hp : 0 ≤ theta := by linarith
  have hkt : 0 < k*t1 := mul_pos hk h1
  have ha : 0 < t1*(1+theta*(k*t1)) :=
    mul_pos h1 (by nlinarith [mul_nonneg hp (le_of_lt hkt)])
  have hb : 0 ≤ (4*theta-1)*(k*t1) := mul_nonneg (by linarith) (le_of_lt hkt)
  have hc : 0 ≤ t2*((1-theta*(k*t1))^2+(4*theta-1)*(k*t1)) :=
    mul_nonneg (le_of_lt h2) (add_nonneg (sq_nonneg _) hb)
  linarith

theorem below_quarter_counterexample (theta : ℝ)
    (hp : 0 < theta) (hq : theta < 1/4) :
    0 < 1/theta ∧ 0 < 4/(1-4*theta) ∧
    inventoryRouth 1 theta (1/theta) (4/(1-4*theta)) = -2/theta := by
  have hd : 0 < 1-4*theta := by linarith
  refine ⟨div_pos (by norm_num) hp, div_pos (by norm_num) hd, ?_⟩
  unfold inventoryRouth
  have ht : theta ≠ 0 := ne_of_gt hp
  have hd' : 1-theta*4 ≠ 0 := by nlinarith
  field_simp [ht, ne_of_gt hd, hd']
  ring

theorem zero_observation_counterexample : inventoryRouth 1 0 2 3 = -1 := by
  norm_num [inventoryRouth]

theorem positive_relaxation_reverse (b c epsilon : ℝ)
    (hc : 0 < c) (he : 0 < epsilon) (hh : epsilon < 1+b/c) :
    0 < (b+c)/epsilon-c := by
  have h : epsilon*c < c+b := (lt_div_iff₀ hc).mp (by
    calc epsilon < 1+b/c := hh
         _ = (c+b)/c := by field_simp)
  apply sub_pos.mpr
  apply (lt_div_iff₀ he).mpr
  nlinarith

end DynamicSequestration
