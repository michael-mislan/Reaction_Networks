import Mathlib

namespace PowerLawSmallRAF

theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1/2) :
    Real.exp (-2*x) ≤ 1-x := by
  have hp : 0 < 1-x := by linarith
  have hi : (1-x)⁻¹ ≤ 1+2*x := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  exact (Real.le_log_iff_exp_le hp).mp (by linarith)

theorem nucleus_product_lower (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1/2) :
    Real.exp (-2*xs.sum) ≤ (xs.map (fun x => 1-x)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx0 := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [List.sum_cons,List.map_cons,List.prod_cons]
    rw [mul_add,Real.exp_add]
    exact mul_le_mul (exp_neg_two_mul_le_one_sub hx0.1 hx0.2) ht
      (Real.exp_pos _).le (by linarith [hx0.2])

theorem nucleus_product_uniform_lower (xs : List ℝ) (B : ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1/2) (hB : xs.sum ≤ B) :
    0 < Real.exp (-2*B) ∧ Real.exp (-2*B) ≤ (xs.map (fun x => 1-x)).prod := by
  refine ⟨Real.exp_pos _,?_⟩
  exact (Real.exp_le_exp.mpr (by linarith)).trans (nucleus_product_lower xs hx)

end PowerLawSmallRAF
