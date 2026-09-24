import Mathlib

namespace MultiConsumerPermanence
open scoped BigOperators

def total {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i
def squares {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i)^2

theorem total_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ total x := Finset.sum_nonneg (fun i _ => hx i)

theorem squares_bounds {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    squares x ≤ (total x)^2 ∧ (total x)^2 ≤ (n:ℝ)*squares x := by
  constructor
  · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hx i)
  · simpa [total, squares] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))

theorem aggregate_identity {n : ℕ} (x : Fin n → ℝ) (g : ℝ) :
    (∑ i, x i*(g-(n:ℝ)*x i)) = g*total x-(n:ℝ)*squares x := by
  simp only [total, squares, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The common environment cancels exactly from total/individual abundance. -/
theorem ratio_derivative_identity (S Q x g n : ℝ) (hx : x ≠ 0) :
    ((g*S-n*Q)*x-S*(x*(g-n*x)))/x^2 = n*S-n*Q/x := by
  field_simp
  ring

theorem ratio_drift (S Q x g n : ℝ) (hx : 0 < x)
    (hc : S^2 ≤ n*Q) :
    ((g*S-n*Q)*x-S*(x*(g-n*x)))/x^2 ≤ n*S-S*(S/x) := by
  rw [ratio_derivative_identity S Q x g n (ne_of_gt hx)]
  calc
    n*S-n*Q/x ≤ n*S-S^2/x := sub_le_sub_left
      (div_le_div_of_nonneg_right hc hx.le) _
    _ = n*S-S*(S/x) := by ring

end MultiConsumerPermanence
