import Mathlib

namespace DisguisedToricAssemblies

/-- Dividing a balanced flux by the positive source activity reconstructs rates. -/
theorem reconstruct_rates {I S : Type*} [Fintype I]
    (y : I → S → ℝ) (b : I → S → ℝ) (m : I → ℝ) (q : I → I → ℝ)
    (hm : ∀ i, 0 < m i) (hq : ∀ i j, 0 ≤ q i j)
    (hb : ∀ i, ∑ j, q i j = ∑ j, q j i)
    (hd : ∀ i k, ∑ j, q i j * (y j k-y i k) = m i*b i k) :
    (∀ i j, 0 ≤ q i j / m i) ∧
    (∀ i j, 0 < q i j / m i ↔ 0 < q i j) ∧
    (∀ i, ∑ j, (q i j / m i)*m i = ∑ j, (q j i / m j)*m j) ∧
    (∀ i k, ∑ j, (q i j / m i)*(y j k-y i k) = b i k) := by
  refine ⟨fun i j => div_nonneg (hq i j) (hm i).le, ?_, ?_, ?_⟩
  · intro i j
    exact div_pos_iff_of_pos_right (hm i)
  · intro i
    simpa only [div_mul_cancel₀ _ (ne_of_gt (hm _))] using hb i
  · intro i k
    calc
      ∑ j, (q i j / m i)*(y j k-y i k) =
          (∑ j, q i j*(y j k-y i k))/m i := by
        simp only [div_mul_eq_mul_div, Finset.sum_div]
      _ = b i k := by rw [hd]; exact mul_div_cancel_left₀ _ (ne_of_gt (hm i))

end DisguisedToricAssemblies
