import proofs.ThermoCoreCompatibility.GeneralCompatibility.ClosedMargin

namespace ThermoCoreCompatibility.GeneralCompatibility

open scoped BigOperators

theorem least_minimizes_monotone {V : Type*} {S : Set (V → ℝ)}
    {x : V → ℝ} (hx : IsLeast S x) {C : (V → ℝ) → ℝ}
    (hC : Monotone C) {y : V → ℝ} (hy : y ∈ S) : C x ≤ C y :=
  hC (hx.2 hy)

theorem least_minimizes_inventory {V : Type*} [Fintype V]
    {S : Set (V → ℝ)} {x : V → ℝ} (hx : IsLeast S x)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) {y : V → ℝ} (hy : y ∈ S) :
    (∑ v, w v * x v) ≤ ∑ v, w v * y v := by
  exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hx.2 hy v) (hw v))

end ThermoCoreCompatibility.GeneralCompatibility
