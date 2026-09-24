import Mathlib

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

theorem positive_part_monotone_product (x y : ℝ) :
    0 ≤ (max 0 x-max 0 y)*(x-y) := by
  rcases le_total x y with h|h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (max_le_max le_rfl h))
      (sub_nonpos.mpr h)
  · exact mul_nonneg (sub_nonneg.mpr (max_le_max le_rfl h)) (sub_nonneg.mpr h)

theorem symmetric_graph_pairing {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hsym : ∀ i j, k i j = k j i) (p x : ι → ℝ) :
    2*(∑ i, ∑ j, k i j*p i*(x j-x i)) =
      -(∑ i, ∑ j, k i j*(p i-p j)*(x i-x j)) := by
  have hr : (∑ i, ∑ j, k i j*p j*(x i-x j)) =
      ∑ i, ∑ j, k i j*p i*(x j-x i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  calc
    _ = (∑ i, ∑ j, k i j*p i*(x j-x i))+
        (∑ i, ∑ j, k i j*p j*(x i-x j)) := by rw [hr]; ring
    _ = ∑ i, ∑ j, (k i j*p i*(x j-x i)+k i j*p j*(x i-x j)) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Symmetric diffusion cannot increase squared positive-part barrier energy. -/
theorem graph_positive_part_dissipation {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j = k j i) (x : ι → ℝ) :
    2*(∑ i, max 0 (x i)*(∑ j, k i j*(x j-x i))) ≤ 0 := by
  have he : (∑ i, max 0 (x i)*(∑ j, k i j*(x j-x i))) =
      ∑ i, ∑ j, k i j*max 0 (x i)*(x j-x i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,symmetric_graph_pairing k hsym]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  rw [mul_assoc]
  exact mul_nonneg (hk i j) (positive_part_monotone_product (x i) (x j))

end
end RAF1519.Refinement
