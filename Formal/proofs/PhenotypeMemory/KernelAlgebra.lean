import Mathlib

namespace PhenotypeMemory
open Finset

variable {S : Type*} [Fintype S]

theorem pair_recovery_normalized (G : S → S → ℝ)
    (hG : ∀ u, ∑ y, G u y = 1) (u v : S) :
    ∑ y, ∑ z, G u y * G v z = 1 := by
  simp_rw [← Finset.mul_sum, hG, mul_one]
  exact hG u

/-- Apply this on the product type to compose the actual joint partition
with independent conditional recovery, including absorbing outcomes. -/
theorem composition_normalized (D : S → ℝ) (G : S → S → ℝ)
    (hD : ∑ u, D u = 1) (hG : ∀ u, ∑ y, G u y = 1) :
    ∑ y, ∑ u, D u*G u y = 1 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hG, mul_one]
  exact hD

noncomputable def retention (K : S → S → ℝ) : ℕ → S → ℝ
  | 0, _ => 1
  | n+1, x => ∑ y, K x y * retention K n y

theorem retention_bounds (K : S → S → ℝ) (l u : ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hrow : ∀ x, l ≤ ∑ y, K x y ∧ ∑ y, K x y ≤ u) :
    ∀ n x, l^n ≤ retention K n x ∧ retention K n x ≤ u^n := by
  intro n
  induction n with
  | zero => intro x; simp [retention]
  | succ n ih =>
    intro x
    constructor
    · calc
        l^(n+1) = l*l^n := by ring
        _ ≤ (∑ y, K x y)*l^n := mul_le_mul_of_nonneg_right (hrow x).1 (pow_nonneg hl _)
        _ = ∑ y, K x y*l^n := Finset.sum_mul _ _ _
        _ ≤ retention K (n+1) x := by
          apply Finset.sum_le_sum
          intro y _
          exact mul_le_mul_of_nonneg_left (ih y).1 (hK x y)
    · calc
        retention K (n+1) x ≤ ∑ y, K x y*u^n := by
          apply Finset.sum_le_sum
          intro y _
          exact mul_le_mul_of_nonneg_left (ih y).2 (hK x y)
        _ = (∑ y, K x y)*u^n := (Finset.sum_mul _ _ _).symm
        _ ≤ u*u^n := mul_le_mul_of_nonneg_right (hrow x).2 (pow_nonneg hu _)
        _ = u^(n+1) := by ring

theorem finite_error_budget {I : Type*} [Fintype I] (errors counts : I → ℝ)
    (eta : ℝ) (h : ∀ i, errors i ≤ eta*counts i) :
    ∑ i, errors i ≤ eta*∑ i, counts i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => h i

end PhenotypeMemory
