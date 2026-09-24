import Mathlib

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

def variance {n : ℕ} (q y : Fin n → ℝ) : ℝ := ∑ i, q i*(y i)^2

def deviationField {n : ℕ} (q y : Fin n → ℝ) (a : ℝ) (i : Fin n) : ℝ :=
  a*y i-(y i)^2+variance q y

theorem variance_nonnegative {n : ℕ} (q y : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    0 ≤ variance q y :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hq i) (sq_nonneg _))

theorem variance_rate {n : ℕ} (q y : Fin n → ℝ) (a : ℝ)
    (hmean : ∑ i, q i*y i = 0) :
    (∑ i, 2*q i*y i*deviationField q y a i) =
      2*a*variance q y-2*∑ i, q i*(y i)^3 := by
  have he : ∀ i, 2*q i*y i*deviationField q y a i =
      2*a*(q i*(y i)^2)-2*(q i*(y i)^3)+2*variance q y*(q i*y i) := by
    intro i; unfold deviationField; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hmean]
  simp [variance]

theorem variance_rate_bound {n : ℕ} (q y : Fin n → ℝ) (a e : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hmean : ∑ i, q i*y i = 0)
    (hy : ∀ i, -e ≤ y i) :
    (∑ i, 2*q i*y i*deviationField q y a i) ≤ 2*(a+e)*variance q y := by
  rw [variance_rate q y a hmean]
  have hterm : ∀ i, -e*(q i*(y i)^2) ≤ q i*(y i)^3 := by
    intro i
    have h := mul_nonneg (hq i) (mul_nonneg (by linarith [hy i] : 0 ≤ y i+e)
      (sq_nonneg (y i)))
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  rw [← Finset.mul_sum] at hsum
  change -e*variance q y ≤ _ at hsum
  nlinarith

/-- Exact aggregate drift: composition variance is the only correction. -/
theorem total_consumer_drift {n : ℕ} (q y : Fin n → ℝ) (g s : ℝ)
    (hq : ∑ i, q i = 1) (hmean : ∑ i, q i*y i = 0) :
    (∑ i, q i*(s+y i)*(g-s-y i)) = s*(g-s)-variance q y := by
  have he : ∀ i, q i*(s+y i)*(g-s-y i) =
      s*(g-s)*q i+(g-2*s)*(q i*y i)-q i*(y i)^2 := by intro i; ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,hq,hmean]
  simp [variance]

theorem deviation_identity {n : ℕ} (q y : Fin n → ℝ) (g s : ℝ) (i : Fin n) :
    (s+y i)*(g-s-y i)-(s*(g-s)-variance q y) =
      deviationField q y (g-2*s) i := by
  unfold deviationField
  ring

end
end RAF1519.Reservoir
