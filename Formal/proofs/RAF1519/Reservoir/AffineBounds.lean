import proofs.CoreCouplingCAC.ComparisonEnergy

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

def affine {n : ℕ} (c x : Fin n → ℝ) : ℝ := ∑ k, c k*x k
def affineLower {n : ℕ} (c l u : Fin n → ℝ) : ℝ :=
  ∑ k, if 0 ≤ c k then c k*l k else c k*u k
def affineUpper {n : ℕ} (c l u : Fin n → ℝ) : ℝ :=
  ∑ k, if 0 ≤ c k then c k*u k else c k*l k

theorem affine_bounds {n : ℕ} (c l u x : Fin n → ℝ)
    (hx : ∀ k, l k ≤ x k ∧ x k ≤ u k) :
    affineLower c l u ≤ affine c x ∧ affine c x ≤ affineUpper c l u := by
  constructor
  · apply Finset.sum_le_sum
    intro k _
    by_cases hc : 0 ≤ c k
    · simp only [if_pos hc]
      exact mul_le_mul_of_nonneg_left (hx k).1 hc
    · simp only [if_neg hc]
      exact mul_le_mul_of_nonpos_left (hx k).2 (le_of_not_ge hc)
  · apply Finset.sum_le_sum
    intro k _
    by_cases hc : 0 ≤ c k
    · simp only [if_pos hc]
      exact mul_le_mul_of_nonneg_left (hx k).2 hc
    · simp only [if_neg hc]
      exact mul_le_mul_of_nonpos_left (hx k).1 (le_of_not_ge hc)

def quadratic {n : ℕ} (Q : Fin n → Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, Q i j*y i*y j

/-- Row and column bounds retain the signed diagonal; no absolute-value
comparison is applied to the original source Jacobian. -/
theorem quadratic_lower {n : ℕ} (Q M : Fin n → Fin n → ℝ) (y : Fin n → ℝ)
    (hd : ∀ i, -Q i i ≤ M i i)
    (hoff : ∀ i j, i ≠ j → |Q i j| ≤ M i j)
    (hrow : ∀ i, (∑ j, M i j)+(∑ j, M j i) ≤ -1) :
    (1/2:ℝ)*(∑ i, (y i)^2) ≤ quadratic Q y := by
  have h := CoreCouplingCAC.comparison_energy_bound (fun i j => -Q i j) M
    (fun _ => 1) (fun _ => 1) y 1 (fun _ => by norm_num)
    (fun _ => by norm_num) hd (fun i j hij => by simpa using hoff i j hij)
    (fun i => by simpa using hrow i)
  have he : (∑ i, ∑ j, 2*(1:ℝ)*(-Q i j)*1*y i*y j) = -2*quadratic Q y := by
    unfold quadratic
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  simp only [one_mul,mul_one] at h
  linarith

end
end RAF1519.Reservoir
