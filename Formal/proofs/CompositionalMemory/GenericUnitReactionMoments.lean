import proofs.CompositionalMemory.GenericReactionVariance

namespace CompositionalMemory

theorem unit_reaction_energy_moments {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y : V) (ν : ι → V) (a : ι → ℝ) (N A L r : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (ha : ∀ j, 0 ≤ a j) (hA : ∑ j, a j ≤ A)
    (hop : ∀ v w, |Q v w| ≤ L*‖v‖*‖w‖)
    (hy : ‖y‖ ≤ r) (hν : ∀ j, ‖ν j‖ ≤ 1) :
    (∑ j, N*a j*(Q (y+(1/N) • ν j) (y+(1/N) • ν j)-Q y y)) ≤
      2*L*r*A+L*A/N ∧
    (∑ j, N*a j*(Q (y+(1/N) • ν j) (y+(1/N) • ν j)-Q y y)^2) ≤
      8*A*L^2*r^2/N+2*A*L^2/N^3 := by
  have hu (j) : |Q y (ν j)| ≤ L*r := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hy hL) (hν j)
      (norm_nonneg _) (mul_nonneg hL hr)
    exact (hop _ _).trans (by simpa only [mul_one] using h)
  have hv (j) : |Q (ν j) (ν j)| ≤ L := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left (hν j) hL) (hν j)
      (norm_nonneg _) (by simpa only [mul_one] using hL)
    exact (hop _ _).trans (by simpa only [mul_one] using h)
  have hsum (f : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ j, f j ≤ B) :
      ∑ j, a j*f j ≤ A*B := calc
    _ ≤ ∑ j, a j*B := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf j) (ha j)
    _ = (∑ j, a j)*B := (Finset.sum_mul ..).symm
    _ ≤ A*B := mul_le_mul_of_nonneg_right hA hB
  constructor
  · rw [reaction_energy_generator_identity Q hQ y ν a N (ne_of_gt hN)]
    simp only [map_sum,map_smul,smul_eq_mul]
    have h := add_le_add
      (mul_le_mul_of_nonneg_left (hsum _ (L*r) (mul_nonneg hL hr)
        (fun j => (le_abs_self _).trans (hu j))) (show (0:ℝ) ≤ 2 by norm_num))
      (mul_le_mul_of_nonneg_left (hsum _ L hL
        (fun j => (le_abs_self _).trans (hv j))) (one_div_nonneg.mpr hN.le))
    convert h using 1
    ring
  · have h := reaction_energy_variance_bound Q hQ y ν a N A (L*r) L hN ha hA hu hv
    convert h using 1
    ring

end CompositionalMemory
