import proofs.CompositionalMemory.GenericReactionVariance

namespace CompositionalMemory

theorem dissipative_reaction_energy_moments {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y : V) (ν : ι → V) (a : ι → ℝ) (v lam r A P R F : ℝ)
    (hv : 0 < v) (hR : 0 ≤ R) (ha : ∀ j, 0 ≤ a j) (hA : ∑ j, a j ≤ A)
    (hu : ∀ j, |Q y (ν j)| ≤ P*r) (hq : ∀ j, |Q (ν j) (ν j)| ≤ R)
    (hd : 2*Q y (∑ j, a j • ν j) ≤ -lam*r^2+F*r) :
    (∑ j, v*a j*(Q (y+(1/v) • ν j) (y+(1/v) • ν j)-Q y y)) ≤
      -lam*r^2+F*r+A*R/v ∧
    (∑ j, v*a j*(Q (y+(1/v) • ν j) (y+(1/v) • ν j)-Q y y)^2) ≤
      8*A*P^2*r^2/v+2*A*R^2/v^3 := by
  have hact : ∑ j, a j*Q (ν j) (ν j) ≤ A*R := calc
    _ ≤ ∑ j, a j*R := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hq j)) (ha j)
    _ = (∑ j, a j)*R := (Finset.sum_mul ..).symm
    _ ≤ A*R := mul_le_mul_of_nonneg_right hA hR
  constructor
  · rw [reaction_energy_generator_identity Q hQ y ν a v (ne_of_gt hv)]
    have h := add_le_add hd (mul_le_mul_of_nonneg_left hact (one_div_nonneg.mpr hv.le))
    convert h using 1
    ring
  · have h := reaction_energy_variance_bound Q hQ y ν a v A (P*r) R hv ha hA hu hq
    convert h using 1
    ring

end CompositionalMemory
