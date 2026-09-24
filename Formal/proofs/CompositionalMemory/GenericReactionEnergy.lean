import Mathlib

namespace CompositionalMemory

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]

theorem bilinear_energy_increment (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ∀ x y, Q x y=Q y x) (y z : V) :
    Q (y+z) (y+z)-Q y y = 2*Q y z+Q z z := by
  simp only [map_add,LinearMap.add_apply]
  rw [hQ z y]
  ring

theorem scaled_bilinear_energy_increment (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ∀ x y, Q x y=Q y x) (y z : V) (N : ℝ) :
    Q (y+(1/N) • z) (y+(1/N) • z)-Q y y =
      (2/N)*Q y z+(1/N^2)*Q z z := by
  rw [bilinear_energy_increment Q hQ]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

/-- Exact finite-reaction identity at real effective volume. The rates and
stoichiometric vectors remain explicit; no stochastic accuracy is assumed. -/
theorem reaction_energy_generator_identity (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ∀ x y, Q x y=Q y x) (y : V) (ν : ι → V) (a : ι → ℝ)
    (N : ℝ) (hN : N ≠ 0) :
    (∑ j, N*a j*(Q (y+(1/N) • ν j) (y+(1/N) • ν j)-Q y y)) =
      2*Q y (∑ j, a j • ν j)+(1/N)*(∑ j, a j*Q (ν j) (ν j)) := by
  simp_rw [scaled_bilinear_energy_increment Q hQ]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

theorem reaction_energy_drift_bound (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ∀ x y, Q x y=Q y x) (y : V) (ν : ι → V) (a : ι → ℝ)
    (N lam r B : ℝ) (hN : 0 < N)
    (hd : 2*Q y (∑ j, a j • ν j) ≤ -lam*r^2)
    (ha : ∑ j, a j*Q (ν j) (ν j) ≤ B) :
    (∑ j, N*a j*(Q (y+(1/N) • ν j) (y+(1/N) • ν j)-Q y y)) ≤
      -lam*r^2+B/N := by
  rw [reaction_energy_generator_identity Q hQ y ν a N (ne_of_gt hN)]
  have h := add_le_add hd (mul_le_mul_of_nonneg_left ha (one_div_nonneg.mpr hN.le))
  convert h using 1
  ring

end CompositionalMemory
