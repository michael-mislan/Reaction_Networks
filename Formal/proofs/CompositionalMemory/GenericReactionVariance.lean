import proofs.CompositionalMemory.GenericReactionEnergy

namespace CompositionalMemory

theorem scaled_energy_square_bound (u v P R N : ℝ)
    (hN : 0 < N) (hu : |u| ≤ P) (hv : |v| ≤ R) :
    N*((2/N)*u+(1/N^2)*v)^2 ≤ 8*P^2/N+2*R^2/N^3 := by
  have hu2 : u^2 ≤ P^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) (le_trans (abs_nonneg u) hu)).mpr hu
  have hv2 : v^2 ≤ R^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg v) (le_trans (abs_nonneg v) hv)).mpr hv
  have hsum : (2*N*u+v)^2 ≤ 8*N^2*P^2+2*R^2 := by
    have h := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ 8*N^2 by positivity)
    nlinarith only [h,hv2,sq_nonneg (2*N*u-v)]
  convert div_le_div_of_nonneg_right hsum (show 0 ≤ N^3 by positivity) using 1 <;>
    field_simp

theorem reaction_energy_variance_bound {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y : V) (ν : ι → V) (a : ι → ℝ) (N A P R : ℝ)
    (hN : 0 < N) (ha : ∀ j, 0 ≤ a j) (hA : ∑ j, a j ≤ A)
    (hu : ∀ j, |Q y (ν j)| ≤ P) (hv : ∀ j, |Q (ν j) (ν j)| ≤ R) :
    (∑ j, N*a j*(Q (y+(1/N) • ν j) (y+(1/N) • ν j)-Q y y)^2) ≤
      8*A*P^2/N+2*A*R^2/N^3 := by
  simp_rw [scaled_bilinear_energy_increment Q hQ]
  calc
    _ ≤ ∑ j, a j*(8*P^2/N+2*R^2/N^3) := by
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left
        (scaled_energy_square_bound _ _ P R N hN (hu j) (hv j)) (ha j)
      nlinarith only [h]
    _ = (∑ j, a j)*(8*P^2/N+2*R^2/N^3) := (Finset.sum_mul ..).symm
    _ ≤ A*(8*P^2/N+2*R^2/N^3) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end CompositionalMemory
