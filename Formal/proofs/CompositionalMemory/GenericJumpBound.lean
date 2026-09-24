import proofs.CompositionalMemory.GenericReactionEnergy

namespace CompositionalMemory

theorem bilinear_scaled_jump_small {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y z : V) (α N P R : ℝ) (hN : 0 < N) (hα : 0 ≤ α)
    (hu : |Q y z| ≤ P) (hv : |Q z z| ≤ R)
    (hsmall : α*(2*P+R/N) ≤ 1) :
    |α*N*(Q (y+(1/N) • z) (y+(1/N) • z)-Q y y)| ≤ 1 := by
  rw [scaled_bilinear_energy_increment Q hQ]
  have hu' : |(2/N)*Q y z| ≤ (2/N)*P := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ (2:ℝ)/N by positivity)]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hv' : |(1/N^2)*Q z z| ≤ (1/N^2)*R := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ (1:ℝ)/N^2 by positivity)]
    exact mul_le_mul_of_nonneg_left hv (by positivity)
  calc
    _ = α*N*|(2/N)*Q y z+(1/N^2)*Q z z| := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg hα hN.le)]
    _ ≤ α*N*((2/N)*P+(1/N^2)*R) := mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add hu' hv')) (mul_nonneg hα hN.le)
    _ = α*(2*P+R/N) := by field_simp
    _ ≤ 1 := hsmall

end CompositionalMemory
