import proofs.CompositionalMemory.GenericReactionVariance

namespace CompositionalMemory

theorem bounded_bilinear_jump_square (u v L r d D : ℝ)
    (hd : 0 ≤ d) (hD : d ≤ D)
    (hu : |u| ≤ L*r*d) (hv : |v| ≤ L*d^2) :
    (2*u+v)^2 ≤ (8*L^2*r^2+2*L^2*D^2)*d^2 := by
  have h := scaled_energy_square_bound u v (L*r*d) (L*d^2) 1 (by norm_num) hu hv
  norm_num only [div_one,one_pow,one_mul] at h
  have hsq : d^2 ≤ D^2 := (sq_le_sq₀ hd (hd.trans hD)).mpr hD
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*L^2*d^2 by positivity)
  nlinarith only [h,hm]

/-- Moment bounds for actual quadratic energy increments with varying jump
sizes. This allows shared-volume membrane jumps, not only fixed nu/N jumps. -/
theorem bounded_bilinear_jump_moments {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y : V) (z : ι → V) (rate d : ι → ℝ) (L r D M S : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hrate : ∀ j, 0 ≤ rate j)
    (hd : ∀ j, 0 ≤ d j) (hD : ∀ j, d j ≤ D)
    (hu : ∀ j, |Q y (z j)| ≤ L*r*d j)
    (hv : ∀ j, |Q (z j) (z j)| ≤ L*(d j)^2)
    (hM : ∑ j, rate j*d j ≤ M) (hS : ∑ j, rate j*(d j)^2 ≤ S) :
    (∑ j, rate j*(Q (y+z j) (y+z j)-Q y y)) ≤ 2*L*r*M+L*S ∧
    (∑ j, rate j*(Q (y+z j) (y+z j)-Q y y)^2) ≤
      (8*L^2*r^2+2*L^2*D^2)*S := by
  simp_rw [bilinear_energy_increment Q hQ]
  constructor
  · calc
      _ ≤ ∑ j, rate j*(2*L*r*d j+L*(d j)^2) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hrate j)
        have h1 := (le_abs_self (Q y (z j))).trans (hu j)
        have h2 := (le_abs_self (Q (z j) (z j))).trans (hv j)
        linarith only [h1,h2]
      _ = 2*L*r*(∑ j, rate j*d j)+L*(∑ j, rate j*(d j)^2) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hM (by positivity))
        (mul_le_mul_of_nonneg_left hS hL)
  · calc
      _ ≤ ∑ j, rate j*((8*L^2*r^2+2*L^2*D^2)*(d j)^2) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (bounded_bilinear_jump_square _ _ L r (d j) D (hd j) (hD j) (hu j) (hv j)) (hrate j)
      _ = (8*L^2*r^2+2*L^2*D^2)*(∑ j, rate j*(d j)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (by positivity)

end CompositionalMemory
