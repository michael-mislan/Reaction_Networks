import proofs.CompositionalMemory.GenericPropensityBias

namespace CompositionalMemory

theorem density_drift_bias {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (a idealDensity d : ι → ℝ) (ν : ι → V) (v : ℝ)
    (hbias : ∀ j, |a j-idealDensity j| ≤ d j/v) :
    ‖(∑ j, a j • ν j)-(∑ j, idealDensity j • ν j)‖ ≤ (∑ j, d j*‖ν j‖)/v := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  calc
    _ ≤ ∑ j, ‖(a j-idealDensity j) • ν j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (d j/v)*‖ν j‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbias j) (norm_nonneg _)
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem dissipation_with_density_bias {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (y actual ideal : V) (L r D v lam : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hop : ∀ x z, |Q x z| ≤ L*‖x‖*‖z‖)
    (hy : ‖y‖ ≤ r) (hbias : ‖actual-ideal‖ ≤ D/v)
    (hd : 2*Q y ideal ≤ -lam*r^2) :
    2*Q y actual ≤ -lam*r^2+(2*L*D/v)*r := by
  have hcross := (hop y (actual-ideal)).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hy hL) hbias (norm_nonneg _) (mul_nonneg hL hr))
  have h := (le_abs_self _).trans hcross
  rw [map_sub] at h
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h,hd]

end CompositionalMemory
