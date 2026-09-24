import proofs.CoreCouplingCAC.Source

namespace CoreCouplingCAC

theorem signed_young (a m x y : ℝ) (hm : 0 ≤ m) (ha : |a| ≤ m) :
    2*a*x*y ≤ m*(x^2+y^2) := by
  obtain ⟨hal,hau⟩ := abs_le.mp ha
  by_cases hxy : 0 ≤ x*y
  · have h₁ := mul_nonneg (sub_nonneg.mpr hau) hxy
    have h₂ := mul_nonneg hm (sq_nonneg (x-y))
    nlinarith
  · have h₁ := mul_nonneg (sub_nonneg.mpr hal) (neg_nonneg.mpr (le_of_not_ge hxy))
    have h₂ := mul_nonneg hm (sq_nonneg (x+y))
    nlinarith

/-- A finite-dimensional diagonal Lyapunov estimate from a Metzler comparison.
It applies to a full Jacobian or to an exact secant matrix, not to a
stationary Schur complement. -/
theorem comparison_energy_bound {n : ℕ}
    (J M : Fin n → Fin n → ℝ) (L R y : Fin n → ℝ) (κ : ℝ)
    (hL : ∀ i, 0 < L i) (hR : ∀ i, 0 < R i)
    (hdiag : ∀ i, J i i ≤ M i i)
    (hoff : ∀ i j, i ≠ j → |J i j| ≤ M i j)
    (hrow : ∀ i, L i*(∑ j, M i j*R j)+R i*(∑ j, M j i*L j) ≤
      -κ*(L i*R i)) :
    (∑ i, ∑ j, 2*L i*J i j*R j*y i*y j) ≤
      -κ*(∑ i, L i*R i*(y i)^2) := by
  classical
  have he : ∀ i j, 2*L i*J i j*R j*y i*y j ≤
      L i*M i j*R j*((y i)^2+(y j)^2) := by
    intro i j
    have hlr : 0 ≤ L i*R j := (mul_pos (hL i) (hR j)).le
    by_cases hij : i = j
    · subst j
      have ht := mul_nonneg (sub_nonneg.mpr (hdiag i)) (sq_nonneg (y i))
      have ht' := mul_nonneg hlr ht
      nlinarith
    · have hm : 0 ≤ M i j := (abs_nonneg _).trans (hoff i j hij)
      have ht := mul_le_mul_of_nonneg_left
        (signed_young (J i j) (M i j) (y i) (y j) hm (hoff i j hij)) hlr
      nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => he i j))
  have hid : (∑ i, ∑ j, L i*M i j*R j*((y i)^2+(y j)^2)) =
      ∑ i, (L i*(∑ j, M i j*R j)+R i*(∑ j, M j i*L j))*(y i)^2 := by
    simp only [mul_add,Finset.sum_add_distrib,add_mul,Finset.sum_mul,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hid] at hs
  apply hs.trans
  calc
    (∑ i, (L i*(∑ j, M i j*R j)+R i*(∑ j, M j i*L j))*(y i)^2) ≤
        ∑ i, (-κ*(L i*R i))*(y i)^2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
    _ = -κ*(∑ i, L i*R i*(y i)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end CoreCouplingCAC
