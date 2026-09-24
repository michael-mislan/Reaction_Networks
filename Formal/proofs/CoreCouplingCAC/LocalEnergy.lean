import proofs.CoreCouplingCAC.ComparisonEnergy
import proofs.CoreCouplingCAC.Dynamics

namespace CoreCouplingCAC

noncomputable def energy (L R c x : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, (L i/R i)*(x i-c i)^2
noncomputable def energyRate (p : Rates) (L R c x : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, 2*(L i/R i)*(x i-c i)*dynamics p x i

theorem energy_nonneg (L R c x : Fin 4 → ℝ)
    (hL : ∀ i, 0 < L i) (hR : ∀ i, 0 < R i) : 0 ≤ energy L R c x := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (div_pos (hL i) (hR i)).le (sq_nonneg _)

theorem energy_eq_zero_iff (L R c x : Fin 4 → ℝ)
    (hL : ∀ i, 0 < L i) (hR : ∀ i, 0 < R i) : energy L R c x = 0 ↔ x = c := by
  constructor
  · intro h
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
        mul_nonneg (div_pos (hL i) (hR i)).le (sq_nonneg (x i-c i)))).1 h
    funext i
    have hi := hh i (Finset.mem_univ i)
    have hz : (x i-c i)^2 = 0 :=
      (mul_eq_zero.mp hi).resolve_left (ne_of_gt (div_pos (hL i) (hR i)))
    nlinarith
  · rintro rfl
    simp [energy]

/-- The concrete nonlinear vector field obeys the comparison-energy estimate
whenever its exact midpoint secant is dominated by the certified matrix. -/
theorem nonlinear_energy_bound (p : Rates) (M : Fin 4 → Fin 4 → ℝ)
    (L R c x : Fin 4 → ℝ) (κ : ℝ)
    (hL : ∀ i, 0 < L i) (hR : ∀ i, 0 < R i)
    (hc : dynamics p c = 0)
    (hdiag : ∀ i, jacobian p (fun k => (x k+c k)/2) i i ≤ M i i)
    (hoff : ∀ i j, i ≠ j → |jacobian p (fun k => (x k+c k)/2) i j| ≤ M i j)
    (hrow : ∀ i, L i*(∑ j, M i j*R j)+R i*(∑ j, M j i*L j) ≤
      -κ*(L i*R i)) :
    energyRate p L R c x ≤ -κ*energy L R c x := by
  have h := comparison_energy_bound
    (jacobian p (fun k => (x k+c k)/2)) M L R (fun i => (x i-c i)/R i) κ
    hL hR hdiag hoff hrow
  have hd : ∀ i, dynamics p x i =
      ∑ j : Fin 4, jacobian p (fun k => (x k+c k)/2) i j*(x j-c j) := by
    intro i
    have hs := midpoint_secant p x c i
    simpa [hc] using hs
  have he : energyRate p L R c x =
      ∑ i : Fin 4, ∑ j : Fin 4,
        2*L i*jacobian p (fun k => (x k+c k)/2) i j*R j*((x i-c i)/R i)*((x j-c j)/R j) := by
    unfold energyRate
    apply Finset.sum_congr rfl
    intro i _
    rw [hd,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hi : R i ≠ 0 := ne_of_gt (hR i)
    have hj : R j ≠ 0 := ne_of_gt (hR j)
    field_simp
  rw [he]
  convert h using 1
  congr 1
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  have hi : R i ≠ 0 := ne_of_gt (hR i)
  field_simp

end CoreCouplingCAC
