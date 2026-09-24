import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace CompositionalMemory

noncomputable def matrixEnergy {N : ℕ} (M : Fin N → Fin N → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i,∑ j,M i j*x i*x j

private theorem cross_lower (a x y : ℝ) : -|a| * (x^2+y^2) ≤ 2*a*x*y := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    nlinarith only [mul_nonneg ha (sq_nonneg (x+y))]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    nlinarith only [mul_nonneg (show 0 ≤ -a by linarith) (sq_nonneg (x-y))]

theorem matrix_energy_row_lower {N : ℕ} (M : Fin N → Fin N → ℝ)
    (hsym : ∀ i j,M i j=M j i) (x : Fin N → ℝ) :
    -(∑ i,(∑ j,|M i j|)*x i^2) ≤ matrixEnergy M x := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => cross_lower (M i j) (x i) (x j)))
  have hleft : (∑ i,∑ j,|M i j| * x i^2)=∑ i,(∑ j,|M i j|)*x i^2 := by
    simp only [Finset.sum_mul]
  have hright : (∑ i,∑ j,|M i j| * x j^2)=∑ i,(∑ j,|M i j|)*x i^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have he : (∑ i,∑ j,-|M i j| * (x i^2+x j^2))=
      -2*(∑ i,(∑ j,|M i j|)*x i^2) := by
    simp only [neg_mul,mul_add,Finset.sum_neg_distrib,Finset.sum_add_distrib]
    rw [hleft,hright]
    ring
  have hr : (∑ i,∑ j,2*M i j*x i*x j)=2*matrixEnergy M x := by
    simp only [matrixEnergy,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,hr] at hs
  linarith only [hs]

theorem matrix_energy_row_upper {N : ℕ} (M : Fin N → Fin N → ℝ)
    (hsym : ∀ i j,M i j=M j i) (x : Fin N → ℝ) :
    matrixEnergy M x ≤ ∑ i,(∑ j,|M i j|)*x i^2 := by
  have hh := matrix_energy_row_lower (fun i j => -M i j) (fun i j => congrArg Neg.neg (hsym i j)) x
  simp only [abs_neg,matrixEnergy,neg_mul,Finset.sum_neg_distrib] at hh ⊢
  linarith only [hh]

theorem matrix_energy_norm_bound {N : ℕ} (M : Fin N → Fin N → ℝ)
    (hsym : ∀ i j,M i j=M j i) (L : ℝ) (hrow : ∀ i,(∑ j,|M i j|) ≤ L)
    (x : Fin N → ℝ) : |matrixEnergy M x| ≤ L*∑ i,x i^2 := by
  have hs : (∑ i,(∑ j,|M i j|)*x i^2) ≤ L*∑ i,x i^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (x i)))
  exact abs_le.mpr ⟨by linarith only [matrix_energy_row_lower M hsym x,hs],
    (matrix_energy_row_upper M hsym x).trans hs⟩

theorem matrix_energy_diagonal_lower {N : ℕ} (M : Fin N → Fin N → ℝ)
    (hsym : ∀ i j,M i j=M j i) (δ : ℝ)
    (hdiag : ∀ i,δ ≤ M i i-∑ j,if j=i then 0 else |M i j|) (x : Fin N → ℝ) :
    δ*∑ i,x i^2 ≤ matrixEnergy M x := by
  let off : Fin N → Fin N → ℝ := fun i j => if j=i then 0 else M i j
  have hos : ∀ i j,off i j=off j i := by
    intro i j
    by_cases h : i=j
    · subst j; rfl
    · simp [off,h,Ne.symm h,hsym i j]
  have ho := matrix_energy_row_lower off hos x
  have habs (i j : Fin N) : |off i j|=if j=i then 0 else |M i j| := by
    by_cases h : j=i <;> simp [off,h]
  simp_rw [habs] at ho
  have he : matrixEnergy M x=(∑ i,M i i*x i^2)+matrixEnergy off x := by
    simp only [matrixEnergy,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hp (j : Fin N) : M i j*x i*x j=(if j=i then M i i*x i^2 else 0)+off i j*x i*x j := by
      by_cases h : j=i
      · subst j; simp [off]; ring
      · simp [off,h]
    simp_rw [hp]
    simp [Finset.sum_add_distrib]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (x i)))
  simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum] at hh
  rw [he]
  linarith only [hh,ho]

end CompositionalMemory
