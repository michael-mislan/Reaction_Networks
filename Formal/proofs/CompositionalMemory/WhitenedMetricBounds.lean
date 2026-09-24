import proofs.CompositionalMemory.MatrixRecoveryBounds
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace CompositionalMemory
open Matrix

noncomputable def vectorSquares {N : ℕ} (x : Fin N → ℝ) : ℝ := ∑ i,x i^2
noncomputable def frobeniusSquared {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ := ∑ i,∑ j,(A i j)^2

theorem vectorSquares_nonneg {N : ℕ} (x : Fin N → ℝ) : 0 ≤ vectorSquares x := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem frobeniusSquared_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ frobeniusSquared A := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))

theorem lower_triangular_det_ne_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (htri : ∀ i j,i<j → A i j=0) (hdiag : ∀ i,0<A i i) : A.det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular A (fun i j h => htri i j h)]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hdiag i))

theorem frobenius_mulVec_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) :
    vectorSquares (A.mulVec y) ≤ frobeniusSquared A*vectorSquares y := by
  unfold vectorSquares frobeniusSquared Matrix.mulVec dotProduct
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) y)

theorem frobeniusSquared_transpose {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    frobeniusSquared A.transpose=frobeniusSquared A := by
  exact Finset.sum_comm

theorem matrixEnergy_dotProduct {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    matrixEnergy P x=dotProduct x (P.mulVec x) := by
  simp only [matrixEnergy,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixEnergy_congruence {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) :
    matrixEnergy P (A.transpose.mulVec y)=matrixEnergy (A*P*A.transpose) y := by
  simp only [matrixEnergy_dotProduct,← Matrix.mulVec_mulVec]
  rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec]

/-- Quantitative coercivity of a metric from a rationally checked congruence.
No spectral solver or numerical inverse is trusted. -/
theorem whitened_metric_coercivity {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.det ≠ 0) (δ : ℝ) (hδ : 0 ≤ δ)
    (hwhite : ∀ y,δ*vectorSquares y ≤ matrixEnergy (A*P*A.transpose) y) (x : Fin N → ℝ) :
    δ*vectorSquares x ≤ frobeniusSquared A*matrixEnergy P x := by
  let y := A.transpose⁻¹.mulVec x
  have hAt : IsUnit A.transpose.det := isUnit_iff_ne_zero.mpr (by simpa using hA)
  have hy : A.transpose.mulVec y=x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hAt,Matrix.one_mulVec]
  have hn := frobenius_mulVec_bound A.transpose y
  rw [hy,frobeniusSquared_transpose] at hn
  have he := hwhite y
  rw [← matrixEnergy_congruence,hy] at he
  have h1 := mul_le_mul_of_nonneg_left hn hδ
  have h2 := mul_le_mul_of_nonneg_left he (frobeniusSquared_nonneg A)
  nlinarith only [h1,h2]

theorem whitened_metric_radius {N : ℕ} (P A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.det ≠ 0) (δ eta radius : ℝ) (hδ : 0<δ)
    (hwhite : ∀ y,δ*vectorSquares y ≤ matrixEnergy (A*P*A.transpose) y)
    (heta : eta*frobeniusSquared A ≤ δ*radius^2) (x : Fin N → ℝ)
    (hx : matrixEnergy P x ≤ eta) : vectorSquares x ≤ radius^2 := by
  have h1 := whitened_metric_coercivity P A hA δ hδ.le hwhite x
  have h2 := mul_le_mul_of_nonneg_left hx (frobeniusSquared_nonneg A)
  have hh : δ*vectorSquares x ≤ δ*radius^2 := h1.trans (h2.trans (by nlinarith only [heta]))
  exact (mul_le_mul_iff_right₀ hδ).mp hh

end CompositionalMemory
