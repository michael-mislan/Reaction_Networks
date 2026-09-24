import proofs.CompositionalMemory.WhitenedMetricBounds
import proofs.CompositionalMemory.BilinearJumpBounds
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace CompositionalMemory
open Matrix

theorem matrixEnergy_toBilin {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    matrixEnergy P x=P.toBilin' x x := by
  rw [matrixEnergy_dotProduct,Matrix.toBilin'_apply']

theorem matrix_bilinear_symmetric {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsym : ∀ i j,P i j=P j i) (x y : Fin N → ℝ) : P.toBilin' x y=P.toBilin' y x := by
  simp only [Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym j i]
  ring

theorem matrix_bilinear_cauchy {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsym : ∀ i j,P i j=P j i) (hpos : ∀ x,0 ≤ matrixEnergy P x) (x y : Fin N → ℝ) :
    (P.toBilin' x y)^2 ≤ matrixEnergy P x*matrixEnergy P y := by
  simp only [matrixEnergy_toBilin] at hpos ⊢
  exact bilinear_cauchy_sq P.toBilin' (matrix_bilinear_symmetric P hsym) hpos x y

theorem matrix_energy_add {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsym : ∀ i j,P i j=P j i) (x y : Fin N → ℝ) :
    matrixEnergy P (x+y)=matrixEnergy P x+2*P.toBilin' x y+matrixEnergy P y := by
  simp only [matrixEnergy_toBilin]
  have hh := bilinear_energy_increment P.toBilin' (matrix_bilinear_symmetric P hsym) x y
  linarith only [hh]

end CompositionalMemory
