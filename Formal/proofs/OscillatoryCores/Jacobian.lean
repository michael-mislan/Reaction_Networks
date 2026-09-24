import proofs.OscillatoryCores.Linearization
import proofs.OscillatoryCores.QuarticCertificates
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OscillatoryCores

open DUnstableCores
open scoped BigOperators Matrix

noncomputable def normalizedJacobian (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, -398;
      0, -2/25, -1/25, 1/25;
      2/375, -2/125, -251/125, 801/375;
      -t/2, 0, 375*t/2, -201*t]

theorem normalizedLinear_entry (t : ℝ) (i j : Fin 4) :
    normalizedLinear t (Pi.single j 1) i = normalizedJacobian t i j := by
  have he : normalizedLinear t (Pi.single j 1) i =
      ∑ k : Fin 5, normalizedCoefficient t i k * (source.reactant j k : ℝ) := by
    simp [normalizedLinear, monomialLinear, Pi.single_apply]
  rw [he]
  fin_cases i <;> fin_cases j <;>
    norm_num [normalizedCoefficient,
      normalizedJacobian, source, SourceNetwork.stoich, equilibrium, flux,
      Fin.sum_univ_succ, div_div_eq_mul_div, Pi.single_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;> ring

noncomputable def characteristicMatrix (t z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![z+1, 0, 0, 398;
      0, z+2/25, 1/25, -1/25;
      -2/375, 2/125, z+251/125, -801/375;
      t/2, 0, -375*t/2, z+201*t]

theorem characteristicMatrix_eq (t z : ℝ) :
    characteristicMatrix t z = z • (1 : Matrix (Fin 4) (Fin 4) ℝ) -
      normalizedJacobian t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [characteristicMatrix, normalizedJacobian] <;> ring

set_option maxHeartbeats 800000 in
theorem characteristic_determinant (t z : ℝ) :
    (characteristicMatrix t z).det =
      z^4 + a1 t*z^3 + a2 t*z^2 + a3 t*z + a4 t := by
  rw [Matrix.det_succ_row_zero]
  norm_num [characteristicMatrix, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Fin.castSucc, Fin.castAdd, Fin.castLE, a1, a2, a3, a4]
  ring

end OscillatoryCores
