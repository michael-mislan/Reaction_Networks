import proofs.CompositionalMemory.SemenovPolynomialIdentities

namespace CompositionalMemory.Semenov
open Polynomial Matrix

theorem checked_metric_residual_bound (z : Fin 8 → QCoefficients)
    (P : Fin 8 → Fin 8 → QCoefficients) (scale : ℚ) (x : ℝ)
    (hp : ∀ i j,P i j=P j i) (rb : Fin 8 → Fin 8 → ℚ) (L : ℚ)
    (hr : ∀ i j,|aeval x (qpolynomial (metricResidualPolynomial z P scale i j))| ≤ (rb i j : ℝ))
    (hrow : ∀ i,(∑ j,rb i j) ≤ L) (v : Fin 8 → ℝ) :
    matrixEnergy (polynomialMatrixSlope P scale x+
      (polynomialJacobian z x).transpose*polynomialMatrix P x+
      polynomialMatrix P x*polynomialJacobian z x+(1 : Matrix (Fin 8) (Fin 8) ℝ)) v ≤
        (L : ℝ)*vectorSquares v := by
  let R := polynomialMatrixSlope P scale x+
    (polynomialJacobian z x).transpose*polynomialMatrix P x+
    polynomialMatrix P x*polynomialJacobian z x+(1 : Matrix (Fin 8) (Fin 8) ℝ)
  have hs : R.transpose=R := lyapunov_residual_symmetric _ _ _
    (polynomialMatrix_symmetric P hp x) (polynomialMatrixSlope_symmetric P hp scale x)
  have hrs (i : Fin 8) : (∑ j,|R i j|) ≤ (L : ℝ) := by
    calc
      _ ≤ ∑ j,(rb i j : ℝ) := Finset.sum_le_sum (fun j _ => by
        simpa only [metric_residual_identity] using hr i j)
      _ ≤ _ := by exact_mod_cast hrow i
  exact (le_abs_self _).trans (matrix_energy_norm_bound R
    (fun i j => (congrFun (congrFun hs j) i)) (L : ℝ) hrs v)

theorem checked_force_residual_bound (z : Fin 8 → QCoefficients)
    (P : Fin 8 → Fin 8 → QCoefficients) (scale : ℚ) (x : ℝ)
    (fb : Fin 8 → ℚ) (F : ℚ)
    (hf : ∀ i,|aeval x (qpolynomial (forceResidualPolynomial z P scale i))| ≤ (fb i : ℝ))
    (hs : (∑ i,fb i^2) ≤ F^2) :
    vectorSquares ((polynomialMatrix P x).mulVec
      (fieldValue (polynomialVector z x)-polynomialVectorSlope z scale x)) ≤ (F : ℝ)^2 := by
  unfold vectorSquares
  calc
    _ ≤ ∑ i,(fb i : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hf i
      rw [force_residual_identity] at hi
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ ≤ _ := by exact_mod_cast hs

end CompositionalMemory.Semenov
