import proofs.CompositionalMemory.SemenovRecoveryEndpoints

namespace CompositionalMemory.Semenov.RecoveryPiece
open Matrix Polynomial
variable {high : Bool}

theorem coefficient_symmetry (p : RecoveryPiece high) (t : ℝ) :
    ∀ i j,coefficientValue (p.pc i j) t=coefficientValue (p.pc j i) t := by
  have hp := polynomialMatrix_coefficients p.pc p.P p.cache_P t
  intro i j
  change coefficientMatrix p.pc t i j=coefficientMatrix p.pc t j i
  rw [← hp]
  exact congrArg (fun q => aeval t (qpolynomial q)) (p.symmetry i j)

theorem left_matrix (p : RecoveryPiece high) :
    coefficientMatrix p.pc (-1)=rationalMatrix p.pLeft := by
  rw [← polynomialMatrix_coefficients p.pc p.P p.cache_P]
  simpa only [Rat.cast_neg,Rat.cast_one] using
    polynomial_matrix_endpoint p.P (-1) p.pLeft (fun i j => (p.p_endpoints i j).1)

theorem right_matrix (p : RecoveryPiece high) :
    coefficientMatrix p.pc 1=rationalMatrix p.pRight := by
  rw [← polynomialMatrix_coefficients p.pc p.P p.cache_P]
  simpa only [Rat.cast_one] using
    polynomial_matrix_endpoint p.P 1 p.pRight (fun i j => (p.p_endpoints i j).2)

theorem left_metric_bounds (p : RecoveryPiece high) (v : Fin 8 → ℝ) :
    0 ≤ matrixEnergy (rationalMatrix p.pLeft) v ∧
      matrixEnergy (rationalMatrix p.pLeft) v ≤ (recoveryL high : ℝ)*vectorSquares v := by
  have hh := geometry_metric_bounds p.zc p.pc p.wc p.A p.nr (recoveryEta high)
    p.radius p.margin (recoveryL high) (recoveryQ high) (recoveryH high)
    p.geometry (-1) (by norm_num) (by norm_num) (p.whitened _) (p.coefficient_symmetry _) v
  simpa only [p.left_matrix] using hh

theorem right_metric_bounds (p : RecoveryPiece high) (v : Fin 8 → ℝ) :
    0 ≤ matrixEnergy (rationalMatrix p.pRight) v ∧
      matrixEnergy (rationalMatrix p.pRight) v ≤ (recoveryL high : ℝ)*vectorSquares v := by
  have hh := geometry_metric_bounds p.zc p.pc p.wc p.A p.nr (recoveryEta high)
    p.radius p.margin (recoveryL high) (recoveryQ high) (recoveryH high)
    p.geometry 1 (by norm_num) (by norm_num) (p.whitened _) (p.coefficient_symmetry _) v
  simpa only [p.right_matrix] using hh

theorem right_radius_bound (p : RecoveryPiece high) (v : Fin 8 → ℝ)
    (hv : matrixEnergy (rationalMatrix p.pRight) v ≤ (recoveryEta high : ℝ)) :
    vectorSquares v ≤ (p.radius : ℝ)^2 := by
  apply geometry_tube_radius p.zc p.pc p.wc p.A p.nr (recoveryEta high)
    p.radius p.margin (recoveryL high) (recoveryQ high) (recoveryH high)
    p.geometry 1 (by norm_num) (by norm_num) (p.whitened _)
    (coefficient_congruence_symmetric p.pc p.wc p.A 1 (p.whitened _) (p.coefficient_symmetry _)) v
  simpa only [← p.right_matrix] using hv

end CompositionalMemory.Semenov.RecoveryPiece
