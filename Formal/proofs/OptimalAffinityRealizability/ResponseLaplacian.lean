import proofs.OptimalAffinityRealizability.FlowReconstruction

namespace OptimalAffinityRealizability

open Matrix
noncomputable section

def responseLaplacian {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal q - T.transpose

theorem responseLaplacian_mul_profile_eq_zero {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (q f h : Fin n → ℝ)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i) :
    (responseLaplacian T q).mulVec f = 0 := by
  funext i
  simp [responseLaplacian, Matrix.sub_mulVec, Matrix.mulVec_diagonal,
    hresponse, hratio i]

def literalCurrentJacobian {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (reconstructedForwardFlow J g q) * source.reactant.transpose -
  Matrix.diagonal (reconstructedReverseFlow J g q) * source.product.transpose

def factoredCurrentJacobian {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (reconstructedReverseFlow J g q) *
    responseLaplacian (responseMatrix source) q * source.reactant.transpose

theorem responseMatrix_transpose_mul_reactantTranspose {n : ℕ}
    (source : SquareSource n) :
    (responseMatrix source).transpose * source.reactant.transpose =
      source.product.transpose := by
  letI : Invertible source.reactant :=
    Matrix.invertibleOfIsUnitDet source.reactant source.reactant_det_isUnit
  unfold responseMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]

theorem diagonal_reconstructedForward_eq_reverse_mul_q {n : ℕ}
    (J : ℝ) (g q : Fin n → ℝ) (hq : ∀ i, 1 < q i) :
    Matrix.diagonal (reconstructedForwardFlow J g q) =
      Matrix.diagonal (reconstructedReverseFlow J g q) * Matrix.diagonal q := by
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  unfold reconstructedForwardFlow reconstructedReverseFlow
  unfold OptimalAffinityCorrected.reconstructedForwardFlux
    OptimalAffinityCorrected.reconstructedReverseFlux
  field_simp [ne_of_gt (sub_pos.mpr (hq i))]

theorem currentJacobian_factor_responseLaplacian {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (hq : ∀ i, 1 < q i) :
    literalCurrentJacobian source J g q = factoredCurrentJacobian source J g q := by
  rw [literalCurrentJacobian, factoredCurrentJacobian]
  rw [diagonal_reconstructedForward_eq_reverse_mul_q J g q hq]
  rw [responseLaplacian]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc,
    responseMatrix_transpose_mul_reactantTranspose source]

end
end OptimalAffinityRealizability
