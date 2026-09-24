import proofs.CompositionalMemory.SemenovPolynomialTransport
import proofs.CompositionalMemory.SemenovMetricEnclosure

namespace CompositionalMemory.Semenov
open Polynomial Matrix

noncomputable def polynomialVector (z : Fin 8 → QCoefficients) (x : ℝ) : Fin 8 → ℝ :=
  fun j => aeval x (qpolynomial (z j))

noncomputable def polynomialMatrix (P : Fin 8 → Fin 8 → QCoefficients) (x : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => aeval x (qpolynomial (P i j))

noncomputable def polynomialVectorSlope (z : Fin 8 → QCoefficients) (scale : ℚ) (x : ℝ) : Fin 8 → ℝ :=
  fun j => (scale : ℝ)*aeval x (qpolynomial (qderivative (z j)))

noncomputable def polynomialMatrixSlope (P : Fin 8 → Fin 8 → QCoefficients) (scale : ℚ) (x : ℝ) :
    Matrix (Fin 8) (Fin 8) ℝ := fun i j => (scale : ℝ)*aeval x (qpolynomial (qderivative (P i j)))

noncomputable def polynomialJacobian (z : Fin 8 → QCoefficients) (x : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  jacobianValue (polynomialVector z x)

theorem polynomialMatrix_coefficients (pc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (P : Fin 8 → Fin 8 → QCoefficients) (hP : ∀ i j,P i j=qchebyshevSeries (pc i j)) (x : ℝ) :
    polynomialMatrix P x=coefficientMatrix pc x := by
  ext i j
  simp only [polynomialMatrix,hP,qchebyshevSeries_semantics,coefficientMatrix,coefficientValue]

theorem polynomialVector_coefficients (zc : Fin 8 → Fin 17 → ℚ)
    (z : Fin 8 → QCoefficients) (hz : ∀ j,z j=qchebyshevSeries (zc j)) (x : ℝ) :
    polynomialVector z x=(fun j => coefficientValue (zc j) x) := by
  funext j
  simp only [polynomialVector,hz,qchebyshevSeries_semantics,coefficientValue]

theorem force_residual_identity (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (scale : ℚ) (x : ℝ) (i : Fin 8) :
    aeval x (qpolynomial (forceResidualPolynomial z P scale i))=
      (polynomialMatrix P x).mulVec (fieldValue (polynomialVector z x)-polynomialVectorSlope z scale x) i := by
  simp only [forceResidualPolynomial,qpolynomial_qsumFin,qpolynomial_qmul,qpolynomial_qsub,qpolynomial_qscale,
    map_sum,map_mul,map_sub,aeval_C,field_polynomial_value]
  change (∑ j,aeval x (qpolynomial (P i j))*(fieldValue (polynomialVector z x) j-
    (scale : ℝ)*aeval x (qpolynomial (qderivative (z j))))) = _
  rfl

theorem metric_residual_identity (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (scale : ℚ) (x : ℝ) (i j : Fin 8) :
    aeval x (qpolynomial (metricResidualPolynomial z P scale i j))=
      (polynomialMatrixSlope P scale x+(polynomialJacobian z x).transpose*polynomialMatrix P x+
        polynomialMatrix P x*polynomialJacobian z x+(1 : Matrix (Fin 8) (Fin 8) ℝ)) i j := by
  simp only [metricResidualPolynomial,qpolynomial_qadd,qpolynomial_qscale,qpolynomial_qsumFin,qpolynomial_qmul,
    map_add,map_mul,map_sum,aeval_C,jacobian_polynomial_value,qsingleton_value]
  change (scale : ℝ)*aeval x (qpolynomial (qderivative (P i j)))+
    ((∑ l,(jacobianValue (polynomialVector z x) l i*aeval x (qpolynomial (P l j))+
      aeval x (qpolynomial (P i l))*jacobianValue (polynomialVector z x) l j))+
      ((if i=j then 1 else 0 : ℚ) : ℝ)) = _
  simp only [apply_ite,Rat.cast_one,Rat.cast_zero,Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.one_apply,polynomialMatrixSlope,polynomialMatrix,polynomialJacobian,Finset.sum_add_distrib]
  split_ifs <;> ring

theorem polynomialMatrix_symmetric (P : Fin 8 → Fin 8 → QCoefficients)
    (hP : ∀ i j,P i j=P j i) (x : ℝ) : (polynomialMatrix P x).transpose=polynomialMatrix P x := by
  ext i j
  exact congrArg (fun p => aeval x (qpolynomial p)) (hP j i)

theorem polynomialMatrixSlope_symmetric (P : Fin 8 → Fin 8 → QCoefficients)
    (hP : ∀ i j,P i j=P j i) (scale : ℚ) (x : ℝ) :
    (polynomialMatrixSlope P scale x).transpose=polynomialMatrixSlope P scale x := by
  ext i j
  change (scale : ℝ)*aeval x (qpolynomial (qderivative (P j i)))=
    (scale : ℝ)*aeval x (qpolynomial (qderivative (P i j)))
  rw [hP j i]

theorem lyapunov_residual_symmetric {N : ℕ} (P Pd J : Matrix (Fin N) (Fin N) ℝ)
    (hp : P.transpose=P) (hd : Pd.transpose=Pd) :
    (Pd+J.transpose*P+P*J+(1 : Matrix (Fin N) (Fin N) ℝ)).transpose=
      Pd+J.transpose*P+P*J+(1 : Matrix (Fin N) (Fin N) ℝ) := by
  simp only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_one,hp,hd]
  abel

end CompositionalMemory.Semenov
