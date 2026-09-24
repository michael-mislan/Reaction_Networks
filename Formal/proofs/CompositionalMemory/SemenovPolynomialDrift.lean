import proofs.CompositionalMemory.SemenovLocalDrift
import proofs.CompositionalMemory.SemenovResidualBounds

namespace CompositionalMemory.Semenov
open Polynomial Matrix

/-- Polynomial replay supplies both residual premises of the actual local drift.
The only numerical assumptions are explicit finite coefficient checks. -/
theorem checked_polynomial_drift
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H) (hL : 0 < L)
    (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (hz : ∀ j,z j=qchebyshevSeries (zc j)) (hP : ∀ i j,P i j=qchebyshevSeries (pc i j))
    (hsym : ∀ i j,P i j=P j i) (scale F : ℚ)
    (rb : Fin 8 → Fin 8 → ℚ) (fb : Fin 8 → ℚ)
    (hrow : ∀ i,(∑ j,rb i j) ≤ (1/1000 : ℚ)) (hfs : (∑ i,fb i^2) ≤ F^2)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1)
    (hr : ∀ i j,|aeval t (qpolynomial (metricResidualPolynomial z P scale i j))| ≤ (rb i j : ℝ))
    (hf : ∀ i,|aeval t (qpolynomial (forceResidualPolynomial z P scale i))| ≤ (fb i : ℝ))
    (hwhite : coefficientMatrix wc t=rationalMatrix A*coefficientMatrix pc t*(rationalMatrix A).transpose)
    (n : Fin 8 → ℝ) (volume : ℝ) (hv : 0 < volume) (hn : ∀ j,0 ≤ n j)
    (he : matrixEnergy (polynomialMatrix P t) (n-polynomialVector z t) ≤ (eta : ℝ)) :
    rawQuadraticDrift (polynomialMatrix P t) (polynomialMatrixSlope P scale t)
      (polynomialVector z t) (polynomialVectorSlope z scale t) n volume (eta : ℝ) ≤
      (-matrixEnergy (polynomialMatrix P t) (n-polynomialVector z t)/(2*(L : ℝ))+
        (Q : ℝ)/volume+100*(F : ℝ)^2)/(eta : ℝ) := by
  have hp := polynomialMatrix_coefficients pc P hP t
  have hps : ∀ i j,polynomialMatrix P t i j=polynomialMatrix P t j i := by
    intro i j
    exact congrArg (fun p => aeval t (qpolynomial p)) (hsym i j)
  apply checked_quadratic_drift zc pc wc A nr eta radius margin L Q H hg hL t hl hu
    (polynomialMatrix P t) (polynomialMatrixSlope P scale t) (polynomialVector z t)
    (polynomialVectorSlope z scale t) n volume (F : ℝ) hv hp
    (polynomialVector_coefficients zc z hz t) hps (by simpa only [hp] using hwhite) hn he
  · simpa only [nominalJacobian,polynomialJacobian,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      checked_metric_residual_bound z P scale t hsym rb (1/1000) hr hrow (n-polynomialVector z t)
  · exact checked_force_residual_bound z P scale t fb F hf hfs

end CompositionalMemory.Semenov
