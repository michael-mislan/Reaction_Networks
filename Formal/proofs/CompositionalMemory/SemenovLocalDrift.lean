import proofs.CompositionalMemory.SemenovQuadraticDrift

namespace CompositionalMemory.Semenov
open Matrix

/-- All nominal chemical and CSTR channels are included. The only remaining
local numerical premises are the two polynomial residual enclosures. -/
theorem checked_quadratic_drift
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H) (hL : 0 < L)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (P Pd : Matrix (Fin 8) (Fin 8) ℝ)
    (z zd n : Fin 8 → ℝ) (volume F : ℝ) (hv : 0 < volume)
    (hP : P=coefficientMatrix pc t) (hz : z=(fun j => coefficientValue (zc j) t))
    (hsym : ∀ i j,P i j=P j i)
    (hwhite : coefficientMatrix wc t=rationalMatrix A*P*(rationalMatrix A).transpose)
    (hn : ∀ j,0 ≤ n j) (henergy : matrixEnergy P (n-z) ≤ (eta : ℝ))
    (hres : matrixEnergy (Pd+(nominalJacobian z).transpose*P+P*nominalJacobian z+
      (1 : Matrix (Fin 8) (Fin 8) ℝ)) (n-z) ≤ (1/1000 : ℝ)*vectorSquares (n-z))
    (hforce : vectorSquares (P.mulVec (fieldValue z-zd)) ≤ F^2) :
    rawQuadraticDrift P Pd z zd n volume (eta : ℝ) ≤
      (-matrixEnergy P (n-z)/(2*(L : ℝ))+(Q : ℝ)/volume+100*F^2)/(eta : ℝ) := by
  subst P
  subst z
  let z0 : Fin 8 → ℝ := fun j => coefficientValue (zc j) t
  have heta : (0 : ℝ) < eta := by exact_mod_cast hg.1.1
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hws := coefficient_congruence_symmetric pc wc A t hwhite hsym
  have hx := geometry_tube_radius zc pc wc A nr eta radius margin L Q H hg t hl hu hwhite hws (n-z0) henergy
  have hmetric := geometry_metric_bounds zc pc wc A nr eta radius margin L Q H hg t hl hu hwhite hsym (n-z0)
  have hcurv := field_remainder_work_bound zc pc wc A nr eta radius margin L Q H hg t hl hu (n-z0) hx
  have hnoise := metric_noise_bound zc pc wc A nr eta radius margin L Q H hg t hl hu n hn hx
  have hy := young_force_bound (n-z0) ((coefficientMatrix pc t).mulVec (fieldValue z0-zd))
  have hf : 2*(∑ i,(n-z0) i*((coefficientMatrix pc t).mulVec (fieldValue z0-zd)) i) ≤
      (1/100 : ℝ)*vectorSquares (n-z0)+100*F^2 :=
    hy.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hforce (by norm_num)))
  have hid := raw_quadratic_numerator_identity pc t Pd z0 zd n volume (ne_of_gt hv) hsym
  have hs : rawQuadraticDrift (coefficientMatrix pc t) Pd z0 zd n volume (eta : ℝ)*(eta : ℝ)=
      rawQuadraticNumerator (coefficientMatrix pc t) Pd z0 zd n volume :=
    div_mul_cancel₀ _ (ne_of_gt heta)
  exact recovery_drift_arithmetic _ _ _
    (∑ r,2*(∑ i,(n-z0) i*((coefficientMatrix pc t).mulVec (fun j => (stoich r j : ℝ))) i)*chemicalQuadratic (n-z0) r)
    (2*(∑ i,(n-z0) i*((coefficientMatrix pc t).mulVec (fieldValue z0-zd)) i)) _
    (eta : ℝ) (L : ℝ) volume F (Q : ℝ) _
    heta hL' hv (vectorSquares_nonneg (n-z0)) hmetric.2 (by rw [hs,hid]; ring) hres hcurv hf hnoise

end CompositionalMemory.Semenov
