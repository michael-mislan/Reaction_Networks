import proofs.CompositionalMemory.SemenovSourceSixthTransport
import proofs.CompositionalMemory.SemenovPolynomialDrift

namespace CompositionalMemory.Semenov
open Matrix

theorem checked_sixth_from_quadratic
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1)
    (hw : coefficientMatrix wc t=rationalMatrix A*coefficientMatrix pc t*(rationalMatrix A).transpose)
    (hs : ∀ i j,coefficientValue (pc i j) t=coefficientValue (pc j i) t)
    (Pd : Matrix (Fin 8) (Fin 8) ℝ) (zd n : Fin 8 → ℝ) (volume F root a : ℝ)
    (hv : 0 < volume) (hr : 0 ≤ root) (hn : ∀ j,0 ≤ n j)
    (hroot : (H : ℝ)/(eta : ℝ) ≤ root^2)
    (he : matrixEnergy (coefficientMatrix pc t) (n-(fun j => coefficientValue (zc j) t)) ≤ (eta : ℝ))
    (hfirst : rawQuadraticDrift (coefficientMatrix pc t) Pd (fun j => coefficientValue (zc j) t) zd n volume (eta : ℝ) ≤
      (-matrixEnergy (coefficientMatrix pc t) (n-(fun j => coefficientValue (zc j) t))/(2*(L : ℝ))+
        (Q : ℝ)/volume+100*F^2)/(eta : ℝ))
    (hscalar : ∀ x : ℝ,0 ≤ x → x ≤ 1 →
      6*x^10*(-x^2/(2*(L : ℝ))+(Q : ℝ)/(volume*(eta : ℝ))+100*F^2/(eta : ℝ))+
        sixthRemainderCoefficient (x^2) (root*(2*x/volume+root/volume^2))*
          (volume*((Q : ℝ)/(eta : ℝ))*(2*x/volume+root/volume^2)^2) ≤ a) :
    6*(matrixEnergy (coefficientMatrix pc t) (n-(fun j => coefficientValue (zc j) t))/(eta : ℝ))^5*
      quadraticTimeSlope (coefficientMatrix pc t) Pd (fun j => coefficientValue (zc j) t) zd n (eta : ℝ)+
      (∑ r,volume*channelIntensity n r*
        ((matrixEnergy (coefficientMatrix pc t) (n-(fun j => coefficientValue (zc j) t))/(eta : ℝ)+
          quadraticChannelDelta (coefficientMatrix pc t) (n-(fun j => coefficientValue (zc j) t)) volume (eta : ℝ) r)^6-
         (matrixEnergy (coefficientMatrix pc t) (n-(fun j => coefficientValue (zc j) t))/(eta : ℝ))^6)) ≤ a := by
  let z : Fin 8 → ℝ := fun j => coefficientValue (zc j) t
  let D := matrixEnergy (coefficientMatrix pc t) (n-z)/(eta : ℝ)
  let x := Real.sqrt D
  have heta : (0 : ℝ) < eta := by exact_mod_cast hg.1.1
  have hp (v : Fin 8 → ℝ) := (geometry_metric_bounds zc pc wc A nr eta radius margin L Q H hg t hl hu hw hs v).1
  have hD : 0 ≤ D := div_nonneg (hp _) heta.le
  have hD1 : D ≤ 1 := (div_le_one heta).mpr he
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx1 : x ≤ 1 := Real.sqrt_le_one.mpr hD1
  have hsq : x^2=D := Real.sq_sqrt hD
  have hrad := geometry_tube_radius zc pc wc A nr eta radius margin L Q H hg t hl hu hw
    (coefficient_congruence_symmetric pc wc A t hw hs) (n-z) he
  have hnoise := div_le_div_of_nonneg_right
    (metric_noise_bound zc pc wc A nr eta radius margin L Q H hg t hl hu n hn hrad) heta.le
  have hj (r : Channel) : matrixEnergy (coefficientMatrix pc t) (channelJump r)/(eta : ℝ) ≤ root^2 :=
    (div_le_div_of_nonneg_right (geometry_channel_energy_bound zc pc wc A nr eta radius margin L Q H hg t hl hu r) heta.le).trans hroot
  have hfirst' : rawQuadraticDrift (coefficientMatrix pc t) Pd z zd n volume (eta : ℝ) ≤
      -x^2/(2*(L : ℝ))+(Q : ℝ)/(volume*(eta : ℝ))+100*F^2/(eta : ℝ) := by
    rw [hsq]
    convert hfirst using 1
    dsimp only [D,z]
    ring
  have hh := source_sixth_drift_bound pc t (eta : ℝ) volume x root ((Q : ℝ)/(eta : ℝ)) _ Pd z zd n
    heta hv hx hr hs hp hn hsq.symm hj hnoise hfirst'
  have result := hh.trans (hscalar x hx hx1)
  simpa only [hsq] using result

end CompositionalMemory.Semenov
