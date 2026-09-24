import proofs.CompositionalMemory.SemenovQuadraticDrift
import proofs.CompositionalMemory.SemenovChannelEnergy

namespace CompositionalMemory.Semenov
open Matrix

noncomputable def quadraticTimeSlope (P Pd : Matrix (Fin 8) (Fin 8) ℝ)
    (z zd n : Fin 8 → ℝ) (eta : ℝ) : ℝ :=
  (matrixEnergy Pd (n-z)-2*P.toBilin' (n-z) zd)/eta

noncomputable def quadraticChannelDelta (P : Matrix (Fin 8) (Fin 8) ℝ)
    (v : Fin 8 → ℝ) (volume eta : ℝ) (r : Channel) : ℝ :=
  (matrixEnergy P (v+(1/volume) • channelJump r)-matrixEnergy P v)/eta

theorem raw_quadratic_first_moment (P Pd : Matrix (Fin 8) (Fin 8) ℝ)
    (z zd n : Fin 8 → ℝ) (volume eta : ℝ) :
    quadraticTimeSlope P Pd z zd n eta+
      (∑ r,volume*channelIntensity n r*quadraticChannelDelta P (n-z) volume eta r)=
      rawQuadraticDrift P Pd z zd n volume eta := by
  simp only [quadraticTimeSlope,quadraticChannelDelta,rawQuadraticDrift,rawQuadraticNumerator,
    ← mul_div_assoc,← Finset.sum_div,← add_div]

theorem source_sixth_drift_bound
    (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (t eta volume x h b drift : ℝ)
    (Pd : Matrix (Fin 8) (Fin 8) ℝ) (z zd n : Fin 8 → ℝ)
    (heta : 0 < eta) (hv : 0 < volume) (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hsym : ∀ i j,coefficientValue (pc i j) t=coefficientValue (pc j i) t)
    (hpos : ∀ w,0 ≤ matrixEnergy (coefficientMatrix pc t) w) (hn : ∀ j,0 ≤ n j)
    (he : matrixEnergy (coefficientMatrix pc t) (n-z)/eta=x^2)
    (hjump : ∀ r,matrixEnergy (coefficientMatrix pc t) (channelJump r)/eta ≤ h^2)
    (hnoise : metricNoiseValue pc t n/eta ≤ b)
    (hfirst : rawQuadraticDrift (coefficientMatrix pc t) Pd z zd n volume eta ≤ drift) :
    6*(x^2)^5*quadraticTimeSlope (coefficientMatrix pc t) Pd z zd n eta+
      (∑ r,volume*channelIntensity n r*((x^2+quadraticChannelDelta (coefficientMatrix pc t)
        (n-z) volume eta r)^6-(x^2)^6)) ≤
      6*x^10*drift+sixthRemainderCoefficient (x^2) (h*(2*x/volume+h/volume^2))*
        (volume*b*(2*x/volume+h/volume^2)^2) := by
  have hb := normalized_channel_jump_bounds pc t eta volume x h b (n-z) n
    heta hv hx hh hsym hpos hn he hjump hnoise
  have result := raw_channel_sixth_bound (fun r => volume*channelIntensity n r)
    (quadraticChannelDelta (coefficientMatrix pc t) (n-z) volume eta) (x^2)
    (quadraticTimeSlope (coefficientMatrix pc t) Pd z zd n eta)
    (h*(2*x/volume+h/volume^2)) drift (volume*b*(2*x/volume+h/volume^2)^2)
    (fun r => mul_nonneg hv.le (channel_intensity_nonneg n hn r)) (sq_nonneg x)
    (by positivity) hb.1 (by rw [raw_quadratic_first_moment]; exact hfirst) hb.2
  simpa only [← pow_mul] using result

end CompositionalMemory.Semenov
