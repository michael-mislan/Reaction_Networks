import proofs.CompositionalMemory.SemenovSourceTransport
import proofs.CompositionalMemory.ReactionPowerMoments
import proofs.CompositionalMemory.MatrixBilinearEnergy

namespace CompositionalMemory.Semenov
open Matrix

noncomputable def normalizedBilinear (P : Matrix (Fin 8) (Fin 8) ℝ) (eta : ℝ) :=
  (1/eta) • P.toBilin'

theorem normalized_bilinear_energy (P : Matrix (Fin 8) (Fin 8) ℝ) (eta : ℝ) (v : Fin 8 → ℝ) :
    normalizedBilinear P eta v v=matrixEnergy P v/eta := by
  simp only [normalizedBilinear,LinearMap.smul_apply,smul_eq_mul,← matrixEnergy_toBilin]
  ring

theorem geometry_channel_energy_bound
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (r : Channel) :
    matrixEnergy (coefficientMatrix pc t) (channelJump r) ≤ (H : ℝ) := by
  rcases hg with ⟨_,_,_,_,_,_,_,_,hchem,hflow,_⟩
  rcases r with r | (j | j)
  · change matrixEnergy (coefficientMatrix pc t) (fun j => (stoich r j : ℝ)) ≤ _
    rw [← jump_energy_value]
    exact (coefficientValue_bounds _ t hl hu).2.trans (by exact_mod_cast (hchem r).2)
  · change matrixEnergy (coefficientMatrix pc t) (fun i => if i=j then (1 : ℝ) else 0) ≤ _
    rw [matrix_energy_coordinate]
    simp only [one_pow,mul_one,coefficientMatrix]
    exact (coefficientValue_bounds _ t hl hu).2.trans (by exact_mod_cast (hflow j).2)
  · change matrixEnergy (coefficientMatrix pc t) (fun i => if i=j then (-1 : ℝ) else 0) ≤ _
    rw [matrix_energy_coordinate]
    simp only [neg_one_sq,mul_one,coefficientMatrix]
    exact (coefficientValue_bounds _ t hl hu).2.trans (by exact_mod_cast (hflow j).2)

theorem normalized_channel_jump_bounds
    (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (t eta volume x h b : ℝ)
    (v n : Fin 8 → ℝ) (heta : 0 < eta) (hv : 0 < volume) (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hsym : ∀ i j,coefficientValue (pc i j) t=coefficientValue (pc j i) t)
    (hpos : ∀ w,0 ≤ matrixEnergy (coefficientMatrix pc t) w)
    (hn : ∀ j,0 ≤ n j) (he : matrixEnergy (coefficientMatrix pc t) v/eta=x^2)
    (hjump : ∀ r,matrixEnergy (coefficientMatrix pc t) (channelJump r)/eta ≤ h^2)
    (hnoise : metricNoiseValue pc t n/eta ≤ b) :
    (∀ r,|(matrixEnergy (coefficientMatrix pc t) (v+(1/volume) • channelJump r)-
      matrixEnergy (coefficientMatrix pc t) v)/eta| ≤ h*(2*x/volume+h/volume^2)) ∧
    (∑ r,volume*channelIntensity n r*((matrixEnergy (coefficientMatrix pc t)
      (v+(1/volume) • channelJump r)-matrixEnergy (coefficientMatrix pc t) v)/eta)^2) ≤
      volume*b*(2*x/volume+h/volume^2)^2 := by
  have hs : ∀ u w,normalizedBilinear (coefficientMatrix pc t) eta u w=
      normalizedBilinear (coefficientMatrix pc t) eta w u := by
    intro u w
    simp only [normalizedBilinear,LinearMap.smul_apply,smul_eq_mul,
      matrix_bilinear_symmetric (coefficientMatrix pc t) hsym u w]
  have hp : ∀ w,0 ≤ normalizedBilinear (coefficientMatrix pc t) eta w w := by
    intro w
    rw [normalized_bilinear_energy]
    exact div_nonneg (hpos w) heta.le
  have hb : (∑ r,channelIntensity n r*normalizedBilinear (coefficientMatrix pc t) eta
      (channelJump r) (channelJump r)) ≤ b := by
    simp only [normalized_bilinear_energy,← mul_div_assoc,← Finset.sum_div,channel_noise_identity]
    exact hnoise
  have result := bilinear_reaction_jump_bounds (normalizedBilinear (coefficientMatrix pc t) eta)
    hs hp v channelJump (channelIntensity n) volume x h b hv hx hh
    (by simpa only [normalized_bilinear_energy] using he) (channel_intensity_nonneg n hn)
    (by simpa only [normalized_bilinear_energy] using hjump) hb
  simpa only [normalized_bilinear_energy,← sub_div] using result

end CompositionalMemory.Semenov
