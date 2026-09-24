import proofs.CompositionalMemory.SemenovSourceTransport
import proofs.CompositionalMemory.SemenovCurvature
import proofs.CompositionalMemory.QuadraticRecoveryIdentity

namespace CompositionalMemory.Semenov
open Matrix

noncomputable def fieldRemainder (x : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ∑ r,chemicalQuadratic x r • (fun j => (stoich r j : ℝ))

noncomputable def nominalJacobian (z : Fin 8 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ := jacobianValue z

theorem fieldRemainder_apply (x : Fin 8 → ℝ) (i : Fin 8) :
    fieldRemainder x i=∑ r,(stoich r i : ℝ)*chemicalQuadratic x r := by
  simp only [fieldRemainder,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem field_decomposition (z x : Fin 8 → ℝ) :
    fieldValue (z+x)=fieldValue z+(nominalJacobian z).mulVec x+fieldRemainder x := by
  funext i
  change fieldValue (fun j => z j+x j) i=fieldValue z i+
    (∑ j,jacobianValue z i j*x j)+fieldRemainder x i
  rw [jacobian_action,fieldRemainder_apply]
  exact field_taylor_exact z x i

theorem field_remainder_bilinear (P : Matrix (Fin 8) (Fin 8) ℝ) (x : Fin 8 → ℝ) :
    2*P.toBilin' x (fieldRemainder x)=
      ∑ r,2*(∑ i,x i*(P.mulVec (fun j => (stoich r j : ℝ))) i)*chemicalQuadratic x r := by
  simp only [fieldRemainder,map_sum,map_smul,smul_eq_mul,Finset.mul_sum,Matrix.toBilin'_apply',dotProduct]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def rawQuadraticNumerator (P Pd : Matrix (Fin 8) (Fin 8) ℝ)
    (z zd n : Fin 8 → ℝ) (volume : ℝ) : ℝ :=
  matrixEnergy Pd (n-z)-2*P.toBilin' (n-z) zd+
    ∑ r,volume*channelIntensity n r*(matrixEnergy P ((n-z)+(1/volume) • channelJump r)-matrixEnergy P (n-z))

noncomputable def rawQuadraticDrift (P Pd : Matrix (Fin 8) (Fin 8) ℝ)
    (z zd n : Fin 8 → ℝ) (volume eta : ℝ) : ℝ := rawQuadraticNumerator P Pd z zd n volume/eta

theorem raw_quadratic_numerator_identity (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (t : ℝ)
    (Pd : Matrix (Fin 8) (Fin 8) ℝ) (z zd n : Fin 8 → ℝ) (volume : ℝ) (hv : volume ≠ 0)
    (hp : ∀ i j,coefficientValue (pc i j) t=coefficientValue (pc j i) t) :
    rawQuadraticNumerator (coefficientMatrix pc t) Pd z zd n volume=
      -vectorSquares (n-z)+
        matrixEnergy (Pd+(nominalJacobian z).transpose*coefficientMatrix pc t+
          coefficientMatrix pc t*nominalJacobian z+(1 : Matrix (Fin 8) (Fin 8) ℝ)) (n-z)+
        2*(∑ i,(n-z) i*((coefficientMatrix pc t).mulVec (fieldValue z-zd)) i)+
        (∑ r,2*(∑ i,(n-z) i*((coefficientMatrix pc t).mulVec (fun j => (stoich r j : ℝ))) i)*chemicalQuadratic (n-z) r)+
        metricNoiseValue pc t n/volume := by
  let P := coefficientMatrix pc t
  have hfield : (∑ r,channelIntensity n r • channelJump r)=fieldValue n := by
    funext i
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using channel_drift_identity n i
  have hgen := reaction_energy_generator_identity P.toBilin' (matrix_bilinear_symmetric P hp)
    (n-z) channelJump (channelIntensity n) volume hv
  simp only [← matrixEnergy_toBilin] at hgen
  dsimp only [P] at hgen
  rw [hfield,channel_noise_identity] at hgen
  have hf : fieldValue n=fieldValue z+(nominalJacobian z).mulVec (n-z)+fieldRemainder (n-z) := by
    have hh := field_decomposition z (n-z)
    have he : z+(n-z)=n := by abel
    rw [he] at hh
    exact hh
  have hi := quadratic_recovery_identity P Pd (nominalJacobian z) hp (n-z) (fieldValue n)
    (fieldValue z) zd (fieldRemainder (n-z)) hf
  unfold rawQuadraticNumerator
  rw [hgen]
  have he : matrixEnergy Pd (n-z)-2*P.toBilin' (n-z) zd+
      (2*P.toBilin' (n-z) (fieldValue n)+(1/volume)*metricNoiseValue pc t n)=
        matrixEnergy Pd (n-z)+2*P.toBilin' (n-z) (fieldValue n-zd)+metricNoiseValue pc t n/volume := by
    rw [map_sub (P.toBilin' (n-z)) (fieldValue n) zd]
    ring
  rw [he,hi,field_remainder_bilinear]
  simp only [Matrix.toBilin'_apply',dotProduct,P]

theorem recovery_drift_arithmetic (energy S residual curvature forcing noise eta L volume F Q d : ℝ)
    (heta : 0 < eta) (hL : 0 < L) (hv : 0 < volume) (hS : 0 ≤ S)
    (henergy : energy ≤ L*S) (hid : d*eta = -S+residual+curvature+forcing+noise/volume)
    (hres : residual ≤ (1/1000 : ℝ)*S) (hcurv : curvature ≤ (12/25 : ℝ)*S)
    (hforce : forcing ≤ (1/100 : ℝ)*S+100*F^2) (hnoise : noise ≤ Q) :
    d ≤ (-energy/(2*L)+Q/volume+100*F^2)/eta := by
  have he : energy/L ≤ S := (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using henergy)
  have hneg : -S/2 ≤ -energy/(2*L) := by
    rw [mul_comm (2 : ℝ) L,div_mul_eq_div_div]
    simp only [neg_div]
    linarith only [he]
  have hn := div_le_div_of_nonneg_right hnoise hv.le
  apply (le_div_iff₀ heta).mpr
  linarith only [hid,hres,hcurv,hforce,hn,hneg,hS]

end CompositionalMemory.Semenov
