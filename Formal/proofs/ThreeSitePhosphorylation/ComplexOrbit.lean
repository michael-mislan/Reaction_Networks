import proofs.ThreeSitePhosphorylation.LinearOrbit
import proofs.ThreeSitePhosphorylation.ScalarODE

namespace ThreeSitePhosphorylation
noncomputable section

def complexify : ReducedState →L[ℝ] (Fin 9 → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem complexify_apply (y : ReducedState) (i : Fin 9) :
    complexify y i=(y i:ℂ) := rfl

theorem complexify_source (r : ℝ) (y : ReducedState) :
    complexify (jacobianOperator r y)=(complexSource r).mulVec (complexify y) := by
  rw [← sourceMatrix_action]
  ext i
  simp [complexSource,Matrix.mulVec,dotProduct]

def conjugateVector (v : Fin 9 → ℂ) : Fin 9 → ℂ := fun i => star (v i)

theorem conjugate_source (r : ℝ) (v : Fin 9 → ℂ) :
    (complexSource r).mulVec (conjugateVector v)=conjugateVector ((complexSource r).mulVec v) := by
  ext i
  simp [conjugateVector,complexSource,Matrix.mulVec,dotProduct]

theorem conjugate_eigen (r w : ℝ) (v : Fin 9 → ℂ)
    (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) :
    (complexSource r).mulVec (conjugateVector v)=(-Complex.I*(w:ℂ)) • conjugateVector v := by
  rw [conjugate_source,he]
  ext i
  simp [conjugateVector]

theorem complexify_orbit (v : Fin 9 → ℂ) (θ : ℝ) :
    complexify (Real.cos θ • realPart v-Real.sin θ • imagPart v)=
      (Complex.exp ((θ:ℂ)*Complex.I)/2) • v+
      (Complex.exp (-(θ:ℂ)*Complex.I)/2) • conjugateVector v := by
  rw [Complex.exp_ofReal_mul_I,← Complex.ofReal_neg,Complex.exp_ofReal_mul_I]
  ext i
  apply Complex.ext <;>
    simp [complexify,realPart,imagPart,conjugateVector,Complex.mul_re,Complex.mul_im] <;> ring

theorem normalized_orbit_harmonics (v : Fin 9 → ℂ) (w : ℝ) (hw : w ≠ 0) (t : ℝ) :
    complexify (linearOrbit (realPart v) (imagPart v) w ((2*Real.pi/w)*t))=
      (Complex.exp (turnFrequency*(t:ℂ))/2) • v+
      (Complex.exp (-turnFrequency*(t:ℂ))/2) • conjugateVector v := by
  have ht : w*((2*Real.pi/w)*t)=2*Real.pi*t := by field_simp
  rw [linearOrbit,ht,complexify_orbit]
  congr 3 <;> simp only [turnFrequency,Complex.ofReal_mul,Complex.ofReal_ofNat] <;> ring

end
end ThreeSitePhosphorylation
