import proofs.ThreeSitePhosphorylation.SourceSimple
import proofs.ThreeSitePhosphorylation.PathSource

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 200000

def realPart (v : Fin 9 → ℂ) : ReducedState := fun i => (v i).re
def imagPart (v : Fin 9 → ℂ) : ReducedState := fun i => (v i).im

theorem source_real_action (r : ℝ) (v : Fin 9 → ℂ) :
    jacobianOperator r (realPart v) = realPart ((complexSource r).mulVec v) := by
  rw [← sourceMatrix_action]
  ext i
  simp [realPart,complexSource,Matrix.mulVec,dotProduct,Complex.mul_re]

theorem source_imag_action (r : ℝ) (v : Fin 9 → ℂ) :
    jacobianOperator r (imagPart v) = imagPart ((complexSource r).mulVec v) := by
  rw [← sourceMatrix_action]
  ext i
  simp [imagPart,complexSource,Matrix.mulVec,dotProduct,Complex.mul_im]

theorem source_eigen_real_imag (r w : ℝ) (v : Fin 9 → ℂ)
    (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) :
    jacobianOperator r (realPart v)=(-w) • imagPart v ∧
      jacobianOperator r (imagPart v)=w • realPart v := by
  rw [source_real_action,source_imag_action,he]
  constructor <;> ext i <;>
    simp [realPart,imagPart,Complex.mul_re,Complex.mul_im]

theorem source_eigen_real_nonzero (r w : ℝ) (hw : w ≠ 0) (v : Fin 9 → ℂ)
    (hv : v ≠ 0) (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) :
    realPart v ≠ 0 := by
  intro hr
  have hi := (source_eigen_real_imag r w v he).1
  rw [hr,map_zero] at hi
  have hb : imagPart v=0 := (smul_eq_zero.mp hi.symm).resolve_left (neg_ne_zero.mpr hw)
  apply hv
  ext i
  apply Complex.ext
  · exact congrFun hr i
  · exact congrFun hb i

def linearOrbit (a b : ReducedState) (w t : ℝ) : ReducedState :=
  Real.cos (w*t) • a-Real.sin (w*t) • b

theorem linearOrbit_derivative (A : ReducedState →L[ℝ] ReducedState)
    (a b : ReducedState) (w : ℝ) (ha : A a=(-w) • b) (hb : A b=w • a) (t : ℝ) :
    HasDerivAt (linearOrbit a b w) (A (linearOrbit a b w t)) t := by
  have hc := ((Real.hasDerivAt_cos (w*t)).comp t ((hasDerivAt_id t).const_mul w)).smul_const a
  have hs := ((Real.hasDerivAt_sin (w*t)).comp t ((hasDerivAt_id t).const_mul w)).smul_const b
  convert hc.sub hs using 1
  simp only [linearOrbit,map_sub,map_smul,ha,hb,smul_smul]
  module

theorem linearOrbit_continuous (a b : ReducedState) (w : ℝ) :
    Continuous (linearOrbit a b w) := by unfold linearOrbit; fun_prop

def referencePath (a b : ReducedState) (w T : ℝ) : SourcePath :=
  ⟨fun t => linearOrbit a b w (T*(t:ℝ)),(linearOrbit_continuous a b w).comp (by fun_prop)⟩

theorem referencePath_endpoints (a b : ReducedState) (w : ℝ) (hw : w ≠ 0) :
    referencePath a b w (2*Real.pi/w) ⟨0,by norm_num⟩=a ∧
      referencePath a b w (2*Real.pi/w) ⟨1,by norm_num⟩=a := by
  have he : w*(2*Real.pi/w)=2*Real.pi := by field_simp
  simp [referencePath,linearOrbit,he]

theorem referencePath_integral (A : ReducedState →L[ℝ] ReducedState)
    (a b : ReducedState) (w T : ℝ) (ha : A a=(-w) • b) (hb : A b=w • a) :
    linearPicard (T • A) (referencePath a b w T) =
      referencePath a b w T-ContinuousMap.const UnitTime a := by
  have hd (s : ℝ) : HasDerivAt (fun t => linearOrbit a b w (T*t))
      ((T • A) (linearOrbit a b w (T*s))) s := by
    have ht : HasDerivAt (fun t : ℝ => T*t) T s := by
      simpa using ((hasDerivAt_id s).const_mul T)
    exact (linearOrbit_derivative A a b w ha hb (T*s)).scomp s ht
  ext t i
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := (t:ℝ)) (fun s _ => hd s)
    (((T • A).continuous.comp ((linearOrbit_continuous a b w).comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _)
  have he : (∫ s in (0:ℝ)..(t:ℝ), (T • A)
      (pathExtension (referencePath a b w T) s)) =
      ∫ s in (0:ℝ)..(t:ℝ), (T • A) (linearOrbit a b w (T*s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le t.2.1] at hs
      exact ⟨hs.1,hs.2.trans t.2.2⟩
    simp [pathExtension,Set.projIcc_of_mem _ hs',referencePath]
  change (∫ s in (0:ℝ)..(t:ℝ), (T • A)
      (pathExtension (referencePath a b w T) s)) i = _
  rw [he,hf]
  simp [referencePath,linearOrbit]

end
end ThreeSitePhosphorylation
