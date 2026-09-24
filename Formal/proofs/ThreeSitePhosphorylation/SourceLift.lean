import proofs.ThreeSitePhosphorylation.Rank
import proofs.ThreeSitePhosphorylation.RescaledSource
import proofs.ThreeSitePhosphorylation.LinearOrbit

namespace ThreeSitePhosphorylation
noncomputable section

def liftOperator : ReducedState →L[ℝ] State := tangentMap.toContinuousLinearMap

theorem lift_reduced_field (r : ℝ) (y : ReducedState) :
    liftOperator (reducedField r y)=field (witnessRates r) (chart y) :=
  source_is_tangent (flux (witnessRates r) (chart y))

theorem chart_hasFDerivAt (y : ReducedState) : HasFDerivAt chart liftOperator y := by
  have he : chart=(fun y => witnessState+liftOperator y) := funext chart_eq_tangent
  rw [he]
  exact liftOperator.hasFDerivAt.const_add witnessState

theorem lift_rescaled_derivative (a r T t : ℝ) (u : ℝ → ReducedState)
    (hu : HasDerivAt u (T • rescaledField a r (u t)) t) :
    HasDerivAt (fun s => chart (a • u s))
      (T • field (witnessRates r) (chart (a • u t))) t := by
  have hd := (chart_hasFDerivAt (a • u t)).comp_hasDerivAt t (hu.const_smul a)
  convert hd using 1
  rw [smul_comm a T,rescaledField_source,map_smul,lift_reduced_field]

theorem critical_velocity_nonzero (r w : ℝ) (hw : w ≠ 0) (v : Fin 9 → ℂ)
    (hv : v ≠ 0) (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) :
    jacobianOperator r (realPart v) ≠ 0 := by
  obtain ⟨ha,hb⟩ := source_eigen_real_imag r w v he
  intro hz
  rw [hz] at ha
  have him : imagPart v=0 := (smul_eq_zero.mp ha.symm).resolve_left (neg_ne_zero.mpr hw)
  rw [him,map_zero] at hb
  have hre : realPart v=0 := (smul_eq_zero.mp hb.symm).resolve_left hw
  exact source_eigen_real_nonzero r w hw v hv he hre

end
end ThreeSitePhosphorylation
