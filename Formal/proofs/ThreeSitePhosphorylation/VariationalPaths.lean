import proofs.ThreeSitePhosphorylation.PathODE

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology

def pathDelta : SourcePath →L[ℝ] SourcePath :=
  (jacobianOperator 1).compLeftContinuous ℝ UnitTime-
    (jacobianOperator 0).compLeftContinuous ℝ UnitTime

theorem pathLinear_direction (r dr : ℝ) (u : ℝ → SourcePath) (q : SourcePath)
    (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => pathLinear (r+s*dr) (u s))
      (pathLinear r q+dr • pathDelta (u 0)) 0 := by
  have hr : HasDerivAt (fun s : ℝ => r+s*dr) dr 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dr).const_add r
  have h0 := ((jacobianOperator 0).compLeftContinuous ℝ UnitTime).hasFDerivAt.comp_hasDerivAt 0 hu
  have hd := pathDelta.hasFDerivAt.comp_hasDerivAt 0 hu
  have hh := h0.add (hr.smul hd)
  convert hh using 1
  simp only [zero_mul,add_zero,pathLinear,pathDelta,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,Function.comp_apply]
  abel

theorem pathField_direction (r T dr dT : ℝ) (u : ℝ → SourcePath) (q : SourcePath)
    (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => pathField (0,(r+s*dr,T+s*dT)) (u s))
      (T • pathLinear r q+dT • pathLinear r (u 0)+T • (dr • pathDelta (u 0))) 0 := by
  have ht : HasDerivAt (fun s : ℝ => T+s*dT) dT 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dT).const_add T
  have hh := ht.smul (pathLinear_direction r dr u q hu)
  convert hh using 1
  · ext s
    simp [pathField]
  · simp only [zero_mul,add_zero,smul_add]
    abel

/-- Differentiating the actual integral equation gives the full parameter/period
variational equation on the whole unit interval. -/
theorem variational_path_equation (r T dr dT : ℝ) (x dx : ReducedState)
    (u : ℝ → SourcePath) (q : SourcePath) (hu : HasDerivAt u q 0)
    (he : ∀ᶠ s in 𝓝 (0:ℝ), pathResidual (((0,(r+s*dr,T+s*dT)),x+s • dx),u s)=0) :
    q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ ReducedState)
      (T • pathLinear r q+dT • pathLinear r (u 0)+T • (dr • pathDelta (u 0))) := by
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  have hc := constantPath.hasFDerivAt.comp_hasDerivAt 0 hx
  have hf := (linearPicard (ContinuousLinearMap.id ℝ ReducedState)).hasFDerivAt.comp_hasDerivAt 0
    (pathField_direction r T dr dT u q hu)
  have hh := (hu.sub hc).sub hf
  have hz : HasDerivAt (fun s : ℝ => pathResidual (((0,(r+s*dr,T+s*dT)),x+s • dx),u s)) 0 0 :=
    (hasDerivAt_const (x := (0:ℝ)) (c := (0:SourcePath))).congr_of_eventuallyEq he
  have hd := hh.unique hz
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp hd) |>.trans (add_comm _ _)

end
end ThreeSitePhosphorylation
