import proofs.ThreeSitePhosphorylation.PathSource

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology
set_option maxHeartbeats 200000

abbrev FlowData := (ℝ × (ℝ × ℝ)) × ReducedState

def constantPath : ReducedState →L[ℝ] SourcePath := ContinuousLinearMap.const ℝ UnitTime

def pathResidual (p : FlowData × SourcePath) : SourcePath :=
  p.2-constantPath p.1.2-
    linearPicard (ContinuousLinearMap.id ℝ ReducedState) (pathField p.1.1 p.2)

theorem pathResidual_smooth : ContDiff ℝ ⊤ pathResidual := by
  have hf : ContDiff ℝ ⊤ (fun p : FlowData × SourcePath => pathField p.1.1 p.2) :=
    pathField_smooth.comp (f := fun p : FlowData × SourcePath => (p.1.1,p.2))
      (contDiff_fst.fst.prodMk contDiff_snd)
  unfold pathResidual
  exact (contDiff_snd.sub (constantPath.contDiff.comp
    (f := fun p : FlowData × SourcePath => p.1.2) contDiff_fst.snd)).sub
    ((linearPicard (ContinuousLinearMap.id ℝ ReducedState)).contDiff.comp
      (f := fun p : FlowData × SourcePath => pathField p.1.1 p.2) hf)

theorem pathResidual_zero_amplitude (r T : ℝ) (x : ReducedState) (u : SourcePath) :
    pathResidual (((0,(r,T)),x),u) =
      (1-linearPicard (T • jacobianOperator r)) u-constantPath x := by
  simp only [pathResidual,pathField,zero_smul,add_zero,linearPicard_pathLinear]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]
  abel

theorem pathResidual_path_derivative (r T : ℝ) (x : ReducedState) (u : SourcePath) :
    fderiv ℝ pathResidual (((0,(r,T)),x),u) ∘L
      ContinuousLinearMap.inr ℝ FlowData SourcePath =
        1-linearPicard (T • jacobianOperator r) := by
  have hi : HasFDerivAt (fun v : SourcePath => (((0,(r,T)),x),v))
      (ContinuousLinearMap.inr ℝ FlowData SourcePath) u := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (((0,(r,T)),x) : FlowData) u).prodMk
      (hasFDerivAt_id u) using 1
  have hc := (pathResidual_smooth.differentiable (by simp)
    (((0,(r,T)),x),u)).hasFDerivAt.comp u hi
  have he : (fun v : SourcePath => pathResidual (((0,(r,T)),x),v)) =
      (fun v => (1-linearPicard (T • jacobianOperator r)) v-constantPath x) :=
    funext (pathResidual_zero_amplitude r T x)
  have hd : HasFDerivAt (fun v : SourcePath => pathResidual (((0,(r,T)),x),v))
      (1-linearPicard (T • jacobianOperator r)) u := by
    rw [he]
    exact (1-linearPicard (T • jacobianOperator r)).hasFDerivAt.sub_const _
  exact hc.unique hd

/-- Smooth full-interval solutions near any zero-amplitude linear solution.
The base residual hypothesis is an explicit integral equation, not a flow theorem. -/
theorem smooth_full_interval_paths (r T : ℝ) (x : ReducedState) (u : SourcePath)
    (hu : pathResidual (((0,(r,T)),x),u)=0) :
    ∃ ψ : FlowData → SourcePath,
      ContDiffAt ℝ ⊤ ψ ((0,(r,T)),x) ∧ ψ ((0,(r,T)),x)=u ∧
      ∀ᶠ p in 𝓝 ((0,(r,T)),x), pathResidual (p,ψ p)=0 := by
  have hi : (fderiv ℝ pathResidual (((0,(r,T)),x),u) ∘L
      ContinuousLinearMap.inr ℝ FlowData SourcePath).IsInvertible := by
    rw [pathResidual_path_derivative]
    obtain ⟨v,hv⟩ := linearPicard_one_sub_isUnit (T • jacobianOperator r)
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ SourcePath v,hv⟩
  let h := pathResidual_smooth.contDiffAt (x := (((0,(r,T)),x),u))
  refine ⟨h.implicitFunction (by simp) hi,h.contDiffAt_implicitFunction (by simp) hi,
    h.implicitFunction_apply_self (by simp) hi,?_⟩
  simpa only [hu] using h.eventually_apply_implicitFunction (by simp) hi

end
end ThreeSitePhosphorylation
