import proofs.ThreeSitePhosphorylation.ClosedPaths
import proofs.ThreeSitePhosphorylation.SourceLift

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology

def familyFullPath {r w : ℝ} (C : ClosedPathFamily r w) (a : ℝ) : C(UnitTime,State) :=
  ContinuousMap.const UnitTime witnessState+
    a • (liftOperator.compLeftContinuous ℝ UnitTime) (C.paths a)

theorem familyFullPath_apply {r w : ℝ} (C : ClosedPathFamily r w) (a : ℝ) (t : UnitTime) :
    familyFullPath C a t=chart (a • C.paths a t) := by
  rw [chart_eq_tangent]
  simp [familyFullPath,liftOperator]

theorem familyFullPath_continuous {r w : ℝ} (C : ClosedPathFamily r w) :
    ContinuousAt (familyFullPath C) 0 := by
  unfold familyFullPath
  exact continuousAt_const.add (continuousAt_id.smul
    ((liftOperator.compLeftContinuous ℝ UnitTime).continuous.continuousAt.comp C.paths_smooth.continuousAt))

theorem familyFullPath_small {r w : ℝ} (C : ClosedPathFamily r w) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a in 𝓝 (0:ℝ), ∀ t : UnitTime, ‖chart (a • C.paths a t)-witnessState‖<ε := by
  have hc := familyFullPath_continuous C
  have he := hc.tendsto.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [he] with a ha
  have hn : ‖familyFullPath C a-ContinuousMap.const UnitTime witnessState‖<ε := by
    simpa [Metric.mem_ball,dist_eq_norm,familyFullPath] using ha
  intro t
  have hb := ContinuousMap.norm_coe_le_norm
    (familyFullPath C a-ContinuousMap.const UnitTime witnessState) t
  simpa only [ContinuousMap.sub_apply,ContinuousMap.const_apply,familyFullPath_apply]
    using hb.trans_lt hn

theorem witness_state_lower_bound (i : Fin 12) : (7/250:ℝ) ≤ witnessState i := by
  fin_cases i <;> norm_num [witnessState]

theorem familyFullPath_positive {r w : ℝ} (C : ClosedPathFamily r w) :
    ∀ᶠ a in 𝓝 (0:ℝ), ∀ t : UnitTime, ∀ i, 0<chart (a • C.paths a t) i := by
  filter_upwards [familyFullPath_small C (7/250) (by norm_num)] with a ha
  intro t i
  have hn := (norm_le_pi_norm (chart (a • C.paths a t)-witnessState) i).trans_lt (ha t)
  have hlo := (abs_lt.mp hn).1
  have hb := witness_state_lower_bound i
  change -(7/250:ℝ)<chart (a • C.paths a t) i-witnessState i at hlo
  linarith

theorem family_velocity_nonzero {r w : ℝ} (C : ClosedPathFamily r w) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    ∀ᶠ a in 𝓝 (0:ℝ), rescaledField a (C.parameters a).2.re (C.parameters a).1 ≠ 0 := by
  have hb := C.parameters_smooth.continuousAt
  have hc : ContinuousAt (fun a => rescaledField a (C.parameters a).2.re (C.parameters a).1) 0 := by
    have hi : ContinuousAt (fun a : ℝ => ((a,(C.parameters a).2.re),(C.parameters a).1)) 0 := by fun_prop
    exact rescaledField_smooth.continuous.continuousAt.comp
      (f := fun a : ℝ => ((a,(C.parameters a).2.re),(C.parameters a).1)) hi
  apply hc.eventually_ne
  rw [C.parameters_zero]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_im,zero_mul,one_mul,sub_self,add_zero,rescaledField_zero]
  obtain ⟨hv,he⟩ := source_root_eigenvector r (Complex.I*(w:ℂ)) hp
  exact critical_velocity_nonzero r w (ne_of_gt hw) _ hv he

theorem family_parameters_near {r w : ℝ} (C : ClosedPathFamily r w) (hr : 0<r) (hw : 0<w)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a in 𝓝 (0:ℝ), 0<(C.parameters a).2.re ∧ 0<(C.parameters a).2.im ∧
      |(C.parameters a).2.re-r|<ε ∧ |(C.parameters a).2.im-2*Real.pi/w|<ε := by
  have hb := C.parameters_smooth.continuousAt
  have hre : ContinuousAt (fun a => (C.parameters a).2.re) 0 := by fun_prop
  have him : ContinuousAt (fun a => (C.parameters a).2.im) 0 := by fun_prop
  have he0 : (C.parameters 0).2.re=r := by simp [C.parameters_zero]
  have hi0 : (C.parameters 0).2.im=2*Real.pi/w := by simp [C.parameters_zero]
  have hT : 0<2*Real.pi/w := by positivity
  have hrep := hre.eventually (Ioi_mem_nhds (he0.symm ▸ hr))
  have himp := him.eventually (Ioi_mem_nhds (hi0.symm ▸ hT))
  have her := hre.eventually (Metric.ball_mem_nhds _ hε)
  have hei := him.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hrep,himp,her,hei] with a h1 h2 h3 h4
  exact ⟨h1,h2,by simpa [Metric.mem_ball,Real.dist_eq,he0] using h3,
    by simpa [Metric.mem_ball,Real.dist_eq,hi0] using h4⟩

end
end ThreeSitePhosphorylation
