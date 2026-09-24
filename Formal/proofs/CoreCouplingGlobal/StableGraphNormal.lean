import proofs.CoreCouplingGlobal.LocalBasinGraph

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

noncomputable def stableCoordinateLinear (C : ResponseVector ≃L[ℝ] ResponseVector) :
    ResponseVector →L[ℝ] StableData :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i.castSucc).comp C.symm.toContinuousLinearMap

noncomputable def unstableCoordinateLinear (C : ResponseVector ≃L[ℝ] ResponseVector) :
    ResponseVector →L[ℝ] ℝ := (ContinuousLinearMap.proj 3).comp C.symm.toContinuousLinearMap

noncomputable def stableGraphHeight (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (ξ : StableData) : ℝ :=
  unstableCoordinateLinear C (φ ξ-encodeState s)

noncomputable def stableGraphResidual (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (x : ResponseVector) : ℝ :=
  unstableCoordinateLinear C (x-encodeState s)-
    stableGraphHeight C s φ (middleStableProjection C s x)

theorem stable_projection_linear (C : ResponseVector ≃L[ℝ] ResponseVector) (s : State)
    (x : ResponseVector) : middleStableProjection C s x=stableCoordinateLinear C (x-encodeState s) := rfl

theorem stable_coordinates_unstable_vector (C : ResponseVector ≃L[ℝ] ResponseVector) :
    stableCoordinateLinear C (C (unstableInclusion 1))=0 ∧
      unstableCoordinateLinear C (C (unstableInclusion 1))=1 := by
  constructor
  · ext i
    fin_cases i <;> simp [stableCoordinateLinear,unstableInclusion]
  · simp [unstableCoordinateLinear,unstableInclusion]

theorem stableGraphHeight_contDiffAt (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (ξ : StableData)
    (hφ : ContDiffAt ℝ ω φ ξ) : ContDiffAt ℝ ω (stableGraphHeight C s φ) ξ :=
  (unstableCoordinateLinear C).contDiff.contDiffAt.comp ξ (hφ.sub contDiffAt_const)

/-- The graph residual has a nonzero normal at every regular graph-domain point:
its derivative in the physical unstable coordinate direction is exactly one. -/
theorem stableGraphResidual_regular (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (x : ResponseVector)
    (hφ : ContDiffAt ℝ ω φ (middleStableProjection C s x)) :
    ContDiffAt ℝ ω (stableGraphResidual C s φ) x ∧
      ∃ N : ResponseVector →L[ℝ] ℝ, HasFDerivAt (stableGraphResidual C s φ) N x ∧
        N (C (unstableInclusion 1))=1 := by
  have hp : HasFDerivAt (middleStableProjection C s) (stableCoordinateLinear C) x := by
    simpa only [ContinuousLinearMap.comp_id] using
      (stableCoordinateLinear C).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (encodeState s))
  have hu : HasFDerivAt (fun y => unstableCoordinateLinear C (y-encodeState s))
      (unstableCoordinateLinear C) x := by
    simpa only [ContinuousLinearMap.comp_id] using
      (unstableCoordinateLinear C).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (encodeState s))
  have hg := stableGraphHeight_contDiffAt C s φ _ hφ
  have hgp := (hg.differentiableAt (by simp)).hasFDerivAt.comp x hp
  have hd := hu.sub hgp
  have hcp : ContDiffAt ℝ ω (middleStableProjection C s) x :=
    (stableCoordinateLinear C).contDiff.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const)
  have hcu : ContDiffAt ℝ ω (fun y => unstableCoordinateLinear C (y-encodeState s)) x :=
    (unstableCoordinateLinear C).contDiff.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const)
  refine ⟨hcu.sub (hg.comp x hcp),_,hd,?_⟩
  obtain ⟨hstable,hunstable⟩ := stable_coordinates_unstable_vector C
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.coe_comp',Function.comp_apply,
    hstable,hunstable,map_zero,sub_zero]

/-- The scalar graph equation is exact wherever the stable projection belongs
to the patch domain. -/
theorem stableGraphResidual_zero_iff (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (U : Set StableData)
    (hleft : ∀ ξ ∈ U, middleStableProjection C s (φ ξ)=ξ)
    (x : ResponseVector) (hx : middleStableProjection C s x ∈ U) :
    stableGraphResidual C s φ x=0 ↔ x=φ (middleStableProjection C s x) := by
  let ξ := middleStableProjection C s x
  have hξ : ξ ∈ U := hx
  have hproj := hleft ξ hξ
  constructor
  · intro hz
    have heq : C.symm (x-encodeState s)=C.symm (φ ξ-encodeState s) := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change C.symm (x-encodeState s) 3=C.symm (φ ξ-encodeState s) 3
        exact sub_eq_zero.1 hz
      · exact (congrFun hproj j).symm
    have hh := C.symm.injective heq
    simpa only [sub_add_cancel] using congrArg (fun v => v+encodeState s) hh
  · intro heq
    change unstableCoordinateLinear C (x-encodeState s)-unstableCoordinateLinear C (φ ξ-encodeState s)=0
    rw [heq]
    exact sub_self _

end CoreCouplingGlobal
