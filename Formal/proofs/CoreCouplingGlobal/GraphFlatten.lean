import proofs.CoreCouplingGlobal.StableGraphNormal

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

noncomputable def firstThreeLinear : ResponseVector →L[ℝ] StableData :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.castSucc

noncomputable def graphShear (g : StableData → ℝ) (v : ResponseVector) : ResponseVector :=
  v-unstableInclusion (g (firstThreeLinear v))

noncomputable def graphUnshear (g : StableData → ℝ) (v : ResponseVector) : ResponseVector :=
  v+unstableInclusion (g (firstThreeLinear v))

theorem firstThree_unstable (a : ℝ) : firstThreeLinear (unstableInclusion a)=0 := by
  ext i
  fin_cases i <;> simp [firstThreeLinear,unstableInclusion]

theorem graphShear_firstThree (g : StableData → ℝ) (v : ResponseVector) :
    firstThreeLinear (graphShear g v)=firstThreeLinear v := by
  simp only [graphShear,map_sub,firstThree_unstable,sub_zero]

theorem graphUnshear_firstThree (g : StableData → ℝ) (v : ResponseVector) :
    firstThreeLinear (graphUnshear g v)=firstThreeLinear v := by
  simp only [graphUnshear,map_add,firstThree_unstable,add_zero]

theorem graph_shear_inverse (g : StableData → ℝ) (v : ResponseVector) :
    graphUnshear g (graphShear g v)=v ∧ graphShear g (graphUnshear g v)=v := by
  constructor
  · rw [graphUnshear,graphShear_firstThree,graphShear,sub_add_cancel]
  · rw [graphShear,graphUnshear_firstThree,graphUnshear,add_sub_cancel_right]

theorem graphShear_contDiffAt (g : StableData → ℝ) (v : ResponseVector)
    (hg : ContDiffAt ℝ ω g (firstThreeLinear v)) : ContDiffAt ℝ ω (graphShear g) v :=
  contDiffAt_id.sub (unstableInclusion.contDiff.contDiffAt.comp v
    (hg.comp v firstThreeLinear.contDiff.contDiffAt))

theorem graphUnshear_contDiffAt (g : StableData → ℝ) (v : ResponseVector)
    (hg : ContDiffAt ℝ ω g (firstThreeLinear v)) : ContDiffAt ℝ ω (graphUnshear g) v :=
  contDiffAt_id.add (unstableInclusion.contDiff.contDiffAt.comp v
    (hg.comp v firstThreeLinear.contDiff.contDiffAt))

noncomputable def physicalGraphFlatten (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (x : ResponseVector) : ResponseVector :=
  graphShear (stableGraphHeight C s φ) (C.symm (x-encodeState s))

noncomputable def physicalGraphUnflatten (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (v : ResponseVector) : ResponseVector :=
  encodeState s+C (graphUnshear (stableGraphHeight C s φ) v)

theorem physical_graph_flatten_inverse (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (x v : ResponseVector) :
    physicalGraphUnflatten C s φ (physicalGraphFlatten C s φ x)=x ∧
    physicalGraphFlatten C s φ (physicalGraphUnflatten C s φ v)=v := by
  constructor
  · simp only [physicalGraphUnflatten,physicalGraphFlatten,(graph_shear_inverse _ _).1,
      ContinuousLinearEquiv.apply_symm_apply,add_sub_cancel]
  · simp only [physicalGraphUnflatten,physicalGraphFlatten,add_sub_cancel_left,
      ContinuousLinearEquiv.symm_apply_apply,(graph_shear_inverse _ _).2]

theorem physicalGraphFlatten_last (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (x : ResponseVector) :
    physicalGraphFlatten C s φ x 3=stableGraphResidual C s φ x := by
  rfl

/-- The physical graph flattens by actual analytic inverse maps. -/
theorem physical_graph_flatten_analytic (C : ResponseVector ≃L[ℝ] ResponseVector)
    (s : State) (φ : StableData → ResponseVector) (x : ResponseVector)
    (hφ : ContDiffAt ℝ ω φ (middleStableProjection C s x)) :
    ContDiffAt ℝ ω (physicalGraphFlatten C s φ) x ∧
      ContDiffAt ℝ ω (physicalGraphUnflatten C s φ) (physicalGraphFlatten C s φ x) := by
  have hg := stableGraphHeight_contDiffAt C s φ _ hφ
  have hcoord : ContDiffAt ℝ ω (fun y => C.symm (y-encodeState s)) x :=
    C.symm.toContinuousLinearMap.contDiff.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const)
  have hflat := (graphShear_contDiffAt _ (C.symm (x-encodeState s)) hg).comp x hcoord
  have hgu : ContDiffAt ℝ ω (stableGraphHeight C s φ)
      (firstThreeLinear (physicalGraphFlatten C s φ x)) := by
    simpa only [physicalGraphFlatten,graphShear_firstThree] using hg
  have hu := graphUnshear_contDiffAt _ (physicalGraphFlatten C s φ x) hgu
  exact ⟨hflat,contDiffAt_const.add (C.toContinuousLinearMap.contDiff.contDiffAt.comp _ hu)⟩

end CoreCouplingGlobal
