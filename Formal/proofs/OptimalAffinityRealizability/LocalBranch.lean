import proofs.OptimalAffinityRealizability.AugmentedJacobian

namespace OptimalAffinityRealizability

open Filter
open scoped Topology
noncomputable section

def controlledTargetDirection {n : ℕ} (source : SquareSource n) : Fin n → ℝ :=
  fun i => if i = source.controlled then 1 else 0

theorem augmentedSteadyContinuousLinearEquiv_symm_controlledTargetDirection
    {n : ℕ} (source : SquareSource n) (E : Matrix (Fin n) (Fin n) ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source E)
    (u : Fin n → ℝ) (hkernel : E.mulVec u = 0)
    (hcontrol : u source.controlled = 1) :
    (augmentedSteadyContinuousLinearEquiv source E hreduced).symm
        (controlledTargetDirection source) = u := by
  let D := augmentedSteadyContinuousLinearEquiv source E hreduced
  have hAu : (augmentedSteadyJacobian source E).mulVec u =
      controlledTargetDirection source := by
    funext i
    by_cases hi : i = source.controlled
    · subst i
      rw [augmentedSteadyJacobian_mulVec_controlled]
      simpa [controlledTargetDirection] using hcontrol
    · rw [augmentedSteadyJacobian_mulVec_noncontrolled source E u i hi, hkernel]
      simp [controlledTargetDirection, hi]
  apply D.injective
  rw [D.apply_symm_apply]
  simpa [D] using hAu.symm

theorem canonicalLocalBranch_hasStrictFDerivAt_kernelTangent
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q))
    (u : Fin n → ℝ)
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0)
    (hcontrol : u source.controlled = 1) :
    let F := augmentedLogStationarity source J g q
    let D := augmentedSteadyContinuousLinearEquiv source
      (literalCurrentJacobian source J g q) hreduced
    let hD : HasStrictFDerivAt F (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0 := by
      simpa [F, D] using augmentedLogStationarity_hasStrictFDerivAt_zero source J g q
    HasStrictFDerivAt
      (inverseFunctionBranch F 0 D hD (controlledTargetDirection source))
      (scalarDirectionMap u) 0 := by
  dsimp only
  let D := augmentedSteadyContinuousLinearEquiv source
    (literalCurrentJacobian source J g q) hreduced
  let hD : HasStrictFDerivAt (augmentedLogStationarity source J g q)
      (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0 := by
    simpa [D] using augmentedLogStationarity_hasStrictFDerivAt_zero source J g q
  have htangent : D.symm (controlledTargetDirection source) = u := by
    exact augmentedSteadyContinuousLinearEquiv_symm_controlledTargetDirection
      source (literalCurrentJacobian source J g q) hreduced u hkernel hcontrol
  have hderiv := inverseFunctionBranch_hasStrictFDerivAt
    (augmentedLogStationarity source J g q) 0 D hD (controlledTargetDirection source)
  have hmap : ((D.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).comp
      (scalarDirectionMap (controlledTargetDirection source))) = scalarDirectionMap u := by
    ext s
    simp [scalarDirectionMap, htangent]
  rw [hmap] at hderiv
  exact hderiv

theorem reconstructedLogReactionCurrent_comp_hasStrictFDerivAt_zero
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (z : ℝ → (Fin n → ℝ)) (u : Fin n → ℝ)
    (hz0 : z 0 = 0) (hz : HasStrictFDerivAt z (scalarDirectionMap u) 0)
    (hkernel : (literalCurrentJacobian source J g q).mulVec u = 0) :
    HasStrictFDerivAt
      (fun s => reconstructedLogReactionCurrent source J g q (z s))
      (0 : ℝ →L[ℝ] (Fin n → ℝ)) 0 := by
  have hcurrent := reconstructedLogReactionCurrent_hasStrictFDerivAt_zero source J g q
  have hcurrentAt : HasStrictFDerivAt (reconstructedLogReactionCurrent source J g q)
      (matrixContinuousLinearMap (literalCurrentJacobian source J g q)) (z 0) := by
    simpa [hz0] using hcurrent
  have hcomp := hcurrentAt.comp 0 hz
  convert hcomp using 1
  ext s
  simp [scalarDirectionMap, hkernel]

structure LocalPositiveLogBranch {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ) : Type where
  branch : ℝ → (Fin n → ℝ)
  atZero : branch 0 = 0
  tendstoZero : Tendsto branch (𝓝 0) (𝓝 0)
  eventuallyControlled : ∀ᶠ s in 𝓝 (0 : ℝ), branch s source.controlled = s
  eventuallyStationary : ∀ᶠ s in 𝓝 (0 : ℝ),
    ∀ i, i ≠ source.controlled → reconstructedLogSourceDrift source J g q (branch s) i = 0
  positiveForward : ∀ s i, 0 < reconstructedLogForwardFlow source J g q (branch s) i
  positiveReverse : ∀ s i, 0 < reconstructedLogReverseFlow source J g q (branch s) i

theorem exists_localPositiveLogBranch {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hmode : ControlledProductionMode source g)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q)) :
    Nonempty (LocalPositiveLogBranch source J g q) := by
  refine ⟨?_⟩
  let F := augmentedLogStationarity source J g q
  let D := augmentedSteadyContinuousLinearEquiv source
    (literalCurrentJacobian source J g q) hreduced
  have hD : HasStrictFDerivAt F (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0 := by
    simpa [F, D] using augmentedLogStationarity_hasStrictFDerivAt_zero source J g q
  let direction := controlledTargetDirection source
  let z := inverseFunctionBranch F 0 D hD direction
  have hFzero : F 0 = 0 := by
    exact augmentedLogStationarity_zero source J g q hJ hg hq hmode
  have heqRaw := inverseFunctionBranch_eventually_equation F 0 D hD direction
  have heq : ∀ᶠ s in 𝓝 (0 : ℝ), F (z s) = s • direction := by
    filter_upwards [heqRaw] with s hs
    rw [hFzero, zero_add] at hs
    exact hs
  refine {
    branch := z
    atZero := inverseFunctionBranch_zero F 0 D hD direction
    tendstoZero := inverseFunctionBranch_tendsto F 0 D hD direction
    eventuallyControlled := ?_
    eventuallyStationary := ?_
    positiveForward := ?_
    positiveReverse := ?_
  }
  · filter_upwards [heq] with s hs
    have hc := congrFun hs source.controlled
    simpa [F, augmentedLogStationarity, direction, controlledTargetDirection] using hc
  · filter_upwards [heq] with s hs
    intro i hi
    have hrow := congrFun hs i
    simpa [F, augmentedLogStationarity, hi, direction, controlledTargetDirection] using hrow
  · intro s i
    exact (reconstructedLogFlows_positive source J g q (z s) hJ hg hq).1 i
  · intro s i
    exact (reconstructedLogFlows_positive source J g q (z s) hJ hg hq).2 i

end
end OptimalAffinityRealizability
