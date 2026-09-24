import proofs.CoreCouplingGlobal.PerronRecovery
import proofs.CoreCouplingGlobal.QuadraticImplicit
import Mathlib.Analysis.Normed.Operator.Mul

namespace CoreCouplingGlobal
open Filter
open scoped BoundedContinuousFunction Topology ContDiff

abbrev PerronSpace := Fin 4 → (ℝ →ᵇ ℝ)
abbrev StableData := Fin 3 → ℝ

noncomputable local instance : NormedAddCommGroup PerronSpace := inferInstance
noncomputable local instance : NormedSpace ℝ PerronSpace := inferInstance
local instance : CompleteSpace PerronSpace := inferInstance

noncomputable def clampOperator : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) where
  toFun f := f.compContinuous nonnegativeTime
  map_add' f g := by ext t; rfl
  map_smul' a f := by ext t; rfl
  cont := BoundedContinuousFunction.continuous_compContinuous nonnegativeTime

noncomputable def perronGreen (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β) :
    PerronSpace →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi fun i => if hi : i=3 then
    -((clampOperator.comp (exponentialGreenOperator (μ i+β) 1 (by simpa [hi] using hu))).comp
      (ContinuousLinearMap.proj i))
    else (pastZeroOperator (-(μ i+β)) (neg_pos.mpr (hs i hi))).comp
      (ContinuousLinearMap.proj i)

noncomputable def perronLinear (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) : StableData →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi (Fin.lastCases 0 fun i : Fin 3 =>
    (ContinuousLinearMap.proj i).smulRight
      (decayingProfile (-(μ i.castSucc+β)) (neg_pos.mpr
        (hs i.castSucc (by simpa using i.castSucc_ne_last)))))

noncomputable def trajectoryMonomial (j k : Fin 4) :
    PerronSpace →L[ℝ] PerronSpace →L[ℝ] (ℝ →ᵇ ℝ) :=
  (ContinuousLinearMap.mul ℝ (ℝ →ᵇ ℝ)).bilinearComp
    (ContinuousLinearMap.proj j) (ContinuousLinearMap.proj k)

/-- Exact weighted pointwise quadratic forcing, assembled as a continuous
bilinear map on the complete trajectory space. -/
noncomputable def weightedTrajectoryBilinear (β : ℝ) (hβ : 0 < β)
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace := by
  letI : AddCommMonoid (PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace) :=
    (inferInstance : NormedAddCommGroup
      (PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace)).toAddCommGroup.toAddCommMonoid
  exact ∑ i, ∑ j, ∑ k, q i j k •
    ((ContinuousLinearMap.compL ℝ PerronSpace (ℝ →ᵇ ℝ) PerronSpace
      ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ →ᵇ ℝ) i).comp
        (ContinuousLinearMap.mul ℝ (ℝ →ᵇ ℝ) (decayingProfile β hβ)))).comp
      (trajectoryMonomial j k))

theorem weightedTrajectoryBilinear_apply (β : ℝ) (hβ : 0 < β)
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) (v w : PerronSpace) (t : ℝ) (i : Fin 4) :
    weightedTrajectoryBilinear β hβ q v w i t =
      Real.exp (-β*max t 0)*(∑ j, ∑ k, q i j k*v j t*w k t) := by
  simp [weightedTrajectoryBilinear,trajectoryMonomial,decayingProfile,
    Finset.mul_sum,Pi.single_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- This constructs the nonlinear weighted integral solution rather than
assuming the existence of self-consistent forcing. ODE and chart coverage are
separate bindings to this actual solution. -/
theorem perron_equation_local_solution (μ : Fin 4 → ℝ) (β : ℝ) (hβ : 0 < β)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (q : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∃ ψ : StableData → PerronSpace, ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧
      HasFDerivAt ψ (perronLinear μ β hs) 0 ∧
      ∀ᶠ ξ in 𝓝 (0:StableData), ψ ξ=perronLinear μ β hs ξ+
        perronGreen μ β hs hu (weightedTrajectoryBilinear β hβ q (ψ ξ) (ψ ξ)) := by
  let G := perronGreen μ β hs hu
  let B := weightedTrajectoryBilinear β hβ q
  let GB : PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace :=
    (ContinuousLinearMap.compL ℝ PerronSpace PerronSpace PerronSpace G).comp B
  obtain ⟨ψ,hzero,hcd,hd,heq,_⟩ := quadratic_implicit_solution (perronLinear μ β hs) GB
  exact ⟨ψ,hzero,hcd,hd,heq⟩

theorem perronLinear_stable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0)
    (ξ : StableData) (i : Fin 3) (t : ℝ) (ht : 0 ≤ t) :
    perronLinear μ β hs ξ i.castSucc t=Real.exp ((μ i.castSucc+β)*t)*ξ i := by
  simp [perronLinear,decayingProfile,max_eq_left ht,mul_comm]

theorem perronLinear_unstable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (ξ : StableData) (t : ℝ) :
    perronLinear μ β hs ξ 3 t=0 := by
  unfold perronLinear
  change (Fin.lastCases (motive := fun _ => StableData →L[ℝ] (ℝ →ᵇ ℝ))
    0 (fun i : Fin 3 => (ContinuousLinearMap.proj i).smulRight
      (decayingProfile (-(μ i.castSucc+β)) (neg_pos.mpr
        (hs i.castSucc (by simpa using i.castSucc_ne_last))))) (Fin.last 3)) ξ t=0
  rw [Fin.lastCases_last]
  rfl

theorem perronGreen_stable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (f : PerronSpace) (i : Fin 3) (t : ℝ) (ht : 0 ≤ t) :
    perronGreen μ β hs hu f i.castSucc t=
      uncutPastTrajectory (-(μ i.castSucc+β)) (f i.castSucc) t := by
  have hi : i.castSucc ≠ (3 : Fin 4) := by simpa using i.castSucc_ne_last
  simpa [perronGreen,hi,pastZeroOperator] using
    (uncutPastTrajectory_agrees (-(μ i.castSucc+β))
      (neg_pos.mpr (hs i.castSucc hi)) (f i.castSucc) t ht).symm

theorem perronGreen_unstable (μ : Fin 4 → ℝ) (β : ℝ)
    (hs : ∀ i : Fin 4, i ≠ 3 → μ i+β < 0) (hu : 0 < μ 3+β)
    (f : PerronSpace) (t : ℝ) (ht : 0 ≤ t) :
    perronGreen μ β hs hu f 3 t=-exponentialAverage (μ 3+β) 1 (f 3) t := by
  simp [perronGreen,clampOperator,nonnegativeTime,max_eq_left ht,
    exponentialGreenOperator,exponentialAverageBCF]

end CoreCouplingGlobal
