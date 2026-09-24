import proofs.CoreCouplingGlobal.FinitePerronOperators

namespace CoreCouplingGlobal
open Set
open scoped Topology BoundedContinuousFunction

theorem finite_reference_exists (T : ℝ) (hT : 0 ≤ T) (X : ℝ → ResponseVector)
    (hX : ContinuousOn X (Icc 0 T)) :
    ∃ a : PerronSpace, ∀ t i, a i t=X (finiteTime T t) i := by
  have hc : Continuous (fun t => X (finiteTime T t)) :=
    hX.comp_continuous (finiteTime T).continuous (finiteTime_mem T hT)
  obtain ⟨R,hR⟩ := (isCompact_Icc.image_of_continuousOn hX).isBounded.subset_closedBall
    (0 : ResponseVector)
  have hb : ∀ t, ‖X (finiteTime T t)‖ ≤ R := by
    intro t
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      hR ⟨finiteTime T t,finiteTime_mem T hT t,rfl⟩
  let a : PerronSpace := fun i => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => X (finiteTime T t) i) ((continuous_apply i).comp hc) R
    (fun t => (norm_le_pi_norm _ i).trans (hb t))
  exact ⟨a,fun _ _ => rfl⟩

noncomputable def trajectoryMatrix (m : Fin 4 → Fin 4 → (ℝ →ᵇ ℝ)) :
    PerronSpace →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi fun i => ∑ j,
    (ContinuousLinearMap.mul ℝ (ℝ →ᵇ ℝ) (m i j)).comp (ContinuousLinearMap.proj j)

theorem trajectoryMatrix_apply (m : Fin 4 → Fin 4 → (ℝ →ᵇ ℝ))
    (v : PerronSpace) (t : ℝ) (i : Fin 4) :
    trajectoryMatrix m v i t=∑ j, m i j t*v j t := by
  simp [trajectoryMatrix]

noncomputable def physicalTrajectoryMatrix (e σ : ℝ) (a : PerronSpace) :
    Fin 4 → Fin 4 → (ℝ →ᵇ ℝ) :=
  σ • !![BoundedContinuousFunction.const ℝ (-2)-(4*e) • a 0,
      a 2+BoundedContinuousFunction.const ℝ (2*e),a 1,0;
    BoundedContinuousFunction.const ℝ 1+(2*e) • a 0,
      BoundedContinuousFunction.const ℝ (-1-e)-a 2,-a 1,0;
    BoundedContinuousFunction.const ℝ 1,-a 2,
      -a 1-BoundedContinuousFunction.const ℝ 16-8 • a 2,BoundedContinuousFunction.const ℝ 3;
    0,0,BoundedContinuousFunction.const ℝ 16+4 • a 2,
      BoundedContinuousFunction.const ℝ (-(20001/10000))]

theorem physicalTrajectoryMatrix_apply (e σ : ℝ) (a v : PerronSpace) (t : ℝ) :
    (fun i => trajectoryMatrix (physicalTrajectoryMatrix e σ a) v i t)=
      σ • (physicalJacobian e (fun i => a i t)).toLin' (fun i => v i t) := by
  ext i
  fin_cases i <;> simp [trajectoryMatrix_apply,physicalTrajectoryMatrix,
    physicalJacobian,dotProduct,Fin.sum_univ_succ] <;> ring

noncomputable local instance : NormedAddCommGroup PerronSpace := inferInstance
noncomputable local instance : NormedSpace ℝ PerronSpace := inferInstance

noncomputable def trajectoryBilinear (q : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace := by
  letI : AddCommMonoid (PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace) :=
    (inferInstance : NormedAddCommGroup
      (PerronSpace →L[ℝ] PerronSpace →L[ℝ] PerronSpace)).toAddCommGroup.toAddCommMonoid
  exact ∑ i, ∑ j, ∑ k, q i j k •
    ((ContinuousLinearMap.compL ℝ PerronSpace (ℝ →ᵇ ℝ) PerronSpace
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ →ᵇ ℝ) i)).comp (trajectoryMonomial j k))

theorem trajectoryBilinear_apply (q : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (v w : PerronSpace) (t : ℝ) (i : Fin 4) :
    trajectoryBilinear q v w i t=∑ j, ∑ k, q i j k*v j t*w k t := by
  simp [trajectoryBilinear,trajectoryMonomial,Pi.single_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  ring

end CoreCouplingGlobal
