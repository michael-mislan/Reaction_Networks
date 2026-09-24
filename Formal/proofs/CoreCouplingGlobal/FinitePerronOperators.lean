import proofs.CoreCouplingGlobal.PerronChart
import proofs.CoreCouplingGlobal.LinearQuadraticImplicit

namespace CoreCouplingGlobal
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

noncomputable def allPastGreen (k : ℝ) (hk : 0 < k) : PerronSpace →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi fun i => (pastZeroOperator k hk).comp (ContinuousLinearMap.proj i)

theorem allPastGreen_bound (k : ℝ) (hk : 0 < k) (v : PerronSpace) :
    ‖allPastGreen k hk v‖ ≤ (2/k)*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  exact (pastZeroTrajectory_norm k hk (v i)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (by positivity))

theorem allPastGreen_norm (k : ℝ) (hk : 0 < k) : ‖allPastGreen k hk‖ ≤ 2/k :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (allPastGreen_bound k hk)

noncomputable def allPastLinear (k : ℝ) (hk : 0 < k) : ResponseVector →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i).smulRight (decayingProfile k hk)

theorem allPastLinear_apply (k : ℝ) (hk : 0 < k) (ξ : ResponseVector)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 4) :
    allPastLinear k hk ξ i t=Real.exp (-k*t)*ξ i := by
  simp [allPastLinear,decayingProfile,max_eq_left ht,mul_comm]

noncomputable def finiteTime (T : ℝ) : C(ℝ,ℝ) := ⟨fun t => min (max t 0) T,by fun_prop⟩

theorem finiteTime_mem (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : finiteTime T t ∈ Icc 0 T :=
  ⟨le_min (le_max_right _ _) hT,min_le_right _ _⟩

theorem finiteTime_eq (T t : ℝ) (ht : t ∈ Icc 0 T) : finiteTime T t=t := by
  simp [finiteTime,max_eq_left ht.1,min_eq_left ht.2]

noncomputable def finiteGrowth (k T : ℝ) (hk : 0 < k) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => Real.exp (k*finiteTime T t))
    (by fun_prop) (Real.exp (k*T)) (by
      intro t
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right _ _) hk.le))

noncomputable def trajectoryScale (g : ℝ →ᵇ ℝ) : PerronSpace →L[ℝ] PerronSpace :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.mul ℝ (ℝ →ᵇ ℝ) g).comp (ContinuousLinearMap.proj i)

/-- The exponential weight can always dominate a bounded linear trajectory
operator, even when the underlying reference time interval is not short. -/
theorem allPast_linear_contractive (H : PerronSpace →L[ℝ] PerronSpace) :
    ∃ k : ℝ, ∃ hk : 0 < k, ‖(allPastGreen k hk).comp H‖ < 1 := by
  let k := 4*(‖H‖+1)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k,hk,?_⟩
  have hbound := (allPastGreen k hk).opNorm_comp_le H
  have hbound' := mul_le_mul_of_nonneg_right (allPastGreen_norm k hk) (norm_nonneg H)
  apply (hbound.trans hbound').trans_lt
  have hlt : 2*‖H‖ < k := by dsimp [k]; linarith [norm_nonneg H]
  have hratio : (2*‖H‖)/k < 1 := (div_lt_one hk).2 hlt
  simpa only [div_mul_eq_mul_div] using hratio

end CoreCouplingGlobal
