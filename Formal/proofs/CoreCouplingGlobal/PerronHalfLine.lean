import proofs.CoreCouplingGlobal.PerronOperator

namespace CoreCouplingGlobal
open Set
open scoped BoundedContinuousFunction

noncomputable def nonnegativeTime : C(ℝ,ℝ) := ⟨fun t => max t 0,by fun_prop⟩

noncomputable def decayingProfile (ν : ℝ) (hν : 0 < ν) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => Real.exp (-ν*max t 0))
    (by fun_prop) 1 (by
      intro t
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hν.le) (le_max_right _ _))

theorem decayingProfile_norm (ν : ℝ) (hν : 0 < ν) : ‖decayingProfile ν hν‖ ≤ 1 := by
  apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
  norm_num

noncomputable def pastZeroTrajectory (ν : ℝ) (hν : 0 < ν) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  (exponentialGreenOperator ν (-1) hν f).compContinuous nonnegativeTime -
    (exponentialGreenOperator ν (-1) hν f 0) • decayingProfile ν hν

theorem pastZeroTrajectory_zero (ν : ℝ) (hν : 0 < ν) (f : ℝ →ᵇ ℝ) :
    pastZeroTrajectory ν hν f 0=0 := by
  simp [pastZeroTrajectory,nonnegativeTime,decayingProfile]

theorem pastZeroTrajectory_norm (ν : ℝ) (hν : 0 < ν) (f : ℝ →ᵇ ℝ) :
    ‖pastZeroTrajectory ν hν f‖ ≤ (2/ν)*‖f‖ := by
  let v := exponentialGreenOperator ν (-1) hν f
  have hv : ‖v‖ ≤ (1/ν)*‖f‖ := exponentialAverageBCF_norm ν (-1) hν f
  have hc := v.norm_compContinuous_le nonnegativeTime
  have h0 := v.norm_coe_le_norm 0
  have he := decayingProfile_norm ν hν
  have hm : ‖v 0 • decayingProfile ν hν‖ ≤ ‖v‖ := by
    rw [norm_smul]
    calc
      ‖v 0‖*‖decayingProfile ν hν‖ ≤ ‖v 0‖*1 :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ ‖v‖ := by simpa using h0
  have hsub := norm_sub_le (v.compContinuous nonnegativeTime) (v 0 • decayingProfile ν hν)
  change ‖pastZeroTrajectory ν hν f‖ ≤ _ at hsub
  calc
    ‖pastZeroTrajectory ν hν f‖ ≤ 2*((1/ν)*‖f‖) := by linarith
    _ = (2/ν)*‖f‖ := by ring

/-- Past exponential convolution with its initial value removed. The full-real
domain is a convenience; nonnegativeTime makes the output constant before zero. -/
noncomputable def pastZeroOperator (ν : ℝ) (hν : 0 < ν) :
    (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := pastZeroTrajectory ν hν
      map_add' := by
        intro f g
        ext t
        simp [pastZeroTrajectory,map_add,add_smul]
        ring
      map_smul' := by
        intro a f
        ext t
        simp [pastZeroTrajectory,map_smul,smul_eq_mul]
        ring }
    (2/ν) (pastZeroTrajectory_norm ν hν)

theorem pastZeroOperator_norm (ν : ℝ) (hν : 0 < ν) :
    ‖pastZeroOperator ν hν‖ ≤ 2/ν := by
  exact ContinuousLinearMap.opNorm_le_bound (pastZeroOperator ν hν)
    (by positivity) (pastZeroTrajectory_norm ν hν)

end CoreCouplingGlobal
