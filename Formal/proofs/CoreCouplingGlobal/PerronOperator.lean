import proofs.CoreCouplingGlobal.PerronKernels
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace CoreCouplingGlobal
open Set MeasureTheory Filter
open scoped BoundedContinuousFunction

/-- A translated exponential convolution. Direction 1 is the future Green
operator; direction -1 is the past convolution used before imposing initial data. -/
noncomputable def exponentialAverage (ν direction : ℝ) (f : ℝ →ᵇ ℝ) (t : ℝ) : ℝ :=
  ∫ s in Ioi (0:ℝ), Real.exp ((-ν)*s)*f (t+direction*s)

theorem exponentialAverage_integrable (ν direction : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) (t : ℝ) :
    IntegrableOn (fun s => Real.exp ((-ν)*s)*f (t+direction*s)) (Ioi (0:ℝ)) := by
  apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hν) 0).mul_bdd
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall (fun s => f.norm_coe_le_norm (t+direction*s))

theorem exponentialAverage_bound (ν direction : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) (t : ℝ) : ‖exponentialAverage ν direction f t‖ ≤ ‖f‖/ν := by
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hν) 0).mul_const ‖f‖
  have hb : ∀ s : ℝ, ‖Real.exp ((-ν)*s)*f (t+direction*s)‖ ≤ Real.exp ((-ν)*s)*‖f‖ := by
    intro s
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (Real.exp_pos _).le
  have h := norm_integral_le_of_norm_le hi (Eventually.of_forall hb)
  change ‖exponentialAverage ν direction f t‖ ≤ _ at h
  rw [integral_mul_const,integral_exp_mul_Ioi (neg_neg_of_pos hν)] at h
  norm_num at h
  convert h using 1
  ring

theorem exponentialAverage_continuous (ν direction : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) : Continuous (exponentialAverage ν direction f) := by
  unfold exponentialAverage
  apply continuous_of_dominated
    (bound := fun s : ℝ => Real.exp ((-ν)*s)*‖f‖)
  · intro t
    exact ((Real.continuous_exp.comp (by fun_prop)).mul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro t
    filter_upwards [] with s
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (Real.exp_pos _).le
  · exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hν) 0).mul_const ‖f‖
  · filter_upwards [] with s
    exact continuous_const.mul (f.continuous.comp (by fun_prop))

noncomputable def exponentialAverageBCF (ν direction : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (exponentialAverage ν direction f)
    (exponentialAverage_continuous ν direction hν f) (‖f‖/ν)
    (exponentialAverage_bound ν direction hν f)

theorem exponentialAverageBCF_norm (ν direction : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) : ‖exponentialAverageBCF ν direction hν f‖ ≤ (1/ν)*‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro t
  change ‖exponentialAverage ν direction f t‖ ≤ _
  convert exponentialAverage_bound ν direction hν f t using 1
  ring

/-- The actual bounded continuous Green operator, linear in its forcing. -/
noncomputable def exponentialGreenOperator (ν direction : ℝ) (hν : 0 < ν) :
    (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := exponentialAverageBCF ν direction hν
      map_add' := by
        intro f g
        ext t
        change exponentialAverage ν direction (f+g) t=
          exponentialAverage ν direction f t+exponentialAverage ν direction g t
        unfold exponentialAverage
        simp only [BoundedContinuousFunction.add_apply,mul_add]
        exact integral_add (exponentialAverage_integrable ν direction hν f t)
          (exponentialAverage_integrable ν direction hν g t)
      map_smul' := by
        intro a f
        ext t
        change exponentialAverage ν direction (a • f) t=a*exponentialAverage ν direction f t
        unfold exponentialAverage
        simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with s
        ring }
    (1/ν) (exponentialAverageBCF_norm ν direction hν)

theorem exponentialGreenOperator_norm (ν direction : ℝ) (hν : 0 < ν) :
    ‖exponentialGreenOperator ν direction hν‖ ≤ 1/ν := by
  exact ContinuousLinearMap.opNorm_le_bound (exponentialGreenOperator ν direction hν)
    (by positivity) (exponentialAverageBCF_norm ν direction hν)

end CoreCouplingGlobal
