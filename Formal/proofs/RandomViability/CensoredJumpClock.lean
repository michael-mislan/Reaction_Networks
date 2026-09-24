import proofs.RandomViability.CensoredExponentialClock
import proofs.RandomViability.CollectiveClockTilt

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 80000

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def censoredClockWeight (w : β → ℝ) (s T : ℝ) (y : β × ℝ) : ℝ≥0∞ :=
  if y.2 ≤ T then ENNReal.ofReal (w y.1)*ENNReal.ofReal (Real.exp (-s*y.2))
    else ENNReal.ofReal (Real.exp (-s*T))

theorem censoredClockWeight_measurable (w : β → ℝ) (s T : ℝ) :
    Measurable (censoredClockWeight w s T) := by
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const)
    (((measurable_of_countable w).comp measurable_fst).ennreal_ofReal.mul (by fun_prop)) measurable_const

theorem jumpClock_censored_integral (a : β → ℝ) (ha : ∀ i,0 ≤ a i)
    (hr : 0 < ∑ i,a i) (w : β → ℝ) (hw : ∀ i,0 ≤ w i) (s T : ℝ)
    (hu : 0 < (∑ i,a i)+s) (hT : 0 ≤ T) :
    (∫⁻ y,censoredClockWeight w s T y ∂jumpClockMeasure a ha hr) =
      ENNReal.ofReal (((∑ i,a i*w i)/((∑ i,a i)+s)) *
        (1-Real.exp (-((∑ i,a i)+s)*T))+Real.exp (-((∑ i,a i)+s)*T)) := by
  letI := isProbabilityMeasure_expMeasure hr
  rw [jumpClockMeasure,lintegral_prod _ (censoredClockWeight_measurable w s T).aemeasurable]
  simp only [censoredClockWeight]
  simp_rw [exponential_censored_weight_integral _ s T _ hr hu hT (hw _)]
  have hE : 0 ≤ 1-Real.exp (-((∑ i,a i)+s)*T) := by
    have h := Real.exp_le_one_iff.mpr (show -((∑ i,a i)+s)*T ≤ 0 by nlinarith)
    linarith
  rw [jumpLabel_weight_integral a ha hr
    (fun i => w i*(∑ j,a j)/((∑ j,a j)+s)*(1-Real.exp (-((∑ j,a j)+s)*T))+
      Real.exp (-((∑ j,a j)+s)*T))
    (fun i => add_nonneg (mul_nonneg (div_nonneg (mul_nonneg (hw i) hr.le) hu.le) hE)
      (Real.exp_pos _).le)]
  congr 1
  simp only [mul_add,Finset.sum_add_distrib]
  simp_rw [show ∀ i,a i*(w i*(∑ j,a j)/((∑ j,a j)+s)*
      (1-Real.exp (-((∑ j,a j)+s)*T))) =
      (a i*w i)*((∑ j,a j)/((∑ j,a j)+s)*(1-Real.exp (-((∑ j,a j)+s)*T))) by intro i; ring]
  rw [← Finset.sum_mul,← Finset.sum_mul]
  field_simp

theorem jumpClock_censored_tilt_le_one (a d : β → ℝ) (ha : ∀ i,0 ≤ a i)
    (hr : 0 < ∑ i,a i) (θ s T : ℝ) (hT : 0 ≤ T)
    (hs : (∑ i,a i*(Real.exp (θ*d i)-1)) ≤ s) :
    (∫⁻ y,censoredClockWeight (fun i => Real.exp (θ*d i)) s T y
      ∂jumpClockMeasure a ha hr) ≤ 1 := by
  have he : (∑ i,a i*Real.exp (θ*d i))-(∑ i,a i) =
      ∑ i,a i*(Real.exp (θ*d i)-1) := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
  have hb : (∑ i,a i*Real.exp (θ*d i)) ≤ (∑ i,a i)+s := by linarith
  have hu : 0 < (∑ i,a i)+s := (tilted_total_positive a d ha hr θ).trans_le hb
  rw [jumpClock_censored_integral a ha hr _ (fun _ => (Real.exp_pos _).le) s T hu hT]
  apply ENNReal.ofReal_le_one.mpr
  have hE : 0 ≤ 1-Real.exp (-((∑ i,a i)+s)*T) := by
    have h := Real.exp_le_one_iff.mpr (show -((∑ i,a i)+s)*T ≤ 0 by nlinarith)
    linarith
  have hq := (div_le_one hu).mpr hb
  nlinarith [mul_le_mul_of_nonneg_right hq hE]

def censoredJumpMultiplier {α : Type*} (w : β → ℝ) (s T : ℝ) (y : JumpState α β) : ℝ≥0∞ :=
  if y.2.2 ≤ T then jumpMultiplier w s y else ENNReal.ofReal (Real.exp (-s*T))

theorem censoredJumpMultiplier_measurable {α : Type*} [MeasurableSpace α]
    (w : β → ℝ) (s T : ℝ) : Measurable (censoredJumpMultiplier (α := α) w s T) :=
  Measurable.ite (measurableSet_le measurable_snd.snd measurable_const)
    (jumpMultiplier_measurable w s) measurable_const

theorem jumpState_censored_tilt_le_one {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x i,0 ≤ rate x i) (ht : ∀ x,0 < ∑ i,rate x i)
    (x : α) (d : β → ℝ) (θ s T : ℝ) (hT : 0 ≤ T)
    (hs : (∑ i,rate x i*(Real.exp (θ*d i)-1)) ≤ s) :
    (∫⁻ y,censoredJumpMultiplier (fun i => Real.exp (θ*d i)) s T y
      ∂jumpStateKernel next rate hr ht x) ≤ 1 := by
  change (∫⁻ y,censoredJumpMultiplier (fun i => Real.exp (θ*d i)) s T y
    ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x)) ≤ 1
  rw [lintegral_map (censoredJumpMultiplier_measurable _ _ _) (jumpStateUpdate_measurable next x)]
  exact jumpClock_censored_tilt_le_one (rate x) d (hr x) (ht x) θ s T hT hs

end
end RandomViability
