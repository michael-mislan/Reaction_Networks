import proofs.RandomViability.CollectiveGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option maxHeartbeats 20000

namespace RandomViability
open Filter Set
open scoped Topology

theorem squared_foodDeficit_hasDerivAt (u : ℝ) :
    HasDerivAt (fun v => (foodDeficit v)^2) (-2*foodDeficit u) u := by
  have hpoly (v : ℝ) : HasDerivAt (fun y : ℝ => (1-y)^2) (-2*(1-v)) v := by
    convert (((hasDerivAt_id v).const_sub 1).pow 2) using 1
    simp only [id_eq]
    ring
  rcases lt_trichotomy u 1 with h | h | h
  · have he : (fun v => (foodDeficit v)^2) =ᶠ[𝓝 u] (fun v => (1-v)^2) := by
      filter_upwards [eventually_lt_nhds h] with v hv
      simp [foodDeficit, max_eq_left (by linarith : 0 ≤ 1-v)]
    rw [show foodDeficit u = 1-u from max_eq_left (by linarith)]
    exact (hpoly u).congr_of_eventuallyEq he
  · subst u
    rw [show foodDeficit 1 = 0 by norm_num [foodDeficit], mul_zero]
    apply hasDerivAt_iff_tendsto_slope_left_right.2
    constructor
    · have hp := (hpoly 1).tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)
      simp only [sub_self, mul_zero] at hp
      apply hp.congr'
      filter_upwards [self_mem_nhdsWithin] with v hv
      simp only [mem_Iio] at hv
      simp [slope, foodDeficit, max_eq_left (by linarith : 0 ≤ 1-v)]
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with v hv
      simp only [mem_Ioi] at hv
      simp [slope, foodDeficit, max_eq_right (by linarith : 1-v ≤ 0)]
  · have he : (fun v => (foodDeficit v)^2) =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_nhds h] with v hv
      simp [foodDeficit, max_eq_right (by linarith : 1-v ≤ 0)]
    rw [show foodDeficit u = 0 from max_eq_right (by linarith), mul_zero]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq he

noncomputable def collectivePotential (u w x : ℝ) : ℝ :=
  Real.log x-4*((foodDeficit u)^2+(foodDeficit w)^2)

theorem collectivePotential_hasDerivAt (u w x : ℝ → ℝ) (t du dw dx : ℝ)
    (hu : HasDerivAt u du t) (hw : HasDerivAt w dw t)
    (hx : HasDerivAt x dx t) (hx0 : x t ≠ 0) :
    HasDerivAt (fun s => collectivePotential (u s) (w s) (x s))
      (dx/x t-4*(-2*foodDeficit (u t)*du-2*foodDeficit (w t)*dw)) t := by
  have h1 := (squared_foodDeficit_hasDerivAt (u t)).comp t hu
  have h2 := (squared_foodDeficit_hasDerivAt (w t)).comp t hw
  convert (hx.log hx0).sub ((h1.add h2).const_mul 4) using 1
  ring

/-- Time-integrated certificate; only M, not the derivative, needs an
integrability hypothesis. This keeps the later stochastic analogue local. -/
theorem collective_integrated_growth (P dP M : ℝ → ℝ) (a b eps : ℝ)
    (hab : a ≤ b) (hP : ∀ t ∈ Icc a b, HasDerivAt P (dP t) t)
    (hM : ContinuousOn M (Icc a b))
    (hbound : ∀ t ∈ Ioo a b, 2-468*eps-624*M t ≤ dP t) :
    (b-a)*(2-468*eps)-624*(∫ t in a..b, M t) ≤ P b-P a := by
  have hcont : ContinuousOn P (Icc a b) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hf : ContinuousOn (fun t => 2-468*eps-624*M t) (Icc a b) :=
    continuousOn_const.sub (continuousOn_const.mul hM)
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hcont
    (fun t ht => (hP t ⟨ht.1.le,ht.2.le⟩).hasDerivWithinAt)
    hf.integrableOn_Icc hbound
  have hMi : IntervalIntegrable M MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hM
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hMi.const_mul 624),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at h
  simpa only [smul_eq_mul] using h

end RandomViability
