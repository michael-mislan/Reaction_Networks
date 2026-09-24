import proofs.InheritedCellAssay.PositiveHorizon
import proofs.InheritedCellAssay.ScalarIntegralLink

namespace InheritedCellAssay.PositiveMoments
open ScalarRateSource

noncomputable def clock (x : ℝ) : ℝ := 10*Real.log (1+x)
noncomputable def baseMean (x : ℝ) : ℝ := (19/24)/(1+x)^3+(5/24)*(1+x)
noncomputable def totalMean (M : MomentODE) (x : ℝ) : ℝ := M.S (clock x)+M.R (clock x)
noncomputable def birthDensity (M : MomentODE) (x : ℝ) : ℝ :=
  M.R (clock x)/((1+x)*(totalMean M x)^2)

theorem clock_bounds (x : ℝ) (hx : x ∈ Set.Icc 0 1) : clock x ∈ Set.Icc 0 7 := by
  have hl : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith [hx.1])
  have hu : Real.log (1+x) ≤ Real.log 2 := Real.log_le_log (by linarith [hx.1]) (by linarith [hx.2])
  have hh := log_two_upper
  unfold clock
  constructor <;> linarith

theorem clock_exp (x : ℝ) (hx : 0 ≤ x) :
    Real.exp ((1/10)*clock x) = 1+x ∧ Real.exp (-(3/10)*clock x) = 1/(1+x)^3 := by
  have hy : 0 < 1+x := by linarith
  constructor
  · have he : (1/10)*clock x = Real.log (1+x) := by unfold clock; ring
    rw [he, Real.exp_log hy]
  · have he : -(3/10)*clock x = -(Real.log (1+x)+Real.log (1+x)+Real.log (1+x)) := by
      unfold clock
      ring
    rw [he, Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_log hy]
    ring

theorem baseMean_pos (x : ℝ) (hx : 0 ≤ x) : 0 < baseMean x := by
  unfold baseMean
  positivity

theorem clock_moment_bounds (M : MomentODE) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    M.R (clock x) ≤ (26/25)*(5/24)*(1+x) ∧
    (993/1000)*baseMean x ≤ totalMean M x := by
  have hr := resistant_upper M (clock x) (clock_bounds x hx)
  have hl := total_lower M (clock x) (clock_bounds x hx)
  obtain ⟨hb,hd⟩ := clock_exp x hx.1
  rw [hb] at hr
  rw [hb,hd] at hl
  exact ⟨hr, by simpa only [baseMean,totalMean,mul_one_div] using hl⟩

theorem totalMean_pos (M : MomentODE) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    0 < totalMean M x :=
  lt_of_lt_of_le (mul_pos (by norm_num) (baseMean_pos x hx.1)) (clock_moment_bounds M x hx).2

noncomputable def densityFactor : ℝ := (26/25)/(993/1000)^2*(64/33)

theorem birthDensity_bound (M : MomentODE) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    0 ≤ birthDensity M x ∧ birthDensity M x ≤ densityFactor*rateMass x := by
  have hy : 0 < 1+x := by linarith [hx.1]
  have hm := totalMean_pos M x hx
  have hb := baseMean_pos x hx.1
  have hr := M.nonnegR (clock x) (clock_bounds x hx).1
  obtain ⟨hRu,hMl⟩ := clock_moment_bounds M x hx
  have hsq : ((993/1000)*baseMean x)^2 ≤ (totalMean M x)^2 := by nlinarith
  constructor
  · unfold birthDensity
    positivity
  · calc
      birthDensity M x ≤ ((26/25)*(5/24)*(1+x))/((1+x)*(totalMean M x)^2) :=
        div_le_div_of_nonneg_right hRu (by positivity)
      _ ≤ ((26/25)*(5/24)*(1+x))/((1+x)*((993/1000)*baseMean x)^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hsq hy.le)
      _ = densityFactor*rateMass x := by
        unfold baseMean densityFactor rateMass den
        have hD := ne_of_gt (den_pos x)
        unfold den at hD
        field_simp [ne_of_gt hy, hD]
        ring

theorem birthDensity_continuous (M : MomentODE) : ContinuousOn (birthDensity M) (Set.Icc 0 1) := by
  have hS : Continuous M.S := continuous_iff_continuousAt.mpr (fun x => (M.derivS x).continuousAt)
  have hR : Continuous M.R := continuous_iff_continuousAt.mpr (fun x => (M.derivR x).continuousAt)
  have ht : ContinuousOn clock (Set.Icc 0 1) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
    intro x hx
    change 1+x ≠ 0
    linarith [hx.1]
  apply ContinuousOn.div (hR.comp_continuousOn ht)
    ((continuousOn_const.add continuousOn_id).mul
      (((hS.comp_continuousOn ht).add (hR.comp_continuousOn ht)).pow 2))
  intro x hx
  have hm := totalMean_pos M x hx
  have hy : 0 < 1+x := by linarith [hx.1]
  change (1+x)*(totalMean M x)^2 ≠ 0
  positivity

theorem birth_integral_bound (M : MomentODE) (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    (M.S horizonDays+M.R horizonDays)*(∫ x in (0 : ℝ)..u, birthDensity M x) ≤ 2/5 := by
  have hi : IntervalIntegrable (birthDensity M) MeasureTheory.volume 0 1 :=
    (birthDensity_continuous M).intervalIntegrable_of_Icc (by norm_num)
  have hmono := intervalIntegral.integral_mono_interval (f := birthDensity M)
    (by norm_num : (0 : ℝ) ≤ 0) hu.1 hu.2
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun x hx => (birthDensity_bound M x ⟨hx.1.le,hx.2⟩).1)) hi
  have hbound := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num) hi ((continuous_const.mul rateMass_continuous).intervalIntegrable 0 1)
    (fun x hx => (birthDensity_bound M x hx).2)
  change (∫ x in (0 : ℝ)..1, birthDensity M x) ≤
    ∫ x in (0 : ℝ)..1, densityFactor*rateMass x at hbound
  rw [intervalIntegral.integral_const_mul] at hbound
  have hA : accumulatedBirth 0 ≤ 173/512 := by
    rw [accumulatedBirth_zero]
    have := ScalarCount.varianceIntegral_bounds.2
    linarith
  change (∫ x in (0 : ℝ)..1, birthDensity M x) ≤ densityFactor*accumulatedBirth 0 at hbound
  have hc : 0 ≤ densityFactor := by norm_num [densityFactor]
  have htotal : 0 ≤ M.S horizonDays+M.R horizonDays :=
    add_nonneg (M.nonnegS _ horizon_bounds.1) (M.nonnegR _ horizon_bounds.1)
  have hproduct := mul_le_mul_of_nonneg_left
    (hmono.trans (hbound.trans (mul_le_mul_of_nonneg_left hA hc))) htotal
  have hm := endpoint_mean_upper M
  norm_num [densityFactor] at hproduct
  nlinarith

end InheritedCellAssay.PositiveMoments
