import proofs.InheritedCellAssay.PositiveMomentConstruction
import proofs.InheritedCellAssay.PositiveBirthIntegral
import proofs.InheritedCellAssay.PositiveScalarCertificate

namespace InheritedCellAssay.PositiveScalar
open PositiveMoments
set_option maxHeartbeats 20000

private theorem pgf_algebra (m p z : ℝ) (hd : 1-(1-p)*z ≠ 0) :
    m*p^2*z*(1-(1-p)*z)⁻¹+(1-m*p) =
      1-m*p*(1-z)/(1-(1-p)*z) := by
  generalize he : 1-(1-p)*z = D at hd ⊢
  field_simp [hd]
  rw [← he]
  ring

noncomputable def endClock : ℝ := Real.exp ((1/10)*horizonDays)-1
noncomputable def mean : ℝ := constructedMoments.S horizonDays+constructedMoments.R horizonDays
noncomputable def birthAccumulation : ℝ := mean*∫ x in (0 : ℝ)..endClock, birthDensity constructedMoments x
noncomputable def parameter : ℝ := 1/(1+birthAccumulation)

theorem endClock_bounds : endClock ∈ Set.Icc 0 1 := by
  have hb := birth_horizon_bound
  have hl : 1 ≤ Real.exp ((1/10)*horizonDays) := Real.one_le_exp_iff.mpr (by
    have := horizon_bounds.1
    linarith)
  unfold endClock
  constructor <;> linarith

theorem endClock_time : clock endClock = horizonDays := by
  unfold clock endClock
  have h : 1+(Real.exp ((1/10)*horizonDays)-1) = Real.exp ((1/10)*horizonDays) := by ring
  rw [h, Real.log_exp]
  ring

theorem mean_bounds : 0 ≤ mean ∧ mean ≤ 11/20 :=
  ⟨add_nonneg (constructedMoments.nonnegS _ horizon_bounds.1)
    (constructedMoments.nonnegR _ horizon_bounds.1), endpoint_mean_upper constructedMoments⟩

theorem accumulation_bounds : 0 ≤ birthAccumulation ∧ birthAccumulation ≤ 2/5 := by
  constructor
  · apply mul_nonneg mean_bounds.1
    apply intervalIntegral.integral_nonneg endClock_bounds.1
    intro x hx
    exact (birthDensity_bound constructedMoments x ⟨hx.1, hx.2.trans endClock_bounds.2⟩).1
  · exact birth_integral_bound constructedMoments endClock endClock_bounds

theorem parameter_bounds : 5/7 ≤ parameter ∧ parameter ≤ 1 := by
  obtain ⟨hl,hu⟩ := accumulation_bounds
  have hd : 0 < 1+birthAccumulation := by linarith
  unfold parameter
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_le_one hd).mpr
    linarith

/-- Explicit scalar terminal weights from the source ODE mean and birth integral.
    The forward/backward equation identification is a separate source obligation. -/
noncomputable def weight : ℕ → ℝ
  | 0 => 1-mean*parameter
  | n+1 => mean*parameter^2*(1-parameter)^n

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  obtain ⟨hm,hm1⟩ := mean_bounds
  obtain ⟨hp,hp1⟩ := parameter_bounds
  have hp0 : 0 ≤ parameter := by linarith
  cases n with
  | zero =>
    have hh := mul_le_of_le_one_right hm hp1
    unfold weight
    linarith
  | succ n =>
    unfold weight
    positivity [sub_nonneg.mpr hp1]

theorem weight_pgf (z : ℝ) (hz : z ∈ Set.Icc 0 1) :
    HasSum (fun n => weight n*z^n)
      (1-mean*parameter*(1-z)/(1-(1-parameter)*z)) := by
  obtain ⟨hp,hp1⟩ := parameter_bounds
  have hp0 : 0 < parameter := by linarith
  have hr : 0 ≤ 1-parameter := by linarith
  have hq : (1-parameter)*z < 1 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hz.2), hz.1]
  have hs := (hasSum_geometric_of_lt_one (mul_nonneg hr hz.1) hq).mul_left
    (mean*parameter^2*z)
  have ht : HasSum (fun n => weight (n+1)*z^(n+1))
      (mean*parameter^2*z*(1-(1-parameter)*z)⁻¹) := by
    convert hs using 1
    funext n
    simp only [weight, pow_succ, mul_pow]
    ring
  have hh := (hasSum_nat_add_iff (f := fun n => weight n*z^n) 1).mp ht
  simp only [Finset.sum_range_one, weight, pow_zero, mul_one] at hh
  have hD : 1-(1-parameter)*z ≠ 0 := by linarith
  exact (pgf_algebra mean parameter z hD) ▸ hh

theorem weight_normalized : HasSum weight 1 := by
  simpa using weight_pgf 1 (by norm_num)

theorem scalar_coverage_sharp : 332/343 ≤ weight 0+weight 1+weight 2 := by
  obtain ⟨hm0,hm⟩ := mean_bounds
  obtain ⟨hp,hp1⟩ := parameter_bounds
  have hp0 : 0 ≤ parameter := by linarith
  have hq : (1-parameter)^2 ≤ 4/49 := by nlinarith
  have hfac : 0 ≤ (2/7 : ℝ)+(1-parameter)-(2/7)^2-
      (2/7)*(1-parameter)-(1-parameter)^2 := by nlinarith only [hp,hp1,hq]
  have hprod := mul_nonneg (show 0 ≤ (2/7 : ℝ)-(1-parameter) by linarith only [hp]) hfac
  have hpoly : parameter*(1-parameter)^2 ≤ 20/343 := by nlinarith only [hprod]
  have htail : mean*parameter*(1-parameter)^2 ≤ 11/343 := by
    calc
      _ = mean*(parameter*(1-parameter)^2) := by ring
      _ ≤ mean*(20/343) := mul_le_mul_of_nonneg_left hpoly hm0
      _ ≤ (11/20)*(20/343) := mul_le_mul_of_nonneg_right hm (by norm_num)
      _ = _ := by norm_num
  have he : weight 0+weight 1+weight 2 = 1-mean*parameter*(1-parameter)^2 := by
    simp only [weight, pow_zero, pow_one, mul_one]
    ring
  rw [he]
  linarith

theorem scalar_coverage : 19/20 < weight 0+weight 1+weight 2 := by
  have := scalar_coverage_sharp
  linarith

end InheritedCellAssay.PositiveScalar
