import proofs.RandomViability.OutputJointLimit
import proofs.RandomViability.RandomAutocatalysis

namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 150000

theorem output_and_some_raf_theta (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∃ L U : ℝ,0 < L ∧ 0 < U ∧ ∀ᶠ n in atTop,
      L*productiveSourceIncidence n ≤ outputJointProbability volume hvolume (fun _ => anySourceRAF) n ∧
      outputJointProbability volume hvolume (fun _ => anySourceRAF) n ≤ U*productiveSourceIncidence n := by
  apply output_joint_probability_theta volume hvolume
  intro n hn c hs
  exact ⟨{productiveReaction hn},productive_singleton_isRAF hn c hs.2⟩

theorem label_free_output_theta (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∃ L U : ℝ,0 < L ∧ 0 < U ∧ ∀ᶠ n in atTop,
      L*productiveSourceIncidence n ≤ outputJointProbability volume hvolume (fun _ _ => True) n ∧
      outputJointProbability volume hvolume (fun _ _ => True) n ≤ U*productiveSourceIncidence n :=
  output_joint_probability_theta volume hvolume (fun _ _ => True) (by intros; trivial)

def disabledOutputJointProbability (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) (n : ℕ) : ℝ :=
  if hn : 4 ≤ n then averagedOutputProbability hn (volume n)
    ((collective_minimal_volume_pos n).trans_le (hvolume n)) (2-2/(n : ℝ)) (fun _ => True) false else 0

theorem disabled_output_joint_bounds (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∀ᶠ n in atTop,0 ≤ disabledOutputJointProbability volume hvolume n ∧
      disabledOutputJointProbability volume hvolume n ≤ 2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ))) := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 1 < 2-2/(n : ℝ) := by
    have hd : 2/(n : ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith)).2 (by linarith)
    linarith
  have hv : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (volume n : ℝ) := by exact_mod_cast hvolume n
  have hs := (collective_quadratic_volume_scale (n : ℝ) (volume n) (by linarith only [hnR]) hv).1
  rw [disabledOutputJointProbability,dif_pos hn]
  constructor
  · unfold averagedOutputProbability uniformFiniteAverage sourceAverage
    apply div_nonneg _ (by positivity)
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (sourcePowerLawConfigWeight_nonneg _ n ha c) (by simp only [if_true]; exact ENNReal.toReal_nonneg)
  · exact averaged_output_disabled_bound hn _ _ hs _ ha

theorem disabled_enabled_output_ratio (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => disabledOutputJointProbability volume hvolume n /
      outputJointProbability volume hvolume (fun _ _ => True) n) atTop (𝓝 0) := by
  obtain ⟨L,U,hL,_,hb⟩ := label_free_output_theta volume hvolume
  have ht := (collective_noise_relative_tendsto_zero volume hvolume).const_mul (2/L)
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [hb,source_incidence_ge_exp_eventually,disabled_output_joint_bounds volume hvolume] with n h hp h0
    exact div_nonneg h0.1 ((mul_pos hL hp.1).trans_le h.1).le
  · filter_upwards [hb,source_incidence_ge_exp_eventually,disabled_output_joint_bounds volume hvolume] with n h hp h0
    have hP := (mul_pos hL hp.1).trans_le h.1
    calc
      _ ≤ (2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ)))) /
          outputJointProbability volume hvolume (fun _ _ => True) n := div_le_div_of_nonneg_right h0.2 hP.le
      _ ≤ (2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ))))/(L*productiveSourceIncidence n) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hL hp.1) h.1
      _ = _ := by ring

/-- Sufficient finite-volume reliability; no quadratic sequence assumption. -/
theorem noise_error_below_tolerance (n V eta : ℝ) (hn : 0 < n) (heta : 0 < eta)
    (hscale : n/markedNoiseRate*Real.log (24/eta) ≤ V) :
    24*Real.exp (-(markedNoiseRate*V/n)) ≤ eta := by
  have hc := marked_noise_rate_pos
  have hlog : Real.log (24/eta) ≤ markedNoiseRate*V/n := by
    apply (le_div_iff₀ hn).2
    have hh := mul_le_mul_of_nonneg_left hscale hc.le
    have he : markedNoiseRate*(n/markedNoiseRate*Real.log (24/eta)) = n*Real.log (24/eta) := by
      field_simp
    rw [he] at hh
    nlinarith only [hh]
  have he : 24/eta ≤ Real.exp (markedNoiseRate*V/n) :=
    (Real.log_le_iff_le_exp (by positivity)).1 hlog
  rw [Real.exp_neg,← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  have hh := (div_le_iff₀ heta).1 he
  nlinarith only [hh]

end
end RandomViability
