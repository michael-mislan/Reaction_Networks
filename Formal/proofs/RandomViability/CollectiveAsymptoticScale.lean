import proofs.RandomViability.MarkedUniformScale
import proofs.RandomViability.SourceFoodSilentSeed
import proofs.RandomViability.ProductiveSourceAsymptotics
import proofs.PowerLawSmallRAF.SourceCriticalSecondMoment

namespace RandomViability
open Classical Filter Topology PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 150000

def collectiveMinimalVolume (n : ℕ) : ℕ := 10^60*(n+1)^2

theorem collective_minimal_volume_pos (n : ℕ) : 0 < collectiveMinimalVolume n := by
  unfold collectiveMinimalVolume
  positivity

theorem collective_quadratic_volume_scale (n V : ℝ) (hn : 1 ≤ n)
    (hV : (10^60 : ℝ)*(n+1)^2 ≤ V) :
    2*n/markedNoiseDelta ≤ V ∧ 3*n ≤ markedNoiseRate*V/n := by
  have hn0 : 0 < n := by linarith only [hn]
  constructor
  · norm_num [markedNoiseDelta] at ⊢
    nlinarith only [hV,hn,sq_nonneg n]
  · apply (le_div_iff₀ hn0).2
    norm_num [markedNoiseRate,markedNoiseDelta]
    nlinarith only [hV,sq_nonneg (n+1),sq_nonneg n,hn]

theorem source_empty_row_mass_eq (a : ℝ) (n : ℕ) :
    sourceEmptyRowMass a n = 1/zipfNormalizer a := by
  have hR : 1 < sourceReactionCount n := by unfold sourceReactionCount; omega
  simp [sourceEmptyRowMass,subsetDegreeWeight,cappedZipfDegreeMass,hR]

theorem collective_empty_row_limit :
    Tendsto (fun n : ℕ => sourceEmptyRowMass (2-2/(n : ℝ)) n)
      atTop (𝓝 (1/(Real.pi^2/6))) := by
  simp_rw [source_empty_row_mass_eq]
  have hz : Tendsto (fun n : ℕ => zipfNormalizer (2-2/(n : ℝ))) atTop (𝓝 (Real.pi^2/6)) := by
    simpa only [zipfNormalizer_two] using
      (continuousAt_zipfNormalizer one_lt_two).tendsto.comp sourceExactCriticalExponent_tendsto
  exact tendsto_const_nhds.div hz (by positivity)

theorem source_incidence_ge_exp_eventually :
    ∀ᶠ n : ℕ in atTop,0 < productiveSourceIncidence n ∧
      Real.exp (-(2*(n : ℝ))) ≤ productiveSourceIncidence n := by
  have hb : (-2 : ℝ) < -Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh]
  have he := productive_source_incidence_log_rate.eventually (eventually_gt_nhds hb)
  filter_upwards [he,productive_source_mean_eventually_pos,eventually_ge_atTop 4] with n hlog hmean hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < productiveSourceIncidence n := by
    apply div_pos hmean
    exact_mod_cast (show 0 < sourceReactionCount n by unfold sourceReactionCount; omega)
  refine ⟨hp,?_⟩
  have hh := (le_div_iff₀ hn0).1 hlog.le
  have hlog' : -(2*(n : ℝ)) ≤ Real.log (productiveSourceIncidence n) := by linarith only [hh]
  have hx := Real.exp_le_exp.mpr hlog'
  simpa only [Real.exp_log hp] using hx

theorem collective_noise_relative_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ)))/productiveSourceIncidence n)
      atTop (𝓝 0) := by
  have hu := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [source_incidence_ge_exp_eventually] with n hn
    exact div_nonneg (Real.exp_pos _).le hn.1.le
  · filter_upwards [source_incidence_ge_exp_eventually,eventually_ge_atTop 4] with n hp hn
    have hvol : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (volume n : ℝ) := by
      exact_mod_cast hvolume n
    have hscale := (collective_quadratic_volume_scale (n : ℝ) (volume n)
      (by exact_mod_cast (show 1 ≤ n by omega)) hvol).2
    calc
      _ ≤ Real.exp (-(3*(n : ℝ)))/productiveSourceIncidence n :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hscale)) hp.1.le
      _ ≤ Real.exp (-(3*(n : ℝ)))/Real.exp (-(2*(n : ℝ))) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hp.2
      _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_sub]; congr 1; ring

end
end RandomViability
