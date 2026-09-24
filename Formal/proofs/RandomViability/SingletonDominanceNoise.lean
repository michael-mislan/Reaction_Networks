import proofs.RandomViability.LocalOutputExclusion
import proofs.RandomViability.CollectiveAsymptoticScale

set_option Elab.async false
namespace RandomViability
open Classical Filter Topology PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 50000

theorem local_output_noise_upper_le (n : ℕ) (hn : 0 < n) (V : NNReal) :
    localOutputNoiseUpper n V ≤ 8*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc (d : ℝ) (hd : 0 < d)
      (hr : markedNoiseRate ≤ d^2/(4*(96011*101+d))) :
      Real.exp (-(d^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+d)))) ≤
        Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have hh := mul_le_mul_of_nonneg_right hr (div_nonneg V.coe_nonneg hnR.le)
    convert hh using 1 <;> field_simp
  have hm := hc (1/200) (by norm_num) (by norm_num [markedNoiseRate,markedNoiseDelta])
  have ho := hc (1/200000) (by norm_num) (by norm_num [markedNoiseRate,markedNoiseDelta])
  unfold localOutputNoiseUpper
  linarith only [hm,ho]

theorem local_output_noise_relative_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => localOutputNoiseUpper n (volume n : NNReal)/productiveSourceIncidence n)
      atTop (𝓝 0) := by
  have hh := (collective_noise_relative_tendsto_zero volume hvolume).const_mul 8
  simp only [mul_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · filter_upwards [source_incidence_ge_exp_eventually] with n hn
    apply div_nonneg _ hn.1.le
    unfold localOutputNoiseUpper
    positivity
  · filter_upwards [source_incidence_ge_exp_eventually,eventually_ge_atTop 1] with n hp hn
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
      (local_output_noise_upper_le n (by omega) (volume n : NNReal)) hp.1.le

theorem singleton_volume_scales (n V : ℕ) (hn : 4 ≤ n)
    (hV : collectiveMinimalVolume n ≤ V) :
    2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ) ∧ (n : ℝ)/(V : ℝ) ≤ 1/200000 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hv : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (V : ℝ) := by exact_mod_cast hV
  have hs := (collective_quadratic_volume_scale n V hnR hv).1
  have hpos : (0 : ℝ) < V := by exact_mod_cast ((collective_minimal_volume_pos n).trans_le hV)
  refine ⟨hs,(div_le_iff₀ hpos).2 ?_⟩
  norm_num [markedNoiseDelta] at hs
  linarith only [hs,hnR]

end
end RandomViability
