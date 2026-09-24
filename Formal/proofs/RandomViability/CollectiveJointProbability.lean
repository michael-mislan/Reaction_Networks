import proofs.RandomViability.CollectiveSourceUpper
import proofs.RandomViability.CollectiveAsymptoticScale
import proofs.PowerLawSmallRAF.SourcePrivateGateway

namespace RandomViability
open Classical Filter Topology MeasureTheory PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 150000

local instance collectiveJointChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance collectiveJointChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

def collectiveJointProbability (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) (n : ℕ) : ℝ :=
  if hn : 4 ≤ n then fullyAveragedCollectiveProbability hn (volume n)
    ((collective_minimal_volume_pos n).trans_le (hvolume n)) (2-2/(n : ℝ)) else 1

theorem collective_joint_probability_bounds (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) (n : ℕ) (hn : 4 ≤ n) :
    sourceEmptyRowMass (2-2/(n : ℝ)) n ^ 6*productiveSourceIncidence n*
      (1-24*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ)))) ≤
        collectiveJointProbability volume hvolume n ∧
    collectiveJointProbability volume hvolume n ≤
      collectiveSourceUpperConstant*productiveSourceIncidence n+
        2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ))) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 1 < 2-2/(n : ℝ) := by
    have hd : 2/(n : ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith)).2 (by linarith)
    linarith
  have hR : 2 ≤ sourceReactionCount n := by unfold sourceReactionCount; omega
  have hv : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (volume n : ℝ) := by exact_mod_cast hvolume n
  have hs := (collective_quadratic_volume_scale (n : ℝ) (volume n) (by linarith only [hnR]) hv).1
  have hh := fully_averaged_collective_bounds hn (volume n)
    ((collective_minimal_volume_pos n).trans_le (hvolume n)) hs (2-2/(n : ℝ)) ha
  rw [powerLawMoleculeGatewayHit_one_eq_mean_div _ _ ha hR] at hh
  simpa only [collectiveJointProbability,dif_pos hn,productiveSourceIncidence,productiveSourceMean] using hh

theorem collective_noise_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ)))) atTop (𝓝 0) := by
  have hu := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun _ => (Real.exp_pos _).le)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hv : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (volume n : ℝ) := by exact_mod_cast hvolume n
    have hs := (collective_quadratic_volume_scale (n : ℝ) (volume n) (by linarith only [hnR]) hv).2
    exact Real.exp_le_exp.mpr (by linarith only [hs,hnR])

/-- Uniform positive constant-factor comparison with the exact source incidence.
It holds for every volume sequence above the same explicit quadratic envelope. -/
theorem collective_joint_probability_theta (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∃ L U : ℝ,0 < L ∧ 0 < U ∧ ∀ᶠ n in atTop,
      L*productiveSourceIncidence n ≤ collectiveJointProbability volume hvolume n ∧
      collectiveJointProbability volume hvolume n ≤ U*productiveSourceIncidence n := by
  let L : ℝ := (1/(Real.pi^2/6))^6/2
  let U : ℝ := collectiveSourceUpperConstant+1
  have hq : 0 < (1/(Real.pi^2/6) : ℝ)^6 := by positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by
    have hc : 0 ≤ collectiveSourceUpperConstant := by unfold collectiveSourceUpperConstant; positivity
    dsimp [U]
    linarith only [hc]
  have hl := (collective_empty_row_limit.pow 6).mul
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      ((collective_noise_tendsto_zero volume hvolume).const_mul 24))
  simp only [mul_zero,sub_zero,mul_one] at hl
  have hle := hl.eventually (eventually_gt_nhds (show L < (1/(Real.pi^2/6) : ℝ)^6 by dsimp [L]; linarith only [hq]))
  have hu := (collective_noise_relative_tendsto_zero volume hvolume).const_mul 2
  simp only [mul_zero] at hu
  have hue := hu.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨L,U,hL,hU,?_⟩
  filter_upwards [hle,hue,source_incidence_ge_exp_eventually,eventually_ge_atTop 4] with n hl hu hp hn
  have hb := collective_joint_probability_bounds volume hvolume n hn
  constructor
  · have hh := mul_le_mul_of_nonneg_right hl.le hp.1.le
    nlinarith only [hh,hb.1]
  · have hh := (div_le_iff₀ hp.1).1 (show
        (2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ))))/productiveSourceIncidence n ≤ 1 by
      simpa only [mul_div_assoc] using hu.le)
    dsimp only [U]
    nlinarith only [hh,hb.2]

theorem collective_joint_logarithmic_limit (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => Real.log (collectiveJointProbability volume hvolume n)/(n : ℝ))
      atTop (𝓝 (-Real.log 2)) := by
  obtain ⟨L,U,hL,hU,hbounds⟩ := collective_joint_probability_theta volume hvolume
  have hl := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log L) atTop (𝓝 (Real.log L))).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))).add productive_source_incidence_log_rate
  have hu := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log U) atTop (𝓝 (Real.log U))).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))).add productive_source_incidence_log_rate
  simp only [zero_add] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hbounds,source_incidence_ge_exp_eventually] with n hb hp
    have hh := Real.log_le_log (mul_pos hL hp.1) hb.1
    rw [Real.log_mul hL.ne' hp.1.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)
  · filter_upwards [hbounds,source_incidence_ge_exp_eventually] with n hb hp
    have hpos := (mul_pos hL hp.1).trans_le hb.1
    have hh := Real.log_le_log hpos hb.2
    rw [Real.log_mul hU.ne' hp.1.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)

end
end RandomViability
