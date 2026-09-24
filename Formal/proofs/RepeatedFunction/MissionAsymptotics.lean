import proofs.RepeatedFunction.FiniteResolution

namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 150000

theorem two_window_noise_relative_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => Real.exp (-(twoWindowNoiseRate*(volume n : ℝ)/(n : ℝ)))/productiveSourceIncidence n)
      atTop (𝓝 0) := by
  have hu := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [source_incidence_ge_exp_eventually] with n hn
    exact div_nonneg (Real.exp_pos _).le hn.1.le
  · filter_upwards [source_incidence_ge_exp_eventually,eventually_ge_atTop 4] with n hp hn
    have hvol : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (volume n : ℝ) := by exact_mod_cast hvolume n
    have hscale := (two_window_quadratic_volume_scale (n : ℝ) (volume n)
      (by exact_mod_cast (show 1 ≤ n by omega)) hvol).2.1
    calc
      _ ≤ Real.exp (-(3*(n : ℝ)))/productiveSourceIncidence n :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hscale)) hp.1.le
      _ ≤ Real.exp (-(3*(n : ℝ)))/Real.exp (-(2*(n : ℝ))) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hp.2
      _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_sub]; congr 1; ring

theorem mission_residual_relative_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n : ℕ => missionResidualBound (2-2/(n : ℝ)) n (volume n)/productiveSourceIncidence n)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n
      (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)/productiveSourceIncidence n) atTop (𝓝 0) := by
    simpa only [productiveSourceIncidence,productiveSourceMean] using
      two_local_incidence_mass_div_incidence_tendsto_zero singleIncidenceCutoff
  simpa only [missionResidualBound,add_div,add_zero] using
    hs.add (local_output_noise_relative_tendsto_zero volume hvolume)

theorem two_window_noise_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => Real.exp (-(twoWindowNoiseRate*(volume n : ℝ)/(n : ℝ)))) atTop (𝓝 0) := by
  have hu := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hv : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (volume n : ℝ) := by exact_mod_cast hvolume n
    have hs := (two_window_quadratic_volume_scale n (volume n)
      (by exact_mod_cast (show 1 ≤ n by omega)) hv).2.1
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hs,hn0]

def missionJointProbability (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n)
    (A : ∀ n,SourceMoleculeFibreConfig n → Prop) (n : ℕ) : ℝ :=
  if hn : 4 ≤ n then averagedMissionProbability hn (volume n)
    ((collective_minimal_volume_pos n).trans_le (hvolume n)) (2-2/(n : ℝ)) (A n) else 1

def missionAsymptoticLower : ℝ := (1/(Real.pi^2/6))^6/2

theorem mission_joint_eventual_bounds (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n)
    (A : ∀ n,SourceMoleculeFibreConfig n → Prop)
    (hA : ∀ n (hn : 4 ≤ n) c,sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn) c → A n c) :
    ∀ᶠ n in atTop,
      missionAsymptoticLower*productiveSourceIncidence n ≤ missionJointProbability volume hvolume A n ∧
      missionJointProbability volume hvolume A n ≤ 15481*productiveSourceIncidence n := by
  have hq : 0 < (1/(Real.pi^2/6) : ℝ)^6 := by positivity
  have hl := (collective_empty_row_limit.pow 6).mul
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      ((two_window_noise_tendsto_zero volume hvolume).const_mul 24))
  simp only [mul_zero,sub_zero,mul_one] at hl
  have hle := hl.eventually (eventually_gt_nhds (show missionAsymptoticLower < (1/(Real.pi^2/6) : ℝ)^6 by
    unfold missionAsymptoticLower; linarith only [hq]))
  have hue := (mission_residual_relative_tendsto_zero volume hvolume).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hle,hue,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
    sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hl hu hp hn ha
  have hsc := singleton_volume_scales n (volume n) hn (hvolume n)
  have hv := (collective_minimal_volume_pos n).trans_le (hvolume n)
  have hlo := averaged_mission_lower hn (volume n) hv hsc.1 _ ha (A n) (hA n hn)
  have hup := averaged_mission_finite_upper hn (volume n) hv hsc.1 hsc.2 _ ha (A n)
  rw [c6_short_coefficient] at hup
  rw [powerLawMoleculeGatewayHit_one_eq_mean_div _ _ ha (by unfold sourceReactionCount; omega)] at hlo
  change sourceEmptyRowMass _ n ^6*productiveSourceIncidence n*(1-24*Real.exp _) ≤ _ at hlo
  have hr := (div_le_iff₀ hp.1).1 hu.le
  change missionResidualBound _ n (volume n) ≤ 1*productiveSourceIncidence n at hr
  simp only [missionJointProbability,dif_pos hn]
  constructor
  · have hh := mul_le_mul_of_nonneg_right hl.le hp.1.le
    nlinarith only [hh,hlo]
  · change _ ≤ 15480*productiveSourceIncidence n+_+_ at hup
    unfold missionResidualBound at hr
    nlinarith only [hup,hr]

end
end RandomViability
