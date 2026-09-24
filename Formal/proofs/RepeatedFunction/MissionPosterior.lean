import proofs.RepeatedFunction.MissionAsymptotics

namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 100000

theorem mission_asymptotic_lower_pos : 0 < missionAsymptoticLower := by
  unfold missionAsymptoticLower
  positivity

theorem no_singleton_given_mission_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => missionJointProbability volume hvolume (fun _ => noProductiveSingleton) n/
      missionJointProbability volume hvolume (fun _ _ => True) n) atTop (𝓝 0) := by
  have hb := mission_joint_eventual_bounds volume hvolume (fun _ _ => True) (fun _ _ _ _ => trivial)
  have hu := (mission_residual_relative_tendsto_zero volume hvolume).div_const missionAsymptoticLower
  simp only [zero_div] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hb,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hd := (mul_pos mission_asymptotic_lower_pos hp.1).trans_le hb.1
    apply div_nonneg _ hd.le
    simp only [missionJointProbability,dif_pos hn]
    exact averaged_mission_nonneg hn _ _ _ ha _
  · filter_upwards [hb,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hd := (mul_pos mission_asymptotic_lower_pos hp.1).trans_le hb.1
    have hs := singleton_volume_scales n (volume n) hn (hvolume n)
    have hr := averaged_mission_without_singleton_upper hn (volume n)
      ((collective_minimal_volume_pos n).trans_le (hvolume n)) hs.1 hs.2 _ ha
    have hnum : 0 ≤ missionJointProbability volume hvolume (fun _ => noProductiveSingleton) n := by
      simp only [missionJointProbability,dif_pos hn]
      exact averaged_mission_nonneg hn _ _ _ ha _
    have hres : missionJointProbability volume hvolume (fun _ => noProductiveSingleton) n ≤
        missionResidualBound (2-2/(n : ℝ)) n (volume n) := by
      simpa only [missionJointProbability,dif_pos hn,missionResidualBound] using hr
    have h1 := div_le_div_of_nonneg_left hnum (mul_pos mission_asymptotic_lower_pos hp.1) hb.1
    have h2 := div_le_div_of_nonneg_right hres (mul_pos mission_asymptotic_lower_pos hp.1).le
    convert h1.trans h2 using 1
    ring

def missionSeedEvent (n : ℕ) : SourceMoleculeFibreConfig n → Prop :=
  if hn : 4 ≤ n then sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn)
  else fun _ => False

/-- A calculated positive successful-run fraction for the food-silent self seed.
This is a conservative lower envelope, not an exact posterior limit. -/
theorem seed_given_mission_eventually_positive (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∀ᶠ n in atTop, missionAsymptoticLower/15481 ≤
      missionJointProbability volume hvolume missionSeedEvent n/
        missionJointProbability volume hvolume (fun _ _ => True) n := by
  have hb := mission_joint_eventual_bounds volume hvolume (fun _ _ => True) (fun _ _ _ _ => trivial)
  have ha := mission_joint_eventual_bounds volume hvolume missionSeedEvent
    (fun n hn c hc => by simpa only [missionSeedEvent,dif_pos hn] using hc)
  filter_upwards [hb,ha,source_incidence_ge_exp_eventually] with n hb ha hp
  have hd := (mul_pos mission_asymptotic_lower_pos hp.1).trans_le hb.1
  have h1 := div_le_div_of_nonneg_left (mul_pos mission_asymptotic_lower_pos hp.1).le hd hb.2
  have h2 := div_le_div_of_nonneg_right ha.1 hd.le
  have heq : missionAsymptoticLower*productiveSourceIncidence n/(15481*productiveSourceIncidence n) =
      missionAsymptoticLower/15481 := by field_simp [hp.1.ne']
  rw [heq] at h1
  exact h1.trans h2

end
end RandomViability
