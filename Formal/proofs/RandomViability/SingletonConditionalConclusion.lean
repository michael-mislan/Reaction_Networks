import proofs.RandomViability.SingletonDominance

set_option Elab.async false
namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 70000

/-- Remark 3.4's conditional conclusion for the literal productive-output event:
the conditional probability of having no productive singleton tends to zero. -/
theorem no_singleton_given_output_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => outputJointProbability volume hvolume (fun _ => noProductiveSingleton) n/
      outputJointProbability volume hvolume (fun _ _ => True) n) atTop (𝓝 0) := by
  obtain ⟨L,U,hL,_,hbound⟩ := output_joint_probability_theta volume hvolume (fun _ _ => True)
    (fun _ _ _ _ => trivial)
  have hu := (output_without_productive_singleton_relative_tendsto_zero volume hvolume).div_const L
  simp only [zero_div] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hbound,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hden : 0 < outputJointProbability volume hvolume (fun _ _ => True) n :=
      (mul_pos hL hp.1).trans_le hb.1
    have hnum : 0 ≤ outputJointProbability volume hvolume (fun _ => noProductiveSingleton) n := by
      unfold outputJointProbability
      rw [dif_pos hn]
      exact averaged_output_nonneg hn _ _ _ ha _
    exact div_nonneg hnum hden.le
  · filter_upwards [hbound,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hnum : 0 ≤ outputJointProbability volume hvolume (fun _ => noProductiveSingleton) n := by
      unfold outputJointProbability
      rw [dif_pos hn]
      exact averaged_output_nonneg hn _ _ _ ha _
    have hh := div_le_div_of_nonneg_left hnum (mul_pos hL hp.1) hb.1
    convert hh using 1
    ring

end
end RandomViability
