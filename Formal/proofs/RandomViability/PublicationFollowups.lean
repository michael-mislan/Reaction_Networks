import proofs.RandomViability.Remark34

set_option Elab.async false
namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 10000

/-- Any source event implying absence of productive singleton incidences is
asymptotically absent after observing the literal output event. -/
theorem output_posterior_bad_event_vanishes
    (volume : ℕ → ℕ) (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n)
    (A : ∀ n,SourceMoleculeFibreConfig n → Prop)
    (hA : ∀ n c,A n c → noProductiveSingleton c) :
    Tendsto (fun n => outputJointProbability volume hvolume A n/
      outputJointProbability volume hvolume (fun _ _ => True) n) atTop (𝓝 0) := by
  have hu := no_singleton_given_output_tendsto_zero volume hvolume
  obtain ⟨L,U,hL,_,hb⟩ := output_joint_probability_theta volume hvolume (fun _ _ => True)
    (fun _ _ _ _ => trivial)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hb,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hd := (mul_pos hL hp.1).trans_le hb.1
    apply div_nonneg _ hd.le
    unfold outputJointProbability
    simp only [dif_pos hn]
    exact averaged_output_nonneg hn _ _ _ ha _
  · filter_upwards [hb,source_incidence_ge_exp_eventually,eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hb hp hn ha
    have hd := (mul_pos hL hp.1).trans_le hb.1
    apply div_le_div_of_nonneg_right _ hd.le
    unfold outputJointProbability
    simp only [dif_pos hn]
    exact averaged_output_mono hn _ _ _ ha _ _ (hA n)

theorem no_singleton_RAF_given_output_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => outputJointProbability volume hvolume (fun _ c => ¬hasSingletonRAF c) n/
      outputJointProbability volume hvolume (fun _ _ => True) n) atTop (𝓝 0) :=
  output_posterior_bad_event_vanishes volume hvolume _ (fun _ c h =>
    no_singleton_raf_implies_no_productive_singleton c h)

theorem no_RAF_given_output_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => outputJointProbability volume hvolume (fun _ c => ¬anySourceRAF c) n/
      outputJointProbability volume hvolume (fun _ _ => True) n) atTop (𝓝 0) := by
  apply output_posterior_bad_event_vanishes volume hvolume
  intro n c h
  apply no_singleton_raf_implies_no_productive_singleton c
  rintro ⟨r,hr⟩
  exact h ⟨{r},hr⟩

theorem deleted_unique_incidence_output_upper {n : ℕ}
    [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]
    (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n) (z : Molecule n) (r : Reaction n)
    (hi : SingleLocalIncidence singleIncidenceCutoff c z r)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hs : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hN : countNonfoodMass N = 0) :
    (physicalTrajectoryLaw (by omega : 2 ≤ n) (eraseLocalIncidence c z r) V 1 hV (by norm_num) basal cat N
      {path | physicalOutputEvent V path}).toReal ≤ 4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  apply physical_output_upper_without_short_incidence hn _ _ V hV hs basal cat hb hc N hN
  have hfree := erase_local_has_no_short_incidence c z r hi
  rintro ⟨q,hq,s,hs,hmem⟩
  apply hfree
  refine ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,s,?_,hmem⟩
  · have hh := (Finset.mem_filter.mp hq).2
    exact hh.trans (by norm_num [collectiveUpperCutoff,singleIncidenceCutoff])
  · exact hs.trans (by norm_num [collectiveUpperCutoff,singleIncidenceCutoff])

end
end RandomViability

