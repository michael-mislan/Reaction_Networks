import proofs.RandomViability.PublicationCorollaries
import proofs.PowerLawSmallRAF.SourceCriticalEndpoint

namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF HordijkSteelThreshold
noncomputable section
set_option maxHeartbeats 150000

theorem source_raf_probability_positive :
    ∃ r : ℝ,0 < r ∧ ∀ᶠ n : ℕ in atTop,r < eventMass (2-2/(n : ℝ)) n anySourceRAF := by
  have hs : 0 < (staticSurvival sourceCriticalOpenness).toReal :=
    ENNReal.toReal_pos (ne_of_gt (staticSurvival_pos sourceCriticalOpenness
      (by linarith [sourceCriticalOpenness_gt_half]))) (measure_ne_top _ _)
  let r := (staticSurvival sourceCriticalOpenness).toReal/2
  obtain ⟨N,_,hN⟩ := source_subexponential_RAF_endpoint_lower r (by dsimp [r]; linarith only [hs])
  refine ⟨r,by dsimp [r]; positivity,?_⟩
  filter_upwards [hN,sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hn ha
  apply hn.trans_le
  unfold sourceBoundedRevRAFProbability eventMass
  apply Finset.sum_le_sum
  intro c _
  by_cases h : ∃ Q : Finset (Reaction n),Q.card ≤ sourceFiniteSeedConstructionBudget N n ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) Q
  · rw [if_pos h,if_pos (show anySourceRAF c from ⟨h.choose,h.choose_spec.2⟩)]
  · rw [if_neg h]
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ n ha c
    · exact le_rfl

theorem source_raf_probability_le_one (n : ℕ) (hn : 4 ≤ n) :
    eventMass (2-2/(n : ℝ)) n anySourceRAF ≤ 1 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 1 < 2-2/(n : ℝ) := by
    have hd : 2/(n : ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith)).2 (by linarith)
    linarith
  rw [← sum_sourcePowerLawConfigWeight_eq_one (2-2/(n : ℝ)) n ha hn]
  apply Finset.sum_le_sum
  intro c _
  split_ifs
  · exact le_rfl
  · exact sourcePowerLawConfigWeight_nonneg _ n ha c

theorem output_conditioned_on_raf_theta (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∃ L U : ℝ,0 < L ∧ 0 < U ∧ ∀ᶠ n : ℕ in atTop,
      L*productiveSourceIncidence n ≤
        outputJointProbability volume hvolume (fun _ => anySourceRAF) n / eventMass (2-2/(n : ℝ)) n anySourceRAF ∧
      outputJointProbability volume hvolume (fun _ => anySourceRAF) n / eventMass (2-2/(n : ℝ)) n anySourceRAF ≤
        U*productiveSourceIncidence n := by
  obtain ⟨L,U,hL,hU,hb⟩ := output_and_some_raf_theta volume hvolume
  obtain ⟨r,hr,hR⟩ := source_raf_probability_positive
  refine ⟨L,U/r,hL,div_pos hU hr,?_⟩
  filter_upwards [hb,hR,source_incidence_ge_exp_eventually,eventually_ge_atTop 4] with n hb hR hp hn
  have hR0 := hr.trans hR
  have hR1 := source_raf_probability_le_one n hn
  constructor
  · apply (le_div_iff₀ hR0).2
    exact (mul_le_of_le_one_right (mul_pos hL hp.1).le hR1).trans hb.1
  · apply (div_le_iff₀ hR0).2
    have hh := mul_le_mul_of_nonneg_left hR.le (div_nonneg (mul_pos hU hp.1).le hr.le)
    have he : U*productiveSourceIncidence n/r*r = U*productiveSourceIncidence n := div_mul_cancel₀ _ hr.ne'
    rw [he] at hh
    have he' : U*productiveSourceIncidence n/r = (U/r)*productiveSourceIncidence n := by ring
    rw [he'] at hh
    exact hb.2.trans hh

theorem mean_degree_per_length_limit :
    Tendsto (fun n => productiveSourceMean n/(n : ℝ)) atTop (𝓝 (9/Real.pi^2)) := by
  have he : criticalLambda (-2) = 9/Real.pi^2 := by
    rw [← sourceFullIntensity_eq_criticalLambda,sourceFullIntensity,criticalPartialMass_full_eq]
    field_simp
    ring
  simpa only [he] using productive_source_mean_normalized

end
end RandomViability
