import proofs.RandomViability.PhysicalOutputEvent

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 150000
variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_output_upper_without_short_incidence (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (hgood : ¬ShortIncidence collectiveUpperCutoff c)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) :
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | physicalOutputEvent V z}).toReal ≤
      4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | physicalOutputEvent V z} →
      z ∈ {z | ¬markedRewardNoiseBound c V basal cat (positiveBasalReward V) 101 (1/100) z} ∪
        {z | ¬markedRewardNoiseBound c V basal cat (normalizedPositiveCatalyticReward V) 101 (1/40) z} := by
    filter_upwards [hi,hc,hp,hw] with z hzi hzc hzp hzw
    intro hz
    exact output_requires_noise c hgood V hV basal cat hb hcat z
      (by simpa only [hzi] using hinit) hzc hzp hzw hz
  have hb1 : ∀ r,(basal r : ℝ) ≤ 1 := by
    intro r
    have h := hb r
    linarith only [h]
  have hm := marked_noise_margins (n : ℝ) V (by exact_mod_cast hn) hV hscale
  have ht := physical_marked_reward_noise_failure hn c V hV basal cat N (normalizedPositiveCatalyticReward V)
    (fun N ch => by
      rw [abs_of_nonneg (positive_catalytic_reward_bounds V hV N ch).1]
      exact (positive_catalytic_reward_bounds V hV N ch).2.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hn) hV.le))
    (fun N hM => positive_catalytic_reward_common_variance (by omega) c V hV basal cat N hM hb1 hcat)
    markedNoiseDelta 101 (1/40) (by norm_num [markedNoiseDelta]) (by norm_num) hm.2.2.2.2.1
  have he := (marked_noise_exponents (n : ℝ) V (by exact_mod_cast hn) hV).1
  have hbt := physical_positive_basal_noise_failure hn c V hV basal cat N hb markedNoiseDelta 101 (1/100)
    (by norm_num [markedNoiseDelta]) (by norm_num) hm.2.2.2.2.2
  have hsum := (measure_mono_ae hsub).trans ((measure_union_le _ _).trans (add_le_add hbt ht))
  have hexp := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg he))
  have hsum' := hsum.trans (add_le_add (mul_le_mul_right hexp 2) (mul_le_mul_right hexp 2))
  have heq : (2 : ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))))+
      2*ENNReal.ofReal (Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) =
      4*ENNReal.ofReal (Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) := by
    rw [← add_mul]
    norm_num
  rw [heq] at hsum'
  have hr := ENNReal.toReal_mono (by finiteness) hsum'
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_pos _).le] using hr

theorem physical_output_disabled_upper (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) :
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal (fun _ _ => 0) N
      {z | physicalOutputEvent V z}).toReal ≤ 2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal (fun _ _ => 0) N
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal (fun _ _ => 0)) (unboundedPhysicalRate_nonneg c V 1 basal (fun _ _ => 0))
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal (fun _ _ => 0))
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal (fun _ _ => 0)) (unboundedPhysicalRate_nonneg c V 1 basal (fun _ _ => 0))
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal (fun _ _ => 0))
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal (fun _ _ => 0)) (unboundedPhysicalRate_nonneg c V 1 basal (fun _ _ => 0))
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal (fun _ _ => 0))
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal (fun _ _ => 0)) (unboundedPhysicalRate_nonneg c V 1 basal (fun _ _ => 0))
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal (fun _ _ => 0))
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | physicalOutputEvent V z} →
      z ∈ {z | ¬markedRewardNoiseBound c V basal (fun _ _ => 0) (positiveBasalReward V) 101 (1/100) z} := by
    filter_upwards [hi,hc,hp,hw] with z hzi hzc hzp hzw
    intro hz
    exact disabled_output_requires_basal_noise c V hV basal hb z
      (by simpa only [hzi] using hinit) hzc hzp hzw hz
  have hm := marked_noise_margins (n : ℝ) V (by exact_mod_cast hn) hV hscale
  have ht := physical_positive_basal_noise_failure hn c V hV basal (fun _ _ => 0) N hb
    markedNoiseDelta 101 (1/100) (by norm_num [markedNoiseDelta]) (by norm_num) hm.2.2.2.2.2
  have he := (marked_noise_exponents (n : ℝ) V (by exact_mod_cast hn) hV).1
  have ht' := (measure_mono_ae hsub).trans (ht.trans
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg he))) 2))
  have hr := ENNReal.toReal_mono (by finiteness) ht'
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_pos _).le] using hr

end
end RandomViability
