import proofs.RandomViability.OutsiderPathBalance

set_option Elab.async false
namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 70000

theorem outsider_signed_reward_variance {n : ℕ} (hn : 2 ≤ n)
    (q : Molecule n) (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(outsiderSignedReward q V N ch)^2) ≤
      (384000+11*(n : ℝ))/V := by
  have hs (ch : PhysicalCountChannel n) : (outsiderSignedReward q V N ch)^2 ≤ (4/(V : ℝ))^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (outsiderSignedReward q V N ch))
      (outsider_signed_reward_bound q V hV N ch) 2
    simpa only [sq_abs] using hh
  calc
    _ ≤ ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(4/(V : ℝ))^2 :=
      Finset.sum_le_sum (fun ch _ => mul_le_mul_of_nonneg_left (hs ch)
        (unboundedPhysicalRate_nonneg c V 1 basal cat N ch))
    _ = (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch)*(4/(V : ℝ))^2 := (Finset.sum_mul _ _ _).symm
    _ ≤ (24000*V)*(4/(V : ℝ))^2 := mul_le_mul_of_nonneg_right
      (unbounded_total_rate_mass_eleven hn c V hV basal cat N hM hb hcat) (sq_nonneg _)
    _ = 384000/(V : ℝ) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ n by positivity]) hV.le

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_isolated_outsider_output_upper (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n)
    (q : Molecule n) (r : Reaction n) (hiso : SingleLocalIncidence singleIncidenceCutoff c q r)
    (hout : OutsiderFoodIncidence r q) (hsmall : molLength q ≤ singleIncidenceCutoff+2)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : (n : ℝ)/V ≤ 1/200000)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) (hq0 : N q = 0) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | physicalOutputEvent V z} ≤
      2*ENNReal.ofReal (Real.exp (-((1/200000 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200000))))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hr := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | physicalOutputEvent V z} →
      z ∈ {z | ¬markedRewardNoiseBound c V basal cat (outsiderSignedReward q V) 101 (1/100000) z} := by
    filter_upwards [hi,hc,hr,hw] with z hzi hzc hzr hzw
    intro hz
    exact output_forces_outsider_noise c q r hiso hout hsmall V hV basal cat hb hcat z
      (by simpa only [hzi] using hinit) (by simpa only [hzi] using hq0) hzc hzr hzw hz
  apply (measure_mono_ae hsub).trans
  apply physical_marked_reward_noise_failure hn c V hV basal cat N (outsiderSignedReward q V) _ _
    (1/200000) 101 (1/100000) (by norm_num) (by norm_num) (by linarith only [hscale])
  · intro N ch
    exact (outsider_signed_reward_bound q V hV N ch).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hn) hV.le)
  · intro N hM
    exact outsider_signed_reward_variance (by omega) q c V hV basal cat N hM
      (fun r => (hb r).trans (by norm_num)) hcat

end
end RandomViability
