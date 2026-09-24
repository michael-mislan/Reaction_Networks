import proofs.RandomViability.MarkedProductiveOutput

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_marked_reward_noise_failure (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (hreward : ∀ N ch,|reward N ch| ≤ (n : ℝ)/V)
    (hvariance : ∀ N,(countMass N : ℝ) ≤ 11*V →
      (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(reward N ch)^2) ≤ (384000+11*(n : ℝ))/V)
    (δ T eta : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (hmargin : δ+(n : ℝ)/V ≤ eta) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬markedRewardNoiseBound c V basal cat reward T eta z} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  apply le_trans (measure_mono ?_)
    (physical_marked_reward_two_sided_interval_tail hn c V hV basal cat N reward hreward hvariance δ T hδ hT)
  intro z hz
  simp only [markedRewardNoiseBound] at hz
  push Not at hz
  obtain ⟨k,s,h0,hs,hlarge⟩ := hz
  exact ⟨k,s,h0,hs,hmargin.trans hlarge.le⟩

theorem physical_export_noise_failure (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (δ T eta : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (hmargin : δ+(n : ℝ)/V ≤ eta) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬markedRewardNoiseBound c V basal cat (fun _ => exportReward V) T eta z} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) :=
  physical_marked_reward_noise_failure hn c V hV basal cat N (fun _ => exportReward V)
    (fun _ ch => by rw [abs_of_nonneg (export_reward_bounds V hV ch).1]; exact (export_reward_bounds V hV ch).2)
    (fun N hM => export_reward_common_variance c V hV basal cat N hM) δ T eta hδ hT hmargin

theorem physical_positive_basal_noise_failure (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (δ T eta : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (hmargin : δ+(n : ℝ)/V ≤ eta) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬markedRewardNoiseBound c V basal cat (positiveBasalReward V) T eta z} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) :=
  physical_marked_reward_noise_failure hn c V hV basal cat N (positiveBasalReward V)
    (fun N ch => by
      rw [abs_of_nonneg (positive_basal_reward_bounds V hV N ch).1]
      exact (positive_basal_reward_bounds V hV N ch).2.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hn) hV.le))
    (fun N hM => positive_basal_reward_common_variance c V hV basal cat N _
      (by norm_num) (by norm_num) hb hM) δ T eta hδ hT hmargin

end
end RandomViability
