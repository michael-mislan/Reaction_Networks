import proofs.RandomViability.MarkedRewardNoise

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

/-- Gross molecules supplied across all six food channels, divided by V. -/
def grossFeedReward {n : ℕ} (V : NNReal) : PhysicalCountChannel n → ℝ
  | .inl (.inl _) => 1/V
  | _ => 0

theorem gross_feed_reward_bounds {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (ch : PhysicalCountChannel n) : 0 ≤ grossFeedReward V ch ∧ grossFeedReward V ch ≤ 1/V := by
  rcases ch with (f|q)|(b|c) <;> simp only [grossFeedReward] <;>
    constructor <;> first | exact le_rfl | positivity

theorem gross_feed_drift {n : ℕ} (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    markedRewardDrift c V basal cat (fun _ => grossFeedReward V) N = 6 := by
  have hcard : Fintype.card ↥(binaryFood n 2) = 6 :=
    (Fintype.card_congr (foodWordEquiv hn)).trans (by decide)
  have hc : (binaryFood n 2).card = 6 := by simpa only [Fintype.card_coe] using hcard
  simp only [markedRewardDrift,Fintype.sum_sum_type,grossFeedReward,mul_zero,
    Finset.sum_const_zero,add_zero,unbounded_feed_rate,NNReal.coe_one,one_mul]
  simp [hV.ne',hc]

theorem gross_feed_variance {n : ℕ} (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(grossFeedReward V ch)^2) ≤
      (384000+11*(n : ℝ))/V := by
  have hq : (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(grossFeedReward V ch)^2) ≤
      (1/(V : ℝ))*markedRewardDrift c V basal cat (fun _ => grossFeedReward V) N := by
    unfold markedRewardDrift
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ch _
    have hb := gross_feed_reward_bounds V hV ch
    have hr := unboundedPhysicalRate_nonneg c V 1 basal cat N ch
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb.2 hb.1) hr]
  rw [gross_feed_drift hn c V hV basal cat N] at hq
  apply hq.trans
  rw [one_div_mul_eq_div]
  apply div_le_div_of_nonneg_right _ hV.le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  linarith only [hn0]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_gross_feed_noise_failure (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (δ T eta : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hmargin : δ+(n : ℝ)/V ≤ eta) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬markedRewardNoiseBound c V basal cat (fun _ => grossFeedReward V) T eta z} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  apply physical_marked_reward_noise_failure hn c V hV basal cat N
    (fun _ => grossFeedReward V)
  · intro _ ch
    rw [abs_of_nonneg (gross_feed_reward_bounds V hV ch).1]
    exact (gross_feed_reward_bounds V hV ch).2.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast (show 1 ≤ n by omega)) hV.le)
  · intro N _
    exact gross_feed_variance (by omega) c V hV basal cat N
  · exact hδ
  · exact hT
  · exact hmargin

end
end RandomViability
