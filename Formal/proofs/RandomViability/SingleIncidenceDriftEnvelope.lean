import proofs.RandomViability.PhysicalInternalLoss
import proofs.RandomViability.SingleIncidenceErasure
import proofs.RandomViability.ShortTargetTailLoss

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

private theorem positive_defect_le (m d a : ℝ) (ha : 0 ≤ a) :
    max 0 (m-a*d) ≤ max 0 m+a*max 0 (-d) := by
  have hm := le_max_right 0 m
  have hd := mul_le_mul_of_nonneg_left (le_max_right 0 (-d)) ha
  have hn := mul_nonneg ha (le_max_left 0 (-d))
  apply max_le
  · linarith [le_max_left 0 m]
  · nlinarith only [hm,hd]

theorem half_modified_reward_le_inputs {n : ℕ} (p : Molecule n) (a : ℝ)
    (ha : 0 ≤ a) (V : NNReal) (hV : 0 < (V : ℝ)) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) :
    2*halfModifiedInputReward p a V N ch ≤ positiveBasalReward V N ch+
      normalizedPositiveCatalyticReward V N ch+a*internalCoordinateLossReward p V N ch := by
  have hg (m d : ℝ) : 2*(max 0 (m-a*d)/(2*(V : ℝ))) ≤
      max 0 m/V+a*(max 0 (-d)/V) := by
    have hh := div_le_div_of_nonneg_right (positive_defect_le m d a ha) hV.le
    convert hh using 1 <;> field_simp
  have he (ch : PhysicalCountChannel n) :
      weightedCountMass (singleIncidenceWeight p a) (unboundedPhysicalNext N ch)-
        weightedCountMass (singleIncidenceWeight p a) N =
      (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)-
        a*((unboundedPhysicalNext N ch p : ℝ)-(N p : ℝ)) := by
    rw [singleIncidence_count_eq,singleIncidence_count_eq]
    ring
  have hc (ch : PhysicalCountChannel n) : (N p : ℝ)-(unboundedPhysicalNext N ch p : ℝ) =
      -((unboundedPhysicalNext N ch p : ℝ)-(N p : ℝ)) := by ring
  rcases ch with external | (b|c)
  · simp [halfModifiedInputReward,positiveBasalReward,normalizedPositiveCatalyticReward,internalCoordinateLossReward]
  · simpa only [halfModifiedInputReward,positiveBasalReward,normalizedPositiveCatalyticReward,
      internalCoordinateLossReward,add_zero,he,hc] using hg
        (countNonfoodMass (unboundedPhysicalNext N (.inr (.inl b)))-countNonfoodMass N)
        ((unboundedPhysicalNext N (.inr (.inl b)) p : ℝ)-(N p : ℝ))
  · simpa only [halfModifiedInputReward,positiveBasalReward,normalizedPositiveCatalyticReward,
      internalCoordinateLossReward,zero_add,he,hc] using hg
        (countNonfoodMass (unboundedPhysicalNext N (.inr (.inr c)))-countNonfoodMass N)
        ((unboundedPhysicalNext N (.inr (.inr c)) p : ℝ)-(N p : ℝ))

theorem half_modified_drift_le_envelopes {n : ℕ} (p : Molecule n) (a : ℝ)
    (ha : 0 ≤ a) (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    2*markedRewardDrift c V basal cat (halfModifiedInputReward p a V) N ≤
      markedRewardDrift c V basal cat (positiveBasalReward V) N+
      markedRewardDrift c V basal cat (normalizedPositiveCatalyticReward V) N+
      a*collectiveLoss (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z)
        (fun z => (N z : ℝ)/V)) (fun z => (N z : ℝ)/V) p := by
  have hp := physical_internal_loss_le_envelope p V hV c basal cat N
  have hs : 2*markedRewardDrift c V basal cat (halfModifiedInputReward p a V) N ≤
      markedRewardDrift c V basal cat (positiveBasalReward V) N+
      markedRewardDrift c V basal cat (normalizedPositiveCatalyticReward V) N+
      a*markedRewardDrift c V basal cat (internalCoordinateLossReward p V) N := by
    unfold markedRewardDrift
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ch _
    have hh := mul_le_mul_of_nonneg_left (half_modified_reward_le_inputs p a ha V hV N ch)
      (unboundedPhysicalRate_nonneg c V 1 basal cat N ch)
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hp ha
  linarith only [hs,hh]

end
end RandomViability
