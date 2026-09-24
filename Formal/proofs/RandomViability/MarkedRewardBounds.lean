import proofs.RandomViability.MarkedBasalInput
import proofs.RandomViability.MarkedRewardClock
import proofs.RandomViability.CollectiveHost

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem count_nonfood_normalized {n : ℕ} (N : Molecule n → ℕ) (V : NNReal) :
    countNonfoodMass N/V = nonfoodMass (fun q => (N q : ℝ)/V) := by
  simp only [countNonfoodMass,weightedCountMass,nonfoodMass,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  unfold foodMassWeight
  by_cases h : molLength q ≤ 2
  · simp [h,show ¬2 < molLength q by omega]
  · simp only [if_neg h,if_pos (show 2 < molLength q by omega),sub_zero]
    ring

theorem count_nonfood_le_mass {n : ℕ} (N : Molecule n → ℕ) :
    countNonfoodMass N ≤ (countMass N : ℝ) := by
  simp only [countNonfoodMass,weightedCountMass,countMass,Nat.cast_sum,Nat.cast_mul]
  apply Finset.sum_le_sum
  intro q _
  have hw : 0 ≤ foodMassWeight q := by unfold foodMassWeight; split_ifs <;> positivity
  exact mul_le_mul_of_nonneg_right (sub_le_self _ hw) (Nat.cast_nonneg _)

theorem export_reward_common_variance {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (hM : (countMass N : ℝ) ≤ 11*V) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(exportReward V ch)^2) ≤
      (384000+11*(n : ℝ))/V := by
  have hm : countNonfoodMass N/V ≤ 11 := (div_le_iff₀ hV).2 ((count_nonfood_le_mass N).trans hM)
  calc
    _ ≤ ((n : ℝ)/V)*(countNonfoodMass N/V) := export_reward_quadratic c V hV basal cat N
    _ ≤ ((n : ℝ)/V)*11 := mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ _ := by apply (le_div_iff₀ hV).2; field_simp; nlinarith

theorem positive_basal_reward_common_variance {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 4*eps) (hM : (countMass N : ℝ) ≤ 11*V) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(positiveBasalReward V N ch)^2) ≤
      (384000+11*(n : ℝ))/V := by
  calc
    _ ≤ (4/(V : ℝ))*(∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*positiveBasalReward V N ch) :=
      positive_basal_reward_quadratic c V hV basal cat N
    _ ≤ (4/(V : ℝ))*(1936*eps) := mul_le_mul_of_nonneg_left
      (positive_basal_reward_drift c V hV basal cat N eps heps hbasal hM) (by positivity)
    _ ≤ (4/(V : ℝ))*1936 := mul_le_mul_of_nonneg_left (by linarith only [heps1]) (by positivity)
    _ ≤ _ := by apply (le_div_iff₀ hV).2; field_simp; nlinarith [show (0 : ℝ) ≤ n by positivity]

theorem marked_reward_tilt_generator {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (N : Molecule n → ℕ)
    (hb : ∀ ch,|reward N ch| ≤ (n : ℝ)/V)
    (hq : (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(reward N ch)^2) ≤ (384000+11*(n : ℝ))/V)
    (θ : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(Real.exp (θ*reward N ch)-1)) ≤
      markedRewardTilt c V basal cat reward θ N := by
  have ht := rate_exponential_tilt_bound (unboundedPhysicalRate c V 1 basal cat N)
    (reward N) (unboundedPhysicalRate_nonneg c V 1 basal cat N) θ (fun ch => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hb ch) (abs_nonneg θ)).trans hθ)
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hq (sq_nonneg θ)))

theorem export_reward_tilt_generator {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (hM : (countMass N : ℝ) ≤ 11*V) (θ : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(Real.exp (θ*exportReward V ch)-1)) ≤
      markedRewardTilt c V basal cat (fun _ => exportReward V) θ N :=
  marked_reward_tilt_generator c V basal cat (fun _ => exportReward V) N
    (fun ch => by rw [abs_of_nonneg (export_reward_bounds V hV ch).1]; exact (export_reward_bounds V hV ch).2)
    (export_reward_common_variance c V hV basal cat N hM) θ hθ

theorem positive_basal_reward_tilt_generator {n : ℕ} (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 4*eps) (hM : (countMass N : ℝ) ≤ 11*V)
    (θ : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(Real.exp (θ*positiveBasalReward V N ch)-1)) ≤
      markedRewardTilt c V basal cat (positiveBasalReward V) θ N :=
  marked_reward_tilt_generator c V basal cat (positiveBasalReward V) N
    (fun ch => by
      rw [abs_of_nonneg (positive_basal_reward_bounds V hV N ch).1]
      exact (positive_basal_reward_bounds V hV N ch).2.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hn) hV.le))
    (positive_basal_reward_common_variance c V hV basal cat N eps heps heps1 hbasal hM) θ hθ

end
end RandomViability
