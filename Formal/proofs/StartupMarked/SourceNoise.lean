import proofs.StartupMarked.UniformBounds
import proofs.StartupMarked.RewardInterval
import Mathlib.Analysis.Complex.ExponentialBounds

namespace StartupMarked
open Classical RandomViability MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

theorem source_cutoff_tilt {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (θ : ℝ) (hθ : |θ| ≤ 1) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*
      (Real.exp (θ*cutoffReward V r stockCutoff N ch)-1)) ≤
      gammaRewardTilt cfg V basal cat (cutoffReward V r stockCutoff) θ (markedGamma V) N := by
  have hv : 0 < (V : ℝ) := by linarith
  have ht := rate_exponential_tilt_bound (unboundedPhysicalRate cfg V 1 basal cat N)
    (cutoffReward V r stockCutoff N) (unboundedPhysicalRate_nonneg cfg V 1 basal cat N) θ
    (fun ch => by
      rw [abs_mul]
      exact (mul_le_mul hθ ((cutoff_reward_abs V hv r N ch).trans
        (marked_jump_budget V hV).le) (abs_nonneg _) (by norm_num)).trans_eq (by ring))
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (cutoff_reward_bracket hn cfg V hv basal cat N r hb hc hfood hM hl hr hlen huw huz hwz)
    (sq_nonneg θ)))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem source_cutoff_interval_tail (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    physicalTrajectoryLaw hn cfg V 1 (by linarith) (by norm_num) basal cat N
      {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2 (200-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        15 ≤ |markedRewardWithinInterval cfg V basal cat (cutoffReward V r stockCutoff)
          200 (massExitStop V) z k s|} ≤ 2*ENNReal.ofReal (Real.exp (-10)) := by
  have hv : 0 < (V : ℝ) := by linarith
  have hg : 0 ≤ markedGamma V := by unfold markedGamma; positivity
  have hh := gamma_reward_interval_tail hn cfg V hv basal cat N (cutoffReward V r stockCutoff)
    (fun X ch => (cutoff_reward_abs V hv r X ch).trans (marked_jump_budget V hV).le)
    (markedGamma V) 200 14 hg (by norm_num)
    (fun θ hθ X hM => source_cutoff_tilt hn cfg V hV basal cat X r hb hc hfood hM
      hl hr hlen huw huz hwz θ hθ)
  norm_num only at hh
  apply hh.trans
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hbudget := marked_gamma_budget V hV
  linarith

theorem marked_noise_scalar : 2*Real.exp (-10) < (1/1000 : ℝ) := by
  have he : (9/4 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1/2 : ℝ)
    have hp := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3/2)
      (show (3/2 : ℝ) ≤ Real.exp (1/2) by linarith)
    rw [← Real.exp_add] at hp
    norm_num at hp
    exact hp
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9/4) he 10
  have hex : Real.exp (10 : ℝ) = (Real.exp 1)^10 := by
    norm_num [← Real.exp_nat_mul]
  have hbig : (2000 : ℝ) < Real.exp 10 := by
    rw [hex]
    exact (by norm_num : (2000 : ℝ) < (9/4 : ℝ)^10).trans_le hp
  rw [Real.exp_neg,← div_eq_mul_inv]
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith)

theorem marked_noise_sharp_scalar : 2*Real.exp (-10) < (99/1000000 : ℝ) := by
  have he : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10) he 10
  have hex : Real.exp (10 : ℝ) = (Real.exp 1)^10 := by norm_num [← Real.exp_nat_mul]
  have hb : (2000000/99 : ℝ) < Real.exp 10 := by
    rw [hex]
    exact (by norm_num : (2000000/99 : ℝ) < (27/10 : ℝ)^10).trans_le hp
  rw [Real.exp_neg,← div_eq_mul_inv]
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith)
end
end StartupMarked

