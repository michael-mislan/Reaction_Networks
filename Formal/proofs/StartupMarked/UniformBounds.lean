import proofs.StartupMarked.SourceBracket
import proofs.StartupMarked.SourceMarkedDrift

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

def stockCutoff : ℕ := 333334
def markedGamma (V : ℝ) : ℝ := 6146*333334/(333332 : ℝ)^2+196608000/V
def markedJump (V : ℝ) : ℝ := 2/333332+32/V

theorem large_count_fraction (K : ℝ) (hK : 333334 ≤ K) :
    K/(K-2)^2 ≤ 333334/(333332 : ℝ)^2 := by
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith)) (by norm_num)).mpr
  have hh := mul_nonneg (show 0 ≤ K-333334 by linarith)
    (show 0 ≤ 333334*K-4 by linarith)
  nlinarith only [hh]

theorem marked_gamma_budget (V : ℝ) (hV : 1000000000000000000000000 ≤ V) :
    200*markedGamma V < 4 := by
  have hsmall := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 196608000)
    (by norm_num : (0 : ℝ) < 1000000000000000000000000) hV
  have hh : markedGamma V ≤ 6146*333334/(333332 : ℝ)^2+196608000/1000000000000000000000000 :=
    add_le_add le_rfl hsmall
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 200)).trans_lt (by norm_num)

theorem marked_jump_budget (V : ℝ) (hV : 1000000000000000000000000 ≤ V) :
    markedJump V < 1 := by
  have hsmall := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 32)
    (by norm_num : (0 : ℝ) < 1000000000000000000000000) hV
  have hh : markedJump V ≤ (2/333332 : ℝ)+32/1000000000000000000000000 := add_le_add le_rfl hsmall
  exact hh.trans_lt (by norm_num)

theorem marked_drift_margin (V K : ℝ) (hV : 1000000000000000000000000 ≤ V) (hK : 333334 ≤ K) :
    19/10 ≤ 2-468*(1/500000000 : ℝ)-(6146/K+3072000/V) := by
  have hk := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6146)
    (by norm_num : (0 : ℝ) < 333334) hK
  have hv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3072000)
    (by norm_num : (0 : ℝ) < 1000000000000000000000000) hV
  have hfixed : (19/10 : ℝ) ≤ 2-468*(1/500000000 : ℝ)-
      (6146/333334+3072000/1000000000000000000000000) := by norm_num
  exact hfixed.trans (sub_le_sub le_rfl (add_le_add hk hv))

theorem cutoff_reward_abs {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    |cutoffReward V r stockCutoff N ch| ≤ markedJump V := by
  by_cases hK : stockCutoff ≤ N (reactionProduct r)
  · rw [cutoff_agrees_above_floor V r stockCutoff N ch hK]
    have hk : (333334 : ℝ) ≤ N (reactionProduct r) := by exact_mod_cast hK
    apply (retained_reward_abs V hV r N ch (by change 333334 ≤ _ at hK; omega)).trans
    exact add_le_add (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 333332)
      (by linarith : (333332 : ℝ) ≤ (N (reactionProduct r) : ℝ)-2)) le_rfl
  · rw [cutoffReward,if_neg hK,abs_zero]
    dsimp [markedJump]
    positivity

theorem cutoff_reward_bracket {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*(cutoffReward V r stockCutoff N ch)^2) ≤
      markedGamma V := by
  by_cases hK : stockCutoff ≤ N (reactionProduct r)
  · simp only [cutoffReward,if_pos hK]
    have hk : (333334 : ℝ) ≤ N (reactionProduct r) := by exact_mod_cast hK
    apply (source_retained_reward_bracket hn cfg V hV basal cat N r hb hc hfood hM hl hr hlen
      huw huz hwz (by change 333334 ≤ _ at hK; omega)).trans
    have hh := mul_le_mul_of_nonneg_left (large_count_fraction _ hk) (by norm_num : (0 : ℝ) ≤ 6146)
    have he : 6146*(N (reactionProduct r) : ℝ)/((N (reactionProduct r) : ℝ)-2)^2 ≤
        6146*333334/(333332 : ℝ)^2 := by simpa only [mul_div_assoc] using hh
    exact add_le_add he le_rfl
  · simp only [cutoffReward,if_neg hK,zero_pow (by decide : 2 ≠ 0),mul_zero,Finset.sum_const_zero]
    dsimp [markedGamma]
    positivity

end
end StartupMarked
