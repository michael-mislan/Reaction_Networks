import proofs.StartupMarked.FoodBracket

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem retained_change_abs {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    |retainedChange r N ch| ≤ 2 := by
  unfold retainedChange
  split_ifs
  · have hs := unbounded_coordinate_jump_sq N (reactionProduct r) ch
    apply abs_le.mpr
    constructor <;> nlinarith only [hs]
  · norm_num

theorem retained_log_abs {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) (hK : 2 < N (reactionProduct r)) :
    |retainedLog r N ch| ≤ 2/((N (reactionProduct r) : ℝ)-2) := by
  have hk : (2 : ℝ) < N (reactionProduct r) := by exact_mod_cast hK
  have hd := retained_change_lower r N ch
  have hh := log_difference_lipschitz (N (reactionProduct r) : ℝ)
    ((N (reactionProduct r) : ℝ)+retainedChange r N ch)
    ((N (reactionProduct r) : ℝ)-2) (by linarith) (by linarith) (by linarith)
  rw [← retained_log_as_change,add_sub_cancel_left] at hh
  exact hh.trans (div_le_div_of_nonneg_right (retained_change_abs r N ch) (by linarith))

theorem retained_reward_abs {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n)
    (hK : 2 < N (reactionProduct r)) :
    |retainedReward V r N ch| ≤ 2/((N (reactionProduct r) : ℝ)-2)+32/(V : ℝ) := by
  have ht := abs_sub_le (retainedLog r N ch) 0
    (foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N)
  simp only [sub_zero,zero_sub,abs_neg] at ht
  exact ht.trans (add_le_add (retained_log_abs r N ch hK)
    (food_penalty_jump_abs V hV r N ch))

theorem source_retained_reward_bracket {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
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
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hK : 2 < N (reactionProduct r)) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*(retainedReward V r N ch)^2) ≤
      6146*(N (reactionProduct r) : ℝ)/((N (reactionProduct r) : ℝ)-2)^2+196608000/(V : ℝ) := by
  let R := unboundedPhysicalRate cfg V 1 basal cat N
  let F := fun ch => foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N
  let K : ℝ := N (reactionProduct r)
  have hlog : (∑ ch,R ch*(retainedLog r N ch)^2) ≤ 3073*K/(K-2)^2 := by
    apply (physical_retained_log_square cfg V basal cat r N huz hwz hK).trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hs := selected_forward_rate_le cfg V hV basal cat N r (hc r _) hM huw hl hr
    have ha := adverse_copy_flux_bound cfg V hV basal cat N hb hc hfood hM (reactionProduct r) hlen
    dsimp [K]
    linarith only [hs,ha]
  have hR : (∑ ch,R ch) ≤ 96000*V := by
    have hh := unbounded_total_rate_mass_eleven hn cfg V hV basal cat N hM
      (fun rr => (hb rr).trans (by norm_num)) hc
    dsimp [R]
    linarith
  have hF (ch : PhysicalCountChannel n) : (F ch)^2 ≤ (32/(V : ℝ))^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (food_penalty_jump_abs V hV r N ch) 2
    simpa only [sq_abs] using hh
  have hfoodvar : (∑ ch,R ch*(F ch)^2) ≤ 98304000/(V : ℝ) := by
    calc
      _ ≤ ∑ ch,R ch*(32/(V : ℝ))^2 := Finset.sum_le_sum (fun ch _ =>
        mul_le_mul_of_nonneg_left (hF ch) (unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch))
      _ = (∑ ch,R ch)*(32/(V : ℝ))^2 := (Finset.sum_mul ..).symm
      _ ≤ (96000*V)*(32/(V : ℝ))^2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
      _ = _ := by field_simp; ring
  have hsplit : (∑ ch,R ch*(retainedReward V r N ch)^2) ≤
      2*(∑ ch,R ch*(retainedLog r N ch)^2)+2*(∑ ch,R ch*(F ch)^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ch _
    have hh : (retainedReward V r N ch)^2 ≤ 2*(retainedLog r N ch)^2+2*(F ch)^2 := by
      dsimp [retainedReward,F]
      nlinarith [sq_nonneg (retainedLog r N ch+
        (foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N))]
    have hh' := mul_le_mul_of_nonneg_left hh (unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch)
    dsimp [R]
    nlinarith only [hh']
  apply hsplit.trans
  exact (add_le_add (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hfoodvar (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by dsimp [K]; ring)

end
end StartupMarked
