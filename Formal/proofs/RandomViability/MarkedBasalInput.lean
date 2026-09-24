import proofs.RandomViability.MarkedExport

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- Positive nonfood mass input on basal marks, using the actual enabled next state. -/
def positiveBasalReward {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) : ℝ :=
  match ch with
  | .inr (.inl _) => max 0 (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V
  | _ => 0

theorem positive_basal_reward_reverse {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (r : Reaction n) : positiveBasalReward V N (.inr (.inl (r,false))) = 0 := by
  have hg := (ligation_nonfood_gain_le_four r).1
  unfold positiveBasalReward
  by_cases he : ∀ x,physicalChannelInput (.inr (.inl (r,false))) x ≤ N x
  · rw [unboundedPhysicalNext,if_pos he,basal_nonfood_raw_change N r false he]
    simp only [Bool.false_eq_true,if_false]
    rw [max_eq_left (by linarith),zero_div]
  · simp [unboundedPhysicalNext,he]

theorem positive_basal_reward_bounds {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    0 ≤ positiveBasalReward V N ch ∧ positiveBasalReward V N ch ≤ 4/V := by
  rcases ch with (f|q)|(⟨r,d⟩|c)
  · simp only [positiveBasalReward]
    exact ⟨le_rfl,by positivity⟩
  · simp only [positiveBasalReward]
    exact ⟨le_rfl,by positivity⟩
  · cases d with
    | false =>
      rw [positive_basal_reward_reverse]
      exact ⟨le_rfl,by positivity⟩
    | true =>
      have hg := ligation_nonfood_gain_le_four r
      unfold positiveBasalReward
      by_cases he : ∀ x,physicalChannelInput (.inr (.inl (r,true))) x ≤ N x
      · rw [unboundedPhysicalNext,if_pos he,basal_nonfood_raw_change N r true he]
        simp only [if_true,max_eq_right hg.1]
        exact ⟨div_nonneg hg.1 hV.le,div_le_div_of_nonneg_right hg.2 hV.le⟩
      · simp [unboundedPhysicalNext,he]
        positivity
  · simp only [positiveBasalReward]
    exact ⟨le_rfl,by positivity⟩

theorem positive_basal_reward_drift {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (eps : ℝ) (heps : 0 ≤ eps) (hbasal : ∀ r,(basal r : ℝ) ≤ 4*eps)
    (hM : (countMass N : ℝ) ≤ 11*V) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch * positiveBasalReward V N ch) ≤ 1936*eps := by
  let R := unboundedPhysicalRate c V 1 basal cat N
  have hsum : (∑ r : Reaction n,R (.inr (.inl (r,true)))) ≤ 484*eps*V := by
    have hp := count_pair_sum_le_mass_sq N
    calc
      _ ≤ ∑ r : Reaction n,4*eps*((N (reactionLeft r) : ℝ)*N (reactionRight r))/V := by
        apply Finset.sum_le_sum
        intro r _
        have hh := bounded_basal_ligation_rate_le c V 1 hV basal cat (countsAtOwnMass N) r
        change R (.inr (.inl (r,true))) ≤ (basal r : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r))/V at hh
        exact hh.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbasal r) (by positivity)) hV.le)
      _ = (4*eps/V)*(∑ r : Reaction n,(N (reactionLeft r) : ℝ)*N (reactionRight r)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ ≤ (4*eps/V)*(countMass N : ℝ)^2 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (4*eps/V)*(11*(V : ℝ))^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hM 2) (by positivity)
      _ = _ := by field_simp; ring
  have he : (∑ ch,R ch*positiveBasalReward V N ch) =
      ∑ r : Reaction n,R (.inr (.inl (r,true)))*positiveBasalReward V N (.inr (.inl (r,true))) := by
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
      positive_basal_reward_reverse,mul_zero,add_zero]
    simp only [positiveBasalReward,mul_zero,Finset.sum_const_zero,zero_add,add_zero]
  change (∑ ch,R ch*positiveBasalReward V N ch) ≤ _
  rw [he]
  calc
    _ ≤ ∑ r : Reaction n,R (.inr (.inl (r,true)))*(4/V) := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left (positive_basal_reward_bounds V hV N _).2
        (unboundedPhysicalRate_nonneg c V 1 basal cat N _)
    _ = (∑ r : Reaction n,R (.inr (.inl (r,true))))*(4/V) := (Finset.sum_mul _ _ _).symm
    _ ≤ (484*eps*V)*(4/V) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := by field_simp; ring

theorem positive_basal_reward_quadratic {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch * (positiveBasalReward V N ch)^2) ≤
      (4/(V : ℝ))*(∑ ch,unboundedPhysicalRate c V 1 basal cat N ch * positiveBasalReward V N ch) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ch _
  have hb := positive_basal_reward_bounds V hV N ch
  have hr := unboundedPhysicalRate_nonneg c V 1 basal cat N ch
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb.2 hb.1) hr]

end
end RandomViability
