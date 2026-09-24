import proofs.RandomViability.CollectiveMassCorridor

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem coordinate_raw_change {n : ℕ} (N input output : Molecule n → ℕ)
    (he : ∀ z,input z ≤ N z) (q : Molecule n) :
    (applyCountChannel N input output q : ℝ)-(N q : ℝ) = (output q : ℝ)-(input q : ℝ) := by
  simp only [applyCountChannel,Nat.cast_add,Nat.cast_sub (he q)]
  ring

theorem singleCount_real_bounds {n : ℕ} (z q : Molecule n) :
    0 ≤ (singleCount z q : ℝ) ∧ (singleCount z q : ℝ) ≤ 1 := by
  unfold singleCount
  split_ifs <;> norm_num

theorem basal_coordinate_raw_change {n : ℕ} (N : Molecule n → ℕ)
    (r : Reaction n) (d : Bool) (q : Molecule n)
    (he : ∀ z,physicalChannelInput (.inr (.inl (r,d))) z ≤ N z) :
    (applyCountChannel N (physicalChannelInput (.inr (.inl (r,d))))
      (physicalChannelOutput (.inr (.inl (r,d)))) q : ℝ)-(N q : ℝ) =
      if d then (singleCount (reactionProduct r) q : ℝ)-
        ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)
      else ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)-
        singleCount (reactionProduct r) q := by
  rw [coordinate_raw_change N _ _ he]
  cases d <;> simp [physicalChannelInput,physicalChannelOutput,Nat.cast_add]

theorem catalytic_coordinate_raw_change {n : ℕ} (N : Molecule n → ℕ)
    (r : Reaction n) (x : Molecule n) (d : Bool) (q : Molecule n)
    (he : ∀ z,physicalChannelInput (.inr (.inr (r,x,d))) z ≤ N z) :
    (applyCountChannel N (physicalChannelInput (.inr (.inr (r,x,d))))
      (physicalChannelOutput (.inr (.inr (r,x,d)))) q : ℝ)-(N q : ℝ) =
      if d then (singleCount (reactionProduct r) q : ℝ)-
        ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)
      else ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)-
        singleCount (reactionProduct r) q := by
  rw [coordinate_raw_change N _ _ he]
  cases d <;> simp [physicalChannelInput,physicalChannelOutput,Nat.cast_add]

theorem reaction_coordinate_jump_sq {n : ℕ} (r : Reaction n) (q : Molecule n) (d : Bool) :
    (if d then (singleCount (reactionProduct r) q : ℝ)-
      ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)
    else ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)-
      singleCount (reactionProduct r) q)^2 ≤ 4 := by
  have hl := singleCount_real_bounds (reactionLeft r) q
  have hr := singleCount_real_bounds (reactionRight r) q
  have hp := singleCount_real_bounds (reactionProduct r) q
  have ha : |((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)-
      singleCount (reactionProduct r) q| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hh := pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hsq : (((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)-
      singleCount (reactionProduct r) q)^2 ≤ 4 := by
    simpa only [sq_abs,show (2 : ℝ)^2 = 4 by norm_num] using hh
  cases d with
  | false =>
    change (((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)-
      singleCount (reactionProduct r) q)^2 ≤ 4
    exact hsq
  | true =>
    change ((singleCount (reactionProduct r) q : ℝ)-
      ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q))^2 ≤ 4
    nlinarith only [hsq]

theorem unbounded_coordinate_jump_sq {n : ℕ} (N : Molecule n → ℕ)
    (q : Molecule n) (ch : PhysicalCountChannel n) :
    ((unboundedPhysicalNext N ch q : ℝ)-(N q : ℝ))^2 ≤ 4 := by
  by_cases he : ∀ z,physicalChannelInput ch z ≤ N z
  · rw [unboundedPhysicalNext,if_pos he]
    rcases ch with (f|x)|(⟨r,d⟩|⟨r,x,d⟩)
    · rw [coordinate_raw_change N _ _ he]
      simp only [physicalChannelInput,physicalChannelOutput,Nat.cast_zero,sub_zero]
      have hh := singleCount_real_bounds f.val q
      nlinarith
    · rw [coordinate_raw_change N _ _ he]
      simp only [physicalChannelInput,physicalChannelOutput,Nat.cast_zero,zero_sub,neg_sq]
      have hh := singleCount_real_bounds x q
      nlinarith
    · rw [basal_coordinate_raw_change N r d q he]
      exact reaction_coordinate_jump_sq r q d
    · rw [catalytic_coordinate_raw_change N r x d q he]
      exact reaction_coordinate_jump_sq r q d
  · simp only [unboundedPhysicalNext,if_neg he,sub_self,zero_pow (by decide : 2 ≠ 0)]
    norm_num

def coordinateConcentrationJump {n : ℕ} (V : NNReal) (q : Molecule n)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  ((unboundedPhysicalNext N ch q : ℝ)-(N q : ℝ))/V

theorem coordinate_concentration_jump_bound {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (q : Molecule n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    |coordinateConcentrationJump V q N ch| ≤ 2/V := by
  have hh := unbounded_coordinate_jump_sq N q ch
  have ha : |(unboundedPhysicalNext N ch q : ℝ)-(N q : ℝ)| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  unfold coordinateConcentrationJump
  rw [abs_div,abs_of_pos hV]
  exact div_le_div_of_nonneg_right ha hV.le

theorem physical_coordinate_quadratic_rate {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16) (q : Molecule n) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(coordinateConcentrationJump V q N ch)^2) ≤
      96000/V := by
  have hr := unbounded_total_rate_mass_eleven hn c V hV basal cat N hM hbasal hcat
  calc
    _ ≤ ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(4/(V : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro ch _
      apply mul_le_mul_of_nonneg_left _ (unboundedPhysicalRate_nonneg c V 1 basal cat N ch)
      simp only [coordinateConcentrationJump,div_pow]
      exact div_le_div_of_nonneg_right (unbounded_coordinate_jump_sq N q ch) (sq_nonneg _)
    _ = (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch)*(4/(V : ℝ)^2) := (Finset.sum_mul _ _ _).symm
    _ ≤ (24000*V)*(4/(V : ℝ)^2) := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by field_simp; ring

end
end RandomViability
