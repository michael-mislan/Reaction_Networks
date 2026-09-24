import proofs.RandomViability.MarkedRewardNoise

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

def normalizedPositiveCatalyticReward {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) : ℝ :=
  match ch with
  | .inr (.inr _) => max 0 (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V
  | _ => 0

theorem positive_catalytic_reward_bounds {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    0 ≤ normalizedPositiveCatalyticReward V N ch ∧ normalizedPositiveCatalyticReward V N ch ≤ 4/V := by
  rcases ch with (f|q)|(b|⟨r,z,d⟩)
  · simp only [normalizedPositiveCatalyticReward]
    exact ⟨le_rfl,by positivity⟩
  · simp only [normalizedPositiveCatalyticReward]
    exact ⟨le_rfl,by positivity⟩
  · simp only [normalizedPositiveCatalyticReward]
    exact ⟨le_rfl,by positivity⟩
  · have hh := unbounded_catalytic_nonfood_jump_sq N r z d
    have hu : countNonfoodMass (unboundedPhysicalNext N (.inr (.inr (r,z,d))))-countNonfoodMass N ≤ 4 := by
      nlinarith only [hh]
    exact ⟨div_nonneg (le_max_left _ _) hV.le,
      div_le_div_of_nonneg_right (max_le (by norm_num) hu) hV.le⟩

theorem positive_catalytic_drift_identity {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    markedRewardDrift c V basal cat (normalizedPositiveCatalyticReward V) N =
      boundedCatalyticUptake c V 1 basal cat (countsAtOwnMass N)/V := by
  rw [boundedCatalyticUptake_eq_actual_positive]
  simp only [markedRewardDrift,Fintype.sum_sum_type,Fintype.sum_prod_type,
    normalizedPositiveCatalyticReward,mul_zero,Finset.sum_const_zero,zero_add,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro d _
  have he := bounded_unbounded_next_agree c V 1 basal cat (countsAtOwnMass N)
    (.inr (.inr (r,z,d))) (by change countMass N+0 ≤ countMass N; omega)
  rw [he]
  change unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,d))) *
      (max 0 (countNonfoodMass (unboundedPhysicalNext N (.inr (.inr (r,z,d))))-countNonfoodMass N)/V) =
    unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,d))) *
      max 0 (countNonfoodMass (unboundedPhysicalNext N (.inr (.inr (r,z,d))))-countNonfoodMass N)/V
  ring

theorem positive_catalytic_drift_short_bound {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ShortIncidence k c) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16) :
    (k : ℝ)*markedRewardDrift c V basal cat (normalizedPositiveCatalyticReward V) N ≤ 85184 := by
  have hh := boundedCatalyticUptake_mass_bound c hgood V 1 hV basal cat (countsAtOwnMass N)
    16 (by norm_num) hcat
  change (k : ℝ)*boundedCatalyticUptake c V 1 basal cat (countsAtOwnMass N) ≤
    4*16*V*((countMass N : ℝ)/V)^3 at hh
  have hm : (countMass N : ℝ)/V ≤ 11 := (div_le_iff₀ hV).2 hM
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (countMass N : ℝ)/V) hm 3
  have hu : 4*16*(V : ℝ)*((countMass N : ℝ)/V)^3 ≤ 85184*V := by
    nlinarith only [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (V : ℝ))]
  rw [positive_catalytic_drift_identity,← mul_div_assoc]
  exact (div_le_iff₀ hV).2 (hh.trans hu)

def collectiveUpperCutoff : ℕ := 400000000

theorem positive_catalytic_drift_small {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ShortIncidence collectiveUpperCutoff c) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16) :
    markedRewardDrift c V basal cat (normalizedPositiveCatalyticReward V) N ≤ 1/4000 := by
  have hh := positive_catalytic_drift_short_bound c hgood V hV basal cat N hM hcat
  norm_num [collectiveUpperCutoff] at hh
  linarith only [hh]

theorem positive_catalytic_reward_common_variance {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hc : ∀ r z,(cat r z : ℝ) ≤ 16) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(normalizedPositiveCatalyticReward V N ch)^2) ≤
      (384000+11*(n : ℝ))/V := by
  calc
    _ ≤ ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(4/(V : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro ch _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (positive_catalytic_reward_bounds V hV N ch).1
          (positive_catalytic_reward_bounds V hV N ch).2 2)
        (unboundedPhysicalRate_nonneg c V 1 basal cat N ch)
    _ = (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch)*(4/(V : ℝ))^2 := (Finset.sum_mul _ _ _).symm
    _ ≤ (24000*V)*(4/(V : ℝ))^2 := mul_le_mul_of_nonneg_right
      (unbounded_total_rate_mass_eleven hn c V hV basal cat N hM hb hc) (sq_nonneg _)
    _ = 384000/(V : ℝ) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ n by positivity]) hV.le

end
end RandomViability
