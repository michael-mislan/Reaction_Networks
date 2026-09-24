import proofs.RandomViability.SingleIncidenceMassDefect
import proofs.RandomViability.MarkedCatalyticInput
import proofs.RandomViability.PhysicalCoordinateVariance

set_option Elab.async false
namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

/-- Half the positive internal modified-mass increment. Feed and washout are
handled separately in the pathwise balance. -/
def halfModifiedInputReward {n : ℕ} (p : Molecule n) (a : ℝ) (V : NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  match ch with
  | .inl _ => 0
  | .inr _ => max 0 (weightedCountMass (singleIncidenceWeight p a) (unboundedPhysicalNext N ch)-
      weightedCountMass (singleIncidenceWeight p a) N)/(2*V)

theorem half_modified_reward_bounds {n : ℕ} (p : Molecule n) (a : ℝ)
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (V : NNReal) (hV : 0 < (V : ℝ))
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    0 ≤ halfModifiedInputReward p a V N ch ∧ halfModifiedInputReward p a V N ch ≤ 4/V := by
  have internal (ch : PhysicalCountChannel n)
      (hm : (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)^2 ≤ 16) :
      max 0 (weightedCountMass (singleIncidenceWeight p a) (unboundedPhysicalNext N ch)-
        weightedCountMass (singleIncidenceWeight p a) N) ≤ 8 := by
    have hc := unbounded_coordinate_jump_sq N p ch
    have hm4 : countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N ≤ 4 := by
      nlinarith only [hm]
    have hc2 : -2 ≤ ((unboundedPhysicalNext N ch p : ℝ)-(N p : ℝ)) := by
      nlinarith only [hc]
    have hmulp := mul_le_mul_of_nonneg_left hc2 ha
    apply max_le (by norm_num)
    rw [singleIncidence_count_eq, singleIncidence_count_eq]
    nlinarith only [hm4, hmulp, ha2]
  rcases ch with external | (⟨r,d⟩ | ⟨r,z,d⟩)
  · simp only [halfModifiedInputReward]
    exact ⟨le_rfl, by positivity⟩
  · have hb := internal (.inr (.inl (r,d))) (unbounded_basal_nonfood_jump_sq N r d)
    constructor
    · exact div_nonneg (le_max_left _ _) (by positivity)
    · change _/(2*(V : ℝ)) ≤ _
      apply (div_le_iff₀ (by positivity : 0 < 2*(V : ℝ))).2
      calc
        _ ≤ 8 := hb
        _ = (4/(V : ℝ))*(2*V) := by field_simp; ring
  · have hb := internal (.inr (.inr (r,z,d))) (unbounded_catalytic_nonfood_jump_sq N r z d)
    constructor
    · exact div_nonneg (le_max_left _ _) (by positivity)
    · change _/(2*(V : ℝ)) ≤ _
      apply (div_le_iff₀ (by positivity : 0 < 2*(V : ℝ))).2
      calc
        _ ≤ 8 := hb
        _ = (4/(V : ℝ))*(2*V) := by field_simp; ring

theorem half_modified_local_reward_zero {n : ℕ} (r : Reaction n) (z : Molecule n)
    (d : Bool) (V : NNReal) (N : Molecule n → ℕ) :
    halfModifiedInputReward (reactionProduct r) (ligationNonfoodMassGain r) V N
      (.inr (.inr (r,z,d))) = 0 := by
  simp only [halfModifiedInputReward, singleIncidence_count_invariant, sub_self, max_self, zero_div]

theorem half_modified_reward_variance {n : ℕ} (hn : 2 ≤ n)
    (p : Molecule n) (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hc : ∀ r z,(cat r z : ℝ) ≤ 16) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(halfModifiedInputReward p a V N ch)^2) ≤
      (384000+11*(n : ℝ))/V := by
  calc
    _ ≤ ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(4/(V : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro ch _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (half_modified_reward_bounds p a ha ha2 V hV N ch).1
          (half_modified_reward_bounds p a ha ha2 V hV N ch).2 2)
        (unboundedPhysicalRate_nonneg c V 1 basal cat N ch)
    _ = (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch)*(4/(V : ℝ))^2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (24000*V)*(4/(V : ℝ))^2 := mul_le_mul_of_nonneg_right
      (unbounded_total_rate_mass_eleven hn c V hV basal cat N hM hb hc) (sq_nonneg _)
    _ = 384000/(V : ℝ) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ n by positivity]) hV.le

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The actual stopped count-process concentration bound, with all scale
parameters explicit. No deterministic approximation or noise independence. -/
theorem physical_half_modified_reward_noise_failure (hn : 4 ≤ n)
    (p : Molecule n) (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (δ T eta : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hmargin : δ+(n : ℝ)/V ≤ eta) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬markedRewardNoiseBound c V basal cat (halfModifiedInputReward p a V) T eta z} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  apply physical_marked_reward_noise_failure hn c V hV basal cat N
    (halfModifiedInputReward p a V) _ _ δ T eta hδ hT hmargin
  · intro N ch
    rw [abs_of_nonneg (half_modified_reward_bounds p a ha ha2 V hV N ch).1]
    exact (half_modified_reward_bounds p a ha ha2 V hV N ch).2.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hn) hV.le)
  · intro N hM
    exact half_modified_reward_variance (by omega) p a ha ha2 c V hV basal cat N hM hb hc

end
end RandomViability
