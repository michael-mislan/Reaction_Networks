import proofs.CompositionalMemory.SemenovRecoveryKernel

namespace CompositionalMemory.Semenov
open MeasureTheory
open scoped ENNReal

noncomputable def offspringDensity (high : Bool) (x y : GoodRecoveryState high) (z : JointRawAllocation) : ℝ :=
  recoveryTransition
    (encodeReactor recoveryCountCap recoveryFeedQuota (refilledCounts (daughterAllocationA z))
      (allocationFeedCount (daughterAllocationA z))) y.val*
    (1-rawDaughterFailure high (daughterAllocationB (recoveryStateCounts x.val) z))

theorem offspring_density_bounds (high : Bool) (x y : GoodRecoveryState high) (z : JointRawAllocation) :
    0 ≤ offspringDensity high x y z ∧ offspringDensity high x y z ≤ 1 := by
  have ha := recovery_transition_bounds
    (encodeReactor recoveryCountCap recoveryFeedQuota (refilledCounts (daughterAllocationA z))
      (allocationFeedCount (daughterAllocationA z))) y.val
  have hb := raw_daughter_failure_bounds high (daughterAllocationB (recoveryStateCounts x.val) z)
  constructor
  · exact mul_nonneg ha.1 (sub_nonneg.mpr hb.2)
  · have hh := mul_le_mul ha.2 (sub_le_self (1 : ℝ) hb.1)
      (sub_nonneg.mpr hb.2) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [mul_one] using hh

theorem offspring_density_integrable (high : Bool) (x y : GoodRecoveryState high) :
    Integrable (offspringDensity high x y)
      (complementaryAllocationLaw (recoveryStateCounts x.val) recoveryFeedMeans) := by
  apply (integrable_const (1 : ℝ)).mono_nonneg (measurable_of_countable _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => (offspring_density_bounds high x y z).1)
  · exact Filter.Eventually.of_forall (fun z => (offspring_density_bounds high x y z).2)

noncomputable def offspringWeight (high : Bool) (x y : GoodRecoveryState high) : ℝ :=
  ∫ z,offspringDensity high x y z ∂complementaryAllocationLaw (recoveryStateCounts x.val) recoveryFeedMeans

theorem offspring_weight_nonneg (high : Bool) (x y : GoodRecoveryState high) :
    0 ≤ offspringWeight high x y := integral_nonneg (fun z => (offspring_density_bounds high x y z).1)

theorem offspring_weight_sum (high : Bool) (x : GoodRecoveryState high) :
    (∑ y,offspringWeight high x y)=bothDaughtersProbability high (recoveryStateCounts x.val) := by
  unfold offspringWeight bothDaughtersProbability
  rw [← integral_finsetSum _ (fun y _ => offspring_density_integrable high x y)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    unfold offspringDensity
    dsimp only
    rw [← Finset.sum_mul,recovery_transition_good_sum]
    rfl)

noncomputable def measuredOffspringKernel (high : Bool) : FiniteLineageKernel (GoodRecoveryState high) where
  weight x y := ENNReal.ofReal (offspringWeight high x y)
  total_le_one x := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => offspring_weight_nonneg high x y),offspring_weight_sum]
    exact ENNReal.ofReal_le_one.mpr (both_daughters_le_one high (recoveryStateCounts x.val))

theorem measured_offspring_total (high : Bool) (x : GoodRecoveryState high) :
    (124/125 : ℝ≥0∞) ≤ ∑ y,(measuredOffspringKernel high).weight x y := by
  change (124/125 : ℝ≥0∞) ≤ ∑ y,ENNReal.ofReal (offspringWeight high x y)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => offspring_weight_nonneg high x y),offspring_weight_sum]
  have hh := ENNReal.ofReal_le_ofReal (both_daughters_bound high (recoveryStateCounts x.val) (good_state_parent high x))
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 125),ENNReal.ofReal_ofNat] at hh
  exact hh

theorem measured_ten_divisions (high : Bool) (x : GoodRecoveryState high) :
    (9/10 : ℝ≥0∞) ≤ (measuredOffspringKernel high).survival 10 x := by
  apply (measuredOffspringKernel high).ten_cycles
  intro y
  have hh := ENNReal.ofReal_le_ofReal (by norm_num : (9901/10000 : ℝ) ≤ (124/125 : ℝ))
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10000),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 125)] at hh
  norm_num only [ENNReal.ofReal_ofNat] at hh
  exact hh.trans (measured_offspring_total high y)

end CompositionalMemory.Semenov
