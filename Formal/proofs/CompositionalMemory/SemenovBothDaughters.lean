import proofs.CompositionalMemory.SemenovReturnBound
import proofs.CompositionalMemory.SemenovComplementaryAllocation

namespace CompositionalMemory.Semenov
open MeasureTheory

noncomputable def rawDaughterFailure (high : Bool) (z : RawAllocation) : ℝ :=
  finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
    500 (recoveryFailure high)
    (encodeReactor recoveryCountCap recoveryFeedQuota (refilledCounts z) (allocationFeedCount z))

theorem raw_daughter_failure_bounds (high : Bool) (z : RawAllocation) :
    0 ≤ rawDaughterFailure high z ∧ rawDaughterFailure high z ≤ 1 :=
  finite_time_bounds _ 500 _ (recovery_failure_bounds high) _

noncomputable def bothDaughtersProbability (high : Bool) (n : Fin 8 → ℕ) : ℝ :=
  ∫ z,(1-rawDaughterFailure high (daughterAllocationA z))*
    (1-rawDaughterFailure high (daughterAllocationB n z)) ∂complementaryAllocationLaw n recoveryFeedMeans

private theorem bounded_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : ∀ x,0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono_nonneg (measurable_of_countable f).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => (hf x).1)
  · exact Filter.Eventually.of_forall (fun x => (hf x).2)

theorem both_daughters_conditional_bounds (high : Bool) (n : Fin 8 → ℕ) (z : JointRawAllocation) :
    0 ≤ (1-rawDaughterFailure high (daughterAllocationA z))*(1-rawDaughterFailure high (daughterAllocationB n z)) ∧
      (1-rawDaughterFailure high (daughterAllocationA z))*(1-rawDaughterFailure high (daughterAllocationB n z)) ≤ 1 := by
  have ha := raw_daughter_failure_bounds high (daughterAllocationA z)
  have hb := raw_daughter_failure_bounds high (daughterAllocationB n z)
  constructor
  · exact mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
  · have hh := mul_le_mul (sub_le_self (1 : ℝ) ha.1) (sub_le_self (1 : ℝ) hb.1)
      (sub_nonneg.mpr hb.2) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [mul_one] using hh

theorem both_daughters_bound (high : Bool) (n : Fin 8 → ℕ) (hn : GoodRecoveryParent high n) :
    (124/125 : ℝ) ≤ bothDaughtersProbability high n := by
  let μ := complementaryAllocationLaw n recoveryFeedMeans
  let a (z : JointRawAllocation) := rawDaughterFailure high (daughterAllocationA z)
  let b (z : JointRawAllocation) := rawDaughterFailure high (daughterAllocationB n z)
  have ha := bounded_integrable μ a (fun z => raw_daughter_failure_bounds high (daughterAllocationA z))
  have hb := bounded_integrable μ b (fun z => raw_daughter_failure_bounds high (daughterAllocationB n z))
  have hp := bounded_integrable μ (fun z => (1-a z)*(1-b z)) (both_daughters_conditional_bounds high n)
  have hpoint (z : JointRawAllocation) : 1-a z-b z ≤ (1-a z)*(1-b z) := by
    have hab := mul_nonneg (raw_daughter_failure_bounds high (daughterAllocationA z)).1
      (raw_daughter_failure_bounds high (daughterAllocationB n z)).1
    dsimp only [a,b] at *
    nlinarith only [hab]
  have hh := integral_mono (((integrable_const (1 : ℝ)).sub ha).sub hb) hp hpoint
  simp only [Pi.sub_apply] at hh
  have hs := integral_sub ((integrable_const (1 : ℝ)).sub ha) hb
  simp only [Pi.sub_apply] at hs
  rw [hs,integral_sub (integrable_const (1 : ℝ)) ha,integral_const] at hh
  norm_num only [probReal_univ,one_smul] at hh
  have hA : (∫ z,a z ∂μ)=daughterFailureProbability high n :=
    complementary_integral_A n recoveryFeedMeans (rawDaughterFailure high)
  have hB : (∫ z,b z ∂μ)=daughterFailureProbability high n :=
    complementary_integral_B n recoveryFeedMeans (rawDaughterFailure high)
  rw [hA,hB] at hh
  have hd := daughter_failure_bound high n hn
  change _ ≤ bothDaughtersProbability high n at hh
  linarith only [hh,hd]

theorem both_daughters_le_one (high : Bool) (n : Fin 8 → ℕ) :
    bothDaughtersProbability high n ≤ 1 := by
  have hi := bounded_integrable (complementaryAllocationLaw n recoveryFeedMeans) _
    (both_daughters_conditional_bounds high n)
  have hh := integral_mono hi (integrable_const (1 : ℝ))
    (fun z => (both_daughters_conditional_bounds high n z).2)
  rw [integral_const] at hh
  simpa only [probReal_univ,one_smul] using hh

end CompositionalMemory.Semenov
