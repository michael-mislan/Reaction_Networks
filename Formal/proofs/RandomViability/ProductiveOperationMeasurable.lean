import proofs.RandomViability.ProductiveOperation
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

omit [MeasurableSingletonClass (PhysicalCountChannel n)] in
theorem productive_clock_measurable (i : ℕ) :
    Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      productiveClock (fun j => (z (j+1)).2.2) i) := by
  unfold productiveClock
  fun_prop

theorem operating_marked_sum_measurable (g : Unit ⊕ PhysicalCountChannel n → ℝ) :
    Measurable (operatingMarkedSum (α := Molecule n → ℕ) g) := by
  unfold operatingMarkedSum
  apply Measurable.tsum
  intro i
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const (productive_clock_measurable (i+1))).inter
      (measurableSet_le (productive_clock_measurable (i+1)) measurable_const)
  · exact (measurable_fun_sum (measurable_of_countable _) (measurable_of_countable _)).comp
      (measurable_pi_apply (i+1)).snd.fst
  · exact measurable_const

theorem startup_operating_marked_sum_measurable (g : Unit ⊕ PhysicalCountChannel n → ℝ) :
    Measurable (startupOperatingMarkedSum (α := Molecule n → ℕ) g) := by
  unfold startupOperatingMarkedSum
  apply Measurable.tsum
  intro i
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const (productive_clock_measurable (i+1))).inter
      (measurableSet_le (productive_clock_measurable (i+1)) measurable_const)
  · exact (measurable_fun_sum (measurable_of_countable _) (measurable_of_countable _)).comp
      (measurable_pi_apply (i+1)).snd.fst
  · exact measurable_const

theorem productive_operation_measurable (r : Reaction n) (V m : ℕ) :
    MeasurableSet {z | ProductiveOperation r V m z} := by
  have hclock := productive_clock_measurable (n := n)
  have hcount (i : ℕ) (x : Molecule n) :
      Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
        (z i).1 x) := (measurable_pi_apply x).comp (measurable_pi_apply i).fst
  have hmass (i : ℕ) :
      Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
        countMass (z i).1) := (measurable_of_countable countMass).comp (measurable_pi_apply i).fst
  have hs := operating_marked_sum_measurable (targetSignedCatalytic r)
  have he := operating_marked_sum_measurable (targetProductExport r)
  have hb := startup_operating_marked_sum_measurable (n := n) basalMassCharge
  unfold ProductiveOperation
  measurability

end
end RandomViability
