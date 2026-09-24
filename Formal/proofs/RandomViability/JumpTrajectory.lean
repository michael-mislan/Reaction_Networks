import proofs.RandomViability.JumpClockKernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.MapComap

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

abbrev JumpState (α β : Type*) := α × ((Unit ⊕ β) × ℝ)

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def jumpStateUpdate (next : α → β → α) (x : α) (y : β × ℝ) : JumpState α β :=
  (next x y.1,(Sum.inr y.1,y.2))

omit [Countable α] [MeasurableSingletonClass α] in
theorem jumpStateUpdate_measurable (next : α → β → α) (x : α) : Measurable (jumpStateUpdate next x) := by
  exact ((measurable_of_countable (next x)).comp measurable_fst).prodMk
    (((measurable_of_countable (fun b : β => (Sum.inr b : Unit ⊕ β))).comp measurable_fst).prodMk measurable_snd)

def jumpStateKernel (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) : Kernel α (JumpState α β) :=
  Kernel.ofFunOfCountable (fun x => (jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x))

instance jumpStateKernel_markov (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) : IsMarkovKernel (jumpStateKernel next rate hr ht) where
  isProbabilityMeasure x := Measure.isProbabilityMeasure_map (jumpStateUpdate_measurable next x).aemeasurable

def jumpHistoryKernel (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) (k : ℕ) :
    Kernel (Finset.Iic k → JumpState α β) (JumpState α β) :=
  (jumpStateKernel next rate hr ht).comap (fun h => (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1)
    (measurable_pi_apply (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).fst

instance jumpHistoryKernel_markov (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) (k : ℕ) :
    IsMarkovKernel (jumpHistoryKernel next rate hr ht k) := by
  unfold jumpHistoryKernel
  infer_instance

def jumpTrajectoryLaw (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) : Measure (ℕ → JumpState α β) :=
  Kernel.trajMeasure (X := fun _ => JumpState α β)
    (Measure.dirac (initial,(Sum.inl (), (0 : ℝ)))) (jumpHistoryKernel next rate hr ht)

instance jumpTrajectoryLaw_probability (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    IsProbabilityMeasure (jumpTrajectoryLaw initial next rate hr ht) := by
  unfold jumpTrajectoryLaw
  infer_instance

end
end RandomViability

