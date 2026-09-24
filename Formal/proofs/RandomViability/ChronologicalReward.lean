import proofs.RandomViability.JumpRestartLaw
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000
variable {α β : Type*}

def jumpElapsed (z : ℕ → JumpState α β) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (z (i+1)).2.2

def jumpEarned (g : α → β → ℝ≥0∞) (z : ℕ → JumpState α β) (k : ℕ) : ℝ≥0∞ :=
  (z (k+1)).2.1.elim (fun _ => 0) (g (z k).1)

/-- Nonnegative reward carried by genuine marked jumps whose cumulative time is at most T. -/
def chronologicalReward (g : α → β → ℝ≥0∞) (T : ℝ) (z : ℕ → JumpState α β) : ℝ≥0∞ :=
  ∑' k, if jumpElapsed z (k+1) ≤ T then jumpEarned g z k else 0

theorem restart_jumpEarned (g : α → β → ℝ≥0∞) (z : ℕ → JumpState α β) (k : ℕ) :
    jumpEarned g (restartJump z) k = jumpEarned g z (k+1) := by
  cases k <;> rfl

theorem chronologicalReward_split (g : α → β → ℝ≥0∞) (T : ℝ) (z : ℕ → JumpState α β) :
    chronologicalReward g T z =
      (if (z 1).2.2 ≤ T then jumpEarned g z 0 else 0) +
        chronologicalReward g (T-(z 1).2.2) (restartJump z) := by
  unfold chronologicalReward
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : jumpElapsed z (0+1) = (z 1).2.2 := by simp [jumpElapsed]
  rw [h0]
  congr 1
  apply tsum_congr
  intro k
  have he : jumpElapsed z (k+1+1) ≤ T ↔
      jumpElapsed (restartJump z) (k+1) ≤ T-(z 1).2.2 := restart_wait_deadline z (k+1) T
  by_cases htime : jumpElapsed z (k+1+1) ≤ T
  · rw [if_pos htime, if_pos (he.mp htime), restart_jumpEarned]
  · rw [if_neg htime, if_neg (fun h => htime (he.mpr h))]

variable [MeasurableSpace α] [MeasurableSpace β]

theorem jumpElapsed_measurable (k : ℕ) : Measurable (fun z : ℕ → JumpState α β => jumpElapsed z k) := by
  unfold jumpElapsed
  fun_prop

variable [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [Fintype β] in
theorem markSingletonClass : MeasurableSingletonClass (Unit ⊕ β) := by
  constructor
  intro b
  cases b with
  | inl u => simpa only [Set.image_singleton] using (measurableSet_singleton u).inl_image
  | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image

theorem jumpEarned_measurable (g : α → β → ℝ≥0∞) (k : ℕ) :
    Measurable (fun z : ℕ → JumpState α β => jumpEarned g z k) := by
  letI := markSingletonClass (β := β)
  have hm : Measurable (fun p : α × (Unit ⊕ β) => p.2.elim (fun _ => (0 : ℝ≥0∞)) (g p.1)) :=
    measurable_of_countable _
  exact hm.comp (((measurable_pi_apply k).fst).prodMk ((measurable_pi_apply (k+1)).snd.fst))

theorem chronologicalReward_measurable (g : α → β → ℝ≥0∞) :
    Measurable (fun p : ℝ × (ℕ → JumpState α β) => chronologicalReward g p.1 p.2) := by
  unfold chronologicalReward
  apply Measurable.tsum
  intro k
  exact Measurable.ite
    (measurableSet_le ((jumpElapsed_measurable (k+1)).comp measurable_snd) measurable_fst)
    ((jumpEarned_measurable g k).comp measurable_snd) measurable_const

end
end RandomViability
