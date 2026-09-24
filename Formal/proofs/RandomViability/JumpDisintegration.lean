import proofs.RandomViability.JumpFirstPrefix

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The conditional continuation retains all already observed marks and waiting times. -/
theorem jumpTrajectory_continue (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) (k : ℕ) :
    jumpTrajectoryLaw initial next rate hr ht =
      Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) k ∘ₘ
        (jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) := by
  unfold jumpTrajectoryLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe k), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Kernel.traj_comp_partialTraj (Nat.zero_le k)]

def firstMarkedPrefix (initial : α) (next : α → β → α) (y : β × ℝ) :
    Finset.Iic (1 : ℕ) → JumpState α β :=
  firstPrefix (initial, (Sum.inl (), (0 : ℝ))) (jumpStateUpdate next initial y)

omit [Countable α] [MeasurableSingletonClass α] in
theorem firstMarkedPrefix_measurable (initial : α) (next : α → β → α) :
    Measurable (firstMarkedPrefix initial next) :=
  (firstPrefix_measurable _).comp (jumpStateUpdate_measurable next initial)

/-- Exact first-jump disintegration of the actual infinite marked trajectory law. -/
theorem jumpTrajectory_first_jump_disintegration (initial : α) (next : α → β → α)
    (rate : α → β → ℝ) (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    jumpTrajectoryLaw initial next rate hr ht =
      Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 ∘ₘ
        (jumpClockMeasure (rate initial) (hr initial) (ht initial)).map
          (firstMarkedPrefix initial next) := by
  rw [jumpTrajectory_continue initial next rate hr ht 1, jumpTrajectory_first_prefix]
  change Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 ∘ₘ
    ((jumpClockMeasure (rate initial) (hr initial) (ht initial)).map (jumpStateUpdate next initial)).map
      (firstPrefix (initial, (Sum.inl (), (0 : ℝ)))) = _
  rw [Measure.map_map (firstPrefix_measurable _) (jumpStateUpdate_measurable next initial)]
  rfl

/-- Nonnegative path observables may be integrated by conditioning on the first physical jump. -/
theorem jumpTrajectory_first_jump_lintegral (initial : α) (next : α → β → α)
    (rate : α → β → ℝ) (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (f : (ℕ → JumpState α β) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂jumpTrajectoryLaw initial next rate hr ht) =
      ∫⁻ y, ∫⁻ z, f z ∂Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1
        (firstMarkedPrefix initial next y)
        ∂jumpClockMeasure (rate initial) (hr initial) (ht initial) := by
  rw [jumpTrajectory_first_jump_disintegration initial next rate hr ht]
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  exact lintegral_map' hf.lintegral_kernel.aemeasurable
    (firstMarkedPrefix_measurable initial next).aemeasurable

end
end RandomViability
