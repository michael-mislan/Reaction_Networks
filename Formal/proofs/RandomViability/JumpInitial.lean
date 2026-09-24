import proofs.RandomViability.JumpTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jumpTrajectory_initial_prefix (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    (jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ : Finset.Iic (0 : ℕ) => (initial, (Sum.inl (), (0 : ℝ))) :
        Finset.Iic (0 : ℕ) → JumpState α β) := by
  unfold jumpTrajectoryLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (by fun_prop)]
  rfl

theorem jumpTrajectory_initial_population (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht, (z 0).1 = initial := by
  have h : ∀ᵐ h ∂(jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe 0),
      (h ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 = initial := by
    rw [jumpTrajectory_initial_prefix]
    exact (ae_dirac_iff (measurableSet_eq_fun
      (measurable_pi_apply (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (0 : ℕ))).fst
      measurable_const)).mpr rfl
  exact ae_of_ae_map (f := Preorder.frestrictLe 0) (by fun_prop) h

end
end RandomViability
