import proofs.RandomViability.JumpRestart

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

theorem restart_wait_sum {α β : Type*} (z : ℕ → JumpState α β) (k : ℕ) :
    (∑ i ∈ Finset.range (k+1), (z (i+1)).2.2) =
      (z 1).2.2 + ∑ i ∈ Finset.range k, (restartJump z (i+1)).2.2 := by
  rw [Finset.sum_range_succ']
  change (∑ i ∈ Finset.range k, (z (i+2)).2.2) + (z 1).2.2 =
    (z 1).2.2 + ∑ i ∈ Finset.range k, (z (i+2)).2.2
  exact add_comm _ _

theorem restart_wait_deadline {α β : Type*} (z : ℕ → JumpState α β) (k : ℕ) (T : ℝ) :
    (∑ i ∈ Finset.range (k+1), (z (i+1)).2.2) ≤ T ↔
      (∑ i ∈ Finset.range k, (restartJump z (i+1)).2.2) ≤ T-(z 1).2.2 := by
  rw [restart_wait_sum]
  constructor <;> intro h <;> linarith

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The conditional future, with the new initial mark reset, is the fresh physical jump law. -/
theorem jumpTrajectory_restart_law (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (h1 : Finset.Iic (1 : ℕ) → JumpState α β) :
    (Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1).map
      restartJump = jumpTrajectoryLaw (h1 ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1 next rate hr ht := by
  let ν := Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1
  letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hfirst : ν.map (Preorder.frestrictLe 1) = Measure.dirac h1 := by
    dsimp [ν]
    rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
  apply trajectory_law_unique (ν.map restartJump)
    (jumpTrajectoryLaw (h1 ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1 next rate hr ht)
    (jumpHistoryKernel next rate hr ht)
  · rw [restart_prefix_map, hfirst, Measure.map_dirac' (restartPrefix_measurable 0),
      jumpTrajectory_initial_prefix]
    congr 1
    funext i
    have hi : (i : ℕ) = 0 := by have hh := Finset.mem_Iic.mp i.property; omega
    simp only [restartPrefix, hi, if_true]
  · intro k
    have hc : ν.map (Preorder.frestrictLe (k+1)) ⊗ₘ jumpHistoryKernel next rate hr ht (k+1) =
        ν.map (fun z => (Preorder.frestrictLe (k+1) z, z (k+2))) := by
      dsimp [ν]
      rw [Kernel.traj_map_frestrictLe_apply]
      exact Kernel.partialTraj_compProd_eq_map_traj (by omega : 1 ≤ k+1)
    rw [restart_prefix_map]
    rw [← map_compProd_first (ν.map (Preorder.frestrictLe (k+1)))
      (jumpHistoryKernel next rate hr ht (k+1)) (jumpHistoryKernel next rate hr ht k)
      (restartPrefix k) (restartPrefix_measurable k)
      (fun h => (restart_history_kernel next rate hr ht k h).symm)]
    rw [hc, Measure.map_map ((restartPrefix_measurable k).prodMap measurable_id) (by fun_prop),
      Measure.map_map (by fun_prop) restartJump_measurable]
    congr 1
    funext z
    exact Prod.ext (restartPrefix_restrict k z) rfl
  · intro k
    exact @Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (fun _ => JumpState α β) _ (jumpHistoryKernel next rate hr ht) _
      (Measure.dirac ((h1 ⟨1, Finset.mem_Iic.mpr le_rfl⟩).1, (Sum.inl (), (0 : ℝ)))) _ k

end
end RandomViability
