import proofs.RandomViability.ChronologicalReward

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def chronologicalTest (g : α → β → ℝ≥0∞) (T : ℝ) (a s : ℝ≥0∞)
    (z : ℕ → JumpState α β) : ℝ≥0∞ :=
  if s ≤ a + chronologicalReward g T z then 1 else 0

theorem chronologicalTest_measurable (g : α → β → ℝ≥0∞) (T : ℝ) (a s : ℝ≥0∞) :
    Measurable (chronologicalTest g T a s) := by
  have hc : Measurable (fun z : ℕ → JumpState α β => chronologicalReward g T z) :=
    (chronologicalReward_measurable g).comp (measurable_const.prodMk measurable_id)
  exact Measurable.ite (measurableSet_le measurable_const (measurable_const.add hc))
    measurable_const measurable_const

def physicalChronologicalTail (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (g : α → β → ℝ≥0∞) (initial : α) (T : ℝ) (a s : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z, chronologicalTest g T a s z ∂jumpTrajectoryLaw initial next rate hr ht

theorem physicalChronologicalTail_eq_measure (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (g : α → β → ℝ≥0∞) (initial : α) (T : ℝ) (a s : ℝ≥0∞) :
    physicalChronologicalTail next rate hr ht g initial T a s =
      jumpTrajectoryLaw initial next rate hr ht {z | s ≤ a + chronologicalReward g T z} := by
  have hc : Measurable (fun z : ℕ → JumpState α β => chronologicalReward g T z) :=
    (chronologicalReward_measurable g).comp (measurable_const.prodMk measurable_id)
  have hs : MeasurableSet {z | s ≤ a + chronologicalReward g T z} :=
    measurableSet_le measurable_const (measurable_const.add hc)
  simpa only [physicalChronologicalTail, chronologicalTest, Set.indicator, Set.mem_setOf_eq,
    Pi.one_apply] using
      (lintegral_indicator_one (μ := jumpTrajectoryLaw initial next rate hr ht) hs)

theorem continuation_prefix_ae (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (h1 : Finset.Iic (1 : ℕ) → JumpState α β) :
    ∀ᵐ z ∂Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1,
      Preorder.frestrictLe 1 z = h1 := by
  letI := markSingletonClass (β := β)
  have hh : ∀ᵐ h ∂(Kernel.traj (X := fun _ => JumpState α β)
      (jumpHistoryKernel next rate hr ht) 1 h1).map (Preorder.frestrictLe 1), h = h1 := by
    rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
    exact (ae_dirac_iff (measurableSet_singleton h1)).mpr rfl
  exact ae_of_ae_map (f := Preorder.frestrictLe 1) (by fun_prop) hh

/-- Exact renewal of the actual chronological reward event through its first physical channel.
The accumulator a keeps the first reward explicit; the deadline is reduced by the first wait. -/
theorem physicalChronologicalTail_renewal (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (g : α → β → ℝ≥0∞) (initial : α) (T : ℝ) (a s : ℝ≥0∞) :
    physicalChronologicalTail next rate hr ht g initial T a s =
      ∫⁻ y, physicalChronologicalTail next rate hr ht g (next initial y.1) (T-y.2)
        (a + if y.2 ≤ T then g initial y.1 else 0) s
        ∂jumpClockMeasure (rate initial) (hr initial) (ht initial) := by
  unfold physicalChronologicalTail
  rw [jumpTrajectory_first_jump_lintegral initial next rate hr ht
    (chronologicalTest g T a s) (chronologicalTest_measurable g T a s)]
  apply lintegral_congr
  intro y
  let h1 := firstMarkedPrefix initial next y
  let ν := Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1
  let a1 : ℝ≥0∞ := a + if y.2 ≤ T then g initial y.1 else 0
  have he : ∀ᵐ z ∂ν, chronologicalTest g T a s z =
      chronologicalTest g (T-y.2) a1 s (restartJump z) := by
    filter_upwards [continuation_prefix_ae next rate hr ht h1] with z hz
    have hz0 : z 0 = (initial, (Sum.inl (), (0 : ℝ))) :=
      congrFun hz ⟨0, Finset.mem_Iic.mpr (by omega)⟩
    have hz1 : z 1 = jumpStateUpdate next initial y :=
      congrFun hz ⟨1, Finset.mem_Iic.mpr le_rfl⟩
    have hw : (z 1).2.2 = y.2 := congrArg (fun v : JumpState α β => v.2.2) hz1
    have hg0 : jumpEarned g z 0 = g initial y.1 := by
      unfold jumpEarned
      rw [hz0, hz1]
      rfl
    have hh := chronologicalReward_split g T z
    rw [hw, hg0] at hh
    simp only [chronologicalTest, hh, a1, add_assoc]
  calc
    _ = ∫⁻ z, chronologicalTest g (T-y.2) a1 s (restartJump z) ∂ν := lintegral_congr_ae he
    _ = ∫⁻ z, chronologicalTest g (T-y.2) a1 s z ∂ν.map restartJump :=
      (lintegral_map' (chronologicalTest_measurable g (T-y.2) a1 s).aemeasurable
        restartJump_measurable.aemeasurable).symm
    _ = _ := by
      rw [jumpTrajectory_restart_law]
      rfl

end
end RandomViability
