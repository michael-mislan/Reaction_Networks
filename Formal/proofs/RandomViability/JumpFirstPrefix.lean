import proofs.RandomViability.JumpInitial

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

def firstPrefix {X : Type*} (initial y : X) : Finset.Iic (1 : ℕ) → X :=
  fun i => if (i : ℕ) = 0 then initial else y

def extendZeroPrefix {X : Type*} (p : (Finset.Iic (0 : ℕ) → X) × X) :
    Finset.Iic (1 : ℕ) → X := firstPrefix (p.1 ⟨0, Finset.mem_Iic.mpr le_rfl⟩) p.2

theorem firstPrefix_measurable {X : Type*} [MeasurableSpace X] (initial : X) :
    Measurable (firstPrefix initial) := by
  apply measurable_pi_lambda
  intro i
  unfold firstPrefix
  split_ifs
  · exact measurable_const
  · exact measurable_id

theorem extendZeroPrefix_measurable {X : Type*} [MeasurableSpace X] :
    Measurable (@extendZeroPrefix X) := by
  apply measurable_pi_lambda
  intro i
  unfold extendZeroPrefix firstPrefix
  split_ifs
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact measurable_snd

theorem extendZeroPrefix_restrict {X : Type*} (z : ℕ → X) :
    extendZeroPrefix (Preorder.frestrictLe 0 z, z 1) = Preorder.frestrictLe 1 z := by
  funext i
  change (if (i : ℕ) = 0 then z 0 else z 1) = z (i : ℕ)
  by_cases hi : (i : ℕ) = 0
  · simp [hi]
  · have hi1 : (i : ℕ) = 1 := by
      have hh := Finset.mem_Iic.mp i.property
      omega
    simp [hi1]

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The actual trajectory's first two coordinates, with the full first mark retained. -/
theorem jumpTrajectory_first_prefix (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    (jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe 1) =
      (jumpStateKernel next rate hr ht initial).map
        (firstPrefix ((initial, (Sum.inl (), (0 : ℝ))) : JumpState α β)) := by
  let μ := jumpTrajectoryLaw initial next rate hr ht
  have he := @Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (fun _ => JumpState α β) _ (jumpHistoryKernel next rate hr ht) _
    (Measure.dirac (initial, (Sum.inl (), (0 : ℝ)))) _ 0
  change μ.map (Preorder.frestrictLe 0) ⊗ₘ jumpHistoryKernel next rate hr ht 0 =
    μ.map (fun z => (Preorder.frestrictLe 0 z, z 1)) at he
  have hm : Measurable (fun z : ℕ → JumpState α β => (Preorder.frestrictLe 0 z, z 1)) := by
    fun_prop
  have hh : (μ.map (fun z => (Preorder.frestrictLe 0 z, z 1))).map extendZeroPrefix =
      μ.map (Preorder.frestrictLe 1) := by
    rw [Measure.map_map extendZeroPrefix_measurable hm]
    congr 1
    funext z
    exact extendZeroPrefix_restrict z
  change μ.map (Preorder.frestrictLe 1) = _
  rw [← hh, ← he]
  change ((jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe 0) ⊗ₘ
    jumpHistoryKernel next rate hr ht 0).map extendZeroPrefix = _
  rw [jumpTrajectory_initial_prefix]
  ext s hs
  rw [Measure.map_apply extendZeroPrefix_measurable hs,
    Measure.compProd_apply (extendZeroPrefix_measurable hs),
    lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left (extendZeroPrefix_measurable hs)),
    Measure.map_apply (firstPrefix_measurable _) hs]
  rfl

end
end RandomViability
