import proofs.RandomViability.JumpWaitingSupport

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 30000

theorem exponential_wait_pos (r : ℝ) : ∀ᵐ x ∂expMeasure r, 0 < x := by
  have hz : expMeasure r {0} = 0 := by
    change volume.withDensity (exponentialPDF r) {0} = 0
    rw [withDensity_apply _ (measurableSet_singleton _)]
    simp
  have hn : ∀ᵐ x ∂expMeasure r, x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not,Set.setOf_eq_eq_singleton] using hz
  filter_upwards [exponential_wait_nonneg r,hn] with x hx hne
  exact lt_of_le_of_ne hx (Ne.symm hne)
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jumpState_wait_pos (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) (x : α) :
    ∀ᵐ y ∂jumpStateKernel next rate hr ht x, 0 < y.2.2 := by
  change ∀ᵐ y ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x), 0 < y.2.2
  rw [ae_map_iff (jumpStateUpdate_measurable next x).aemeasurable
    (measurableSet_lt measurable_const measurable_snd.snd)]
  letI := isProbabilityMeasure_expMeasure (ht x)
  change ∀ᵐ y ∂(jumpLabelPMF (rate x) (hr x) (ht x)).toMeasure.prod (expMeasure (∑ b, rate x b)), 0 < y.2
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
  exact Eventually.of_forall (fun _ => exponential_wait_pos _)

theorem jumpTrajectory_wait_pos (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht, ∀ k, 0 < (z (k+1)).2.2 := by
  apply ae_all_iff.mpr
  intro k
  have ha : ∀ᵐ p ∂((jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) ⊗ₘ
      jumpHistoryKernel next rate hr ht k), 0 < p.2.2.2 := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_lt measurable_const measurable_snd.snd.snd)
    exact Eventually.of_forall (fun h => jumpState_wait_pos next rate hr ht
      (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1)
  have he := @Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (fun _ => JumpState α β) _ (jumpHistoryKernel next rate hr ht) _
    (Measure.dirac (initial, (Sum.inl (), (0 : ℝ)))) _ k
  change (jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) ⊗ₘ
    jumpHistoryKernel next rate hr ht k = (jumpTrajectoryLaw initial next rate hr ht).map
    (fun z => (Preorder.frestrictLe k z, z (k+1))) at he
  rw [he] at ha
  exact ae_of_ae_map (f := fun z : ℕ → JumpState α β =>
    (Preorder.frestrictLe k z, z (k+1))) (by fun_prop) ha

end
end RandomViability

