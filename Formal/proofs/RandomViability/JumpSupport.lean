import proofs.RandomViability.JumpTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def jumpConsistent (next : α → β → α) (x : α) (y : JumpState α β) : Prop :=
  ∃ b, y.2.1 = Sum.inr b ∧ y.1 = next x b

theorem jumpConsistent_measurable (next : α → β → α) :
    MeasurableSet {z : α × JumpState α β | jumpConsistent next z.1 z.2} := by
  unfold jumpConsistent
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro b
  have hl : MeasurableSet ((Sum.inr : β → Unit ⊕ β) '' {b}) :=
    (measurableSet_singleton b).inr_image
  have hl' : MeasurableSet ({Sum.inr b} : Set (Unit ⊕ β)) := by simpa using hl
  exact (hl'.preimage measurable_snd.snd.fst).inter
    (measurableSet_eq_fun measurable_snd.fst ((measurable_of_countable (fun x => next x b)).comp measurable_fst))

theorem jumpStateKernel_consistent (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) (x : α) :
    ∀ᵐ y ∂jumpStateKernel next rate hr ht x, jumpConsistent next x y := by
  change ∀ᵐ y ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x), _
  apply (ae_map_iff (jumpStateUpdate_measurable next x).aemeasurable
    ((jumpConsistent_measurable next).preimage (measurable_const.prodMk measurable_id))).mpr
  exact Filter.Eventually.of_forall (fun y => ⟨y.1, rfl, rfl⟩)

theorem jumpTrajectory_consistent (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht, ∀ k, jumpConsistent next (z k).1 (z (k+1)) := by
  apply ae_all_iff.mpr
  intro k
  have hm : Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β =>
      ((p.1 ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1, p.2)) :=
    (((measurable_pi_apply _).comp measurable_fst).fst).prodMk measurable_snd
  have ha : ∀ᵐ p ∂((jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) ⊗ₘ
      jumpHistoryKernel next rate hr ht k),
      jumpConsistent next (p.1 ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 p.2 := by
    apply Measure.ae_compProd_of_ae_ae ((jumpConsistent_measurable next).preimage hm)
    exact Filter.Eventually.of_forall (fun h => jumpStateKernel_consistent next rate hr ht (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1)
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
