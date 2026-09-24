import proofs.RandomViability.JumpTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 30000

variable {α β : Type*} [mα : MeasurableSpace α] [cα : Countable α]
  [sα : MeasurableSingletonClass α] [fβ : Fintype β]
  [mβ : MeasurableSpace β] [sβ : MeasurableSingletonClass β]

def jumpPositiveRate (rate : α → β → ℝ) (x : α) (y : JumpState α β) : Prop :=
  ∃ b, y.2.1 = Sum.inr b ∧ 0 < rate x b

theorem jumpPositiveRate_measurable (rate : α → β → ℝ) :
    MeasurableSet {p : α × JumpState α β | jumpPositiveRate rate p.1 p.2} := by
  unfold jumpPositiveRate
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro b
  have hl : MeasurableSet ((Sum.inr : β → Unit ⊕ β) '' {b}) :=
    (measurableSet_singleton b).inr_image
  have hl' : MeasurableSet ({Sum.inr b} : Set (Unit ⊕ β)) := by simpa using hl
  exact (hl'.preimage measurable_snd.snd.fst).inter
    (measurableSet_lt measurable_const
      ((measurable_of_countable (fun x => rate x b)).comp measurable_fst))

theorem jumpStateKernel_positive_rate (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) (x : α) :
    ∀ᵐ y ∂jumpStateKernel next rate hr ht x, jumpPositiveRate rate x y := by
  have hl : ∀ᵐ b ∂(jumpLabelPMF (rate x) (hr x) (ht x)).toMeasure, 0 < rate x b := by
    apply ae_iff_of_countable.mpr
    intro b hb
    by_contra hp
    have hz : rate x b = 0 := le_antisymm (le_of_not_gt hp) (hr x b)
    apply hb
    rw [PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b)]
    change ENNReal.ofReal (rate x b/(∑ c, rate x c)) = 0
    simp [hz]
  change ∀ᵐ y ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x), _
  apply (ae_map_iff (jumpStateUpdate_measurable next x).aemeasurable
    ((jumpPositiveRate_measurable rate).preimage (measurable_const.prodMk measurable_id))).mpr
  have hm : MeasurableSet {y : β × ℝ | jumpPositiveRate rate x (jumpStateUpdate next x y)} :=
    ((jumpPositiveRate_measurable rate).preimage
      (measurable_const.prodMk (jumpStateUpdate_measurable next x)))
  letI := isProbabilityMeasure_expMeasure (ht x)
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [hl] with b hb
  exact Eventually.of_forall (fun _ => ⟨b,rfl,hb⟩)

/-- Every actual jump, simultaneously over the countable history, has a
strictly positive propensity at its preceding population. -/
theorem jumpTrajectory_positive_rate (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    ∀ᵐ z ∂jumpTrajectoryLaw initial next rate hr ht, ∀ k, jumpPositiveRate rate (z k).1 (z (k+1)) := by
  apply ae_all_iff.mpr
  intro k
  have hm : Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β =>
      ((p.1 ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1, p.2)) :=
    (((measurable_pi_apply _).comp measurable_fst).fst).prodMk measurable_snd
  have ha : ∀ᵐ p ∂((jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) ⊗ₘ
      jumpHistoryKernel next rate hr ht k),
      jumpPositiveRate rate (p.1 ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 p.2 := by
    apply Measure.ae_compProd_of_ae_ae ((jumpPositiveRate_measurable rate).preimage hm)
    exact Eventually.of_forall (fun h => jumpStateKernel_positive_rate next rate hr ht
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
