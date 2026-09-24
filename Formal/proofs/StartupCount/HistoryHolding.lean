import proofs.StartupCount.ClockOccupation

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def holdingWeight (τ t u : ℝ) : ℝ≥0∞ := if τ ≤ t ∧ t < τ+u then 1 else 0

theorem holdingWeight_measurable (τ t : ℝ) : Measurable (holdingWeight τ t) :=
  Measurable.ite ((MeasurableSet.const _).inter (measurableSet_lt measurable_const
    (measurable_const.add measurable_id))) measurable_const measurable_const

theorem exp_holding_mean (R τ t : ℝ) :
    (∫⁻ u,holdingWeight τ t u ∂expMeasure R) = activeClockWeight R (t-τ) := by
  by_cases hτ : τ ≤ t
  · have he : holdingWeight τ t = (Ioi (t-τ)).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext u
      have hh : t < τ+u ↔ t-τ < u := by constructor <;> intro h <;> linarith
      simp only [holdingWeight,hτ,true_and,hh,Set.indicator,Set.mem_Ioi]
    rw [he,lintegral_indicator measurableSet_Ioi,lintegral_const,one_mul,
      Measure.restrict_apply_univ,activeClockWeight,if_pos (sub_nonneg.mpr hτ)]
  · simp only [holdingWeight,hτ,false_and,if_false,lintegral_zero,activeClockWeight,
      if_neg (fun h => hτ (sub_nonneg.mp h))]

theorem jumpState_holding_mean (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (x : α) (τ t : ℝ) :
    (∫⁻ y,holdingWeight τ t y.2.2 ∂jumpStateKernel next rate hr ht x) =
      activeClockWeight (∑ j,rate x j) (t-τ) := by
  letI := isProbabilityMeasure_expMeasure (ht x)
  change (∫⁻ y,holdingWeight τ t y.2.2
    ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x)) = _
  have hm : Measurable (fun y : JumpState α β => holdingWeight τ t y.2.2) :=
    (holdingWeight_measurable τ t).comp measurable_snd.snd
  rw [lintegral_map hm (jumpStateUpdate_measurable next x)]
  change (∫⁻ y,holdingWeight τ t y.2 ∂jumpClockMeasure (rate x) (hr x) (ht x)) = _
  unfold jumpClockMeasure
  have hm' : Measurable (fun y : β × ℝ => holdingWeight τ t y.2) :=
    (holdingWeight_measurable τ t).comp measurable_snd
  rw [lintegral_prod _ hm'.aemeasurable]
  simp only [exp_holding_mean,lintegral_const,measure_univ,mul_one]

/-- Actual active-holding payoff expressed by the predictable survival density. -/
theorem history_holding_density (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (k : ℕ) (τ : (Finset.Iic k → JumpState α β) → ℝ) (hτ : Measurable τ)
    (g : (Finset.Iic k → JumpState α β) → ℝ≥0∞) (hg : Measurable g) (t : ℝ) :
    (∫⁻ z,g (Preorder.frestrictLe k z)*holdingWeight (τ (Preorder.frestrictLe k z)) t (z (k+1)).2.2
      ∂jumpTrajectoryLaw initial next rate hr ht) =
    ∫⁻ h,g h*activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j) (t-τ h)
      ∂(jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) := by
  let μ := jumpTrajectoryLaw initial next rate hr ht
  let F : (Finset.Iic k → JumpState α β) × JumpState α β → ℝ≥0∞ :=
    fun p => g p.1*holdingWeight (τ p.1) t p.2.2.2
  have hm : Measurable F := by
    apply (hg.comp measurable_fst).mul
    apply Measurable.ite
      ((measurableSet_le (hτ.comp measurable_fst) measurable_const).inter
        (measurableSet_lt measurable_const ((hτ.comp measurable_fst).add measurable_snd.snd.snd)))
      measurable_const measurable_const
  have htransition : μ.map (Preorder.frestrictLe k) ⊗ₘ jumpHistoryKernel next rate hr ht k =
      μ.map (fun z => (Preorder.frestrictLe k z,z (k+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  change (∫⁻ z,F (Preorder.frestrictLe k z,z (k+1)) ∂μ) = _
  rw [← lintegral_map hm (by fun_prop),← htransition,Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro h
  simp only [F,jumpHistoryKernel,Kernel.comap_apply]
  have hy : Measurable (fun y : JumpState α β => holdingWeight (τ h) t y.2.2) :=
    (holdingWeight_measurable (τ h) t).comp measurable_snd.snd
  rw [lintegral_const_mul _ hy,
    jumpState_holding_mean]

end
end StartupCount
