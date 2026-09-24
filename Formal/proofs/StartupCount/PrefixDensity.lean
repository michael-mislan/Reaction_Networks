import proofs.StartupCount.PrefixReadiness
import proofs.StartupCount.AbsoluteClockOccupation

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def lowPrefixWeight (guard : α → Prop) (count : α → ℕ) (b k : ℕ)
    (h : Finset.Iic k → JumpState α β) (t : ℝ) : ℝ≥0∞ :=
  if readyPrefix guard k h t ∧ count (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 ≤ b then 1 else 0

omit [Fintype β] [MeasurableSingletonClass β] in
theorem lowPrefixWeight_joint (guard : α → Prop) (count : α → ℕ) (b k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState α β) × ℝ =>
      lowPrefixWeight guard count b k p.1 p.2) := by
  apply Measurable.ite
    ((readyPrefix_measurableSet guard k).inter
      ((Set.to_countable {x : α | count x ≤ b}).measurableSet.preimage
        (((measurable_pi_apply (⟨k,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp
          measurable_fst).fst))) measurable_const measurable_const

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
theorem lowPrefix_holding_eq (guard : α → Prop) (count : α → ℕ) (b k : ℕ)
    (t : ℝ) (z : ℕ → JumpState α β) :
    lowPrefixWeight guard count b k (Preorder.frestrictLe k z) t *
      holdingWeight (prefixElapsed k (Preorder.frestrictLe k z)) t (z (k+1)).2.2 =
    (guardedLowAt guard count b k t).indicator (fun _ => (1 : ℝ≥0∞)) z := by
  have hs : jumpElapsed z (k+1) = jumpElapsed z k+(z (k+1)).2.2 := by
    unfold jumpElapsed
    rw [Finset.sum_range_succ]
  have hr : readyPrefix guard k (Preorder.frestrictLe k z) t → jumpElapsed z k ≤ t := by
    intro hh
    exact ((readyPrefix_restrict guard k z t).mp hh).2 k le_rfl
  rw [prefixElapsed_eq_jumpElapsed]
  simp only [lowPrefixWeight,holdingWeight,Set.indicator,guardedLowAt,Set.mem_setOf_eq,hs]
  by_cases hp : readyPrefix guard k (Preorder.frestrictLe k z) t
  · have ht := hr hp
    simp only [hp,ht,true_and]
    split_ifs <;> simp_all
  · simp only [hp,false_and,if_false,zero_mul]

theorem lowAt_density (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (guard : α → Prop) (count : α → ℕ) (b k : ℕ) (t : ℝ) :
    (∫⁻ h,lowPrefixWeight guard count b k h t *
      activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)
        (t-prefixElapsed k h)
      ∂(jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k)) =
    (jumpTrajectoryLaw initial next rate hr ht) (guardedLowAt guard count b k t) := by
  have hg : Measurable (fun h : Finset.Iic k → JumpState α β =>
      lowPrefixWeight guard count b k h t) :=
    (lowPrefixWeight_joint guard count b k).comp (measurable_id.prodMk measurable_const)
  rw [← history_holding_density next rate hr ht initial k (prefixElapsed k)
    (prefixElapsed_measurable k) _ hg t]
  simp_rw [lowPrefix_holding_eq]
  rw [lintegral_indicator (guardedLowAt_measurable guard count b k t),
    lintegral_const,one_mul,Measure.restrict_apply_univ]

end
end StartupCount
