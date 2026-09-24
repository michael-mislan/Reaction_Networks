import proofs.StartupCount.CrossingOccupation

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem lowAt_probability_measurable (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (guard : α → Prop) (count : α → ℕ) (l k : ℕ) :
    Measurable (fun t : ℝ =>
      (jumpTrajectoryLaw initial next rate hr ht) (guardedLowAt guard count l k t)) := by
  have hm := (lowPrefixWeight_joint (β := β) guard count l k).mul
    (activeClockWeight_joint
      (fun h : Finset.Iic k → JumpState α β => ∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)
      (prefixElapsed k) (fun h => ht _)
      ((measurable_of_countable (fun x => ∑ j,rate x j)).comp
        (measurable_pi_apply (⟨k,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).fst)
      (prefixElapsed_measurable k))
  have hi := hm.lintegral_prod_left'
    (μ := (jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k))
  simpa only [lowAt_density next rate hr ht initial guard count l k] using hi

theorem summed_crossing_occupation (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (w : α → β → ℝ) (hw : ∀ x j,0 ≤ w x j)
    (guard : α → Prop) (count : α → ℕ) (l : ℕ) (C a b : ℝ)
    (hbound : ∀ x,guard x → (∑ j,rate x j*w x j) ≤ C*(if count x ≤ l then 1 else 0)) :
    (∑' k,∫⁻ z,ENNReal.ofReal ((z (k+1)).2.1.elim (fun _ => 0) (w (z k).1))*
      windowPrefixWeight guard a b k (Preorder.frestrictLe k z) (jumpElapsed z (k+1))
      ∂jumpTrajectoryLaw initial next rate hr ht) ≤
    ∫⁻ t : ℝ,if a < t ∧ t ≤ b then ENNReal.ofReal C *
      (jumpTrajectoryLaw initial next rate hr ht) (guardedLowEvent guard count l t) else 0 := by
  apply le_trans (ENNReal.tsum_le_tsum (fun k =>
    one_jump_crossing_occupation next rate hr ht initial w hw guard count l k C a b hbound))
  have hm (k : ℕ) : Measurable (fun t : ℝ => if a < t ∧ t ≤ b then ENNReal.ofReal C *
      (jumpTrajectoryLaw initial next rate hr ht) (guardedLowAt guard count l k t) else 0) :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const))
      (measurable_const.mul (lowAt_probability_measurable next rate hr ht initial guard count l k))
      measurable_const
  rw [← lintegral_tsum (fun k => (hm k).aemeasurable)]
  apply le_of_eq
  apply lintegral_congr
  intro t
  by_cases hh : a < t ∧ t ≤ b
  · simp only [if_pos hh,ENNReal.tsum_mul_left,guardedLowAt_measure_sum]
  · simp only [if_neg hh,tsum_zero]

end
end StartupCount
