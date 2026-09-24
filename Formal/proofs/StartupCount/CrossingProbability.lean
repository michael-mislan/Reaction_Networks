import proofs.StartupCount.CrossingSum
import proofs.StartupCount.LowCrossingPath
import proofs.RandomViability.JumpSupport
import proofs.RandomViability.JumpWaitingSupport

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [Fintype β] [MeasurableSingletonClass β] in
theorem crossingAt_measurable (guard : α → Prop) (count : α → ℕ) (h : ℕ)
    (a b : ℝ) (k : ℕ) : MeasurableSet (crossingAt (β := β) guard count h a b k) := by
  have hm : Measurable (fun z : ℕ → JumpState α β =>
      (Preorder.frestrictLe k z,jumpElapsed z (k+1))) :=
    (Preorder.measurable_frestrictLe k).prodMk (jumpElapsed_measurable (k+1))
  exact ((readyPrefix_measurableSet guard k).preimage hm).inter
    ((measurableSet_lt measurable_const (jumpElapsed_measurable (k+1))).inter
      ((measurableSet_le (jumpElapsed_measurable (k+1)) measurable_const).inter
        (((Set.to_countable {x : α | h ≤ count x}).measurableSet.preimage
          (measurable_pi_apply k).fst).inter
        ((Set.to_countable {x : α | count x < h}).measurableSet.preimage
          (measurable_pi_apply (k+1)).fst))))

theorem crossingAt_probability (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (guard : α → Prop) (count : α → ℕ) (h k : ℕ) (a b : ℝ) :
    (jumpTrajectoryLaw initial next rate hr ht) (crossingAt guard count h a b k) =
    ∫⁻ z,ENNReal.ofReal ((z (k+1)).2.1.elim (fun _ => 0)
      (fun j => if h ≤ count (z k).1 ∧ count (next (z k).1 j) < h then (1 : ℝ) else 0))*
      windowPrefixWeight guard a b k (Preorder.frestrictLe k z) (jumpElapsed z (k+1))
      ∂jumpTrajectoryLaw initial next rate hr ht := by
  rw [← Measure.restrict_apply_univ (s := crossingAt guard count h a b k),
    ← one_mul ((jumpTrajectoryLaw initial next rate hr ht).restrict
      (crossingAt guard count h a b k) Set.univ),← lintegral_const,
    ← lintegral_indicator (crossingAt_measurable guard count h a b k)]
  apply lintegral_congr_ae
  filter_upwards [jumpTrajectory_consistent initial next rate hr ht] with z hz
  obtain ⟨j,hmark,hnext⟩ := hz k
  rw [hmark]
  simp only [Sum.elim_inr,windowPrefixWeight,Set.indicator,crossingAt,Set.mem_setOf_eq]
  rw [← hnext]
  split_ifs <;> simp_all
  omega

theorem crossings_probability_le (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (guard : α → Prop) (count : α → ℕ) (h l : ℕ) (C a b : ℝ)
    (hbound : ∀ x,guard x →
      (∑ j,rate x j*(if h ≤ count x ∧ count (next x j) < h then 1 else 0)) ≤
        C*(if count x ≤ l then 1 else 0)) :
    (jumpTrajectoryLaw initial next rate hr ht) (⋃ k,crossingAt guard count h a b k) ≤
      ∫⁻ t : ℝ,if a < t ∧ t ≤ b then ENNReal.ofReal C *
        (jumpTrajectoryLaw initial next rate hr ht) (guardedLowEvent guard count l t) else 0 := by
  apply le_trans (measure_iUnion_le _)
  simp_rw [crossingAt_probability next rate hr ht initial guard count h]
  exact summed_crossing_occupation next rate hr ht initial
    (fun x j => if h ≤ count x ∧ count (next x j) < h then 1 else 0)
    (by intros; dsimp only; split_ifs <;> norm_num) guard count l C a b hbound

end
end StartupCount
