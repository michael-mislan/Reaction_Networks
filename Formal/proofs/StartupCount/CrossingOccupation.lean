import proofs.StartupCount.CrossingDensity

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass β] in
theorem low_density_measurable (rate : α → β → ℝ) (ht : ∀ x,0 < ∑ j,rate x j)
    (guard : α → Prop) (count : α → ℕ) (l k : ℕ) (t : ℝ) :
    Measurable (fun h : Finset.Iic k → JumpState α β =>
      lowPrefixWeight guard count l k h t *
      activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)
        (t-prefixElapsed k h)) := by
  have hm := (lowPrefixWeight_joint (β := β) guard count l k).mul
    (activeClockWeight_joint
      (fun h : Finset.Iic k → JumpState α β => ∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)
      (prefixElapsed k) (fun h => ht _)
      ((measurable_of_countable (fun x => ∑ j,rate x j)).comp
        (measurable_pi_apply (⟨k,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).fst)
      (prefixElapsed_measurable k))
  exact hm.comp (measurable_id.prodMk measurable_const)

theorem one_jump_crossing_occupation (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (w : α → β → ℝ) (hw : ∀ x j,0 ≤ w x j)
    (guard : α → Prop) (count : α → ℕ) (l k : ℕ) (C a b : ℝ)
    (hbound : ∀ x,guard x → (∑ j,rate x j*w x j) ≤ C*(if count x ≤ l then 1 else 0)) :
    (∫⁻ z,ENNReal.ofReal ((z (k+1)).2.1.elim (fun _ => 0) (w (z k).1))*
      windowPrefixWeight guard a b k (Preorder.frestrictLe k z) (jumpElapsed z (k+1))
      ∂jumpTrajectoryLaw initial next rate hr ht) ≤
    ∫⁻ t : ℝ,if a < t ∧ t ≤ b then ENNReal.ofReal C *
      (jumpTrajectoryLaw initial next rate hr ht) (guardedLowAt guard count l k t) else 0 := by
  have hs (z : ℕ → JumpState α β) : jumpElapsed z (k+1) =
      prefixElapsed k (Preorder.frestrictLe k z)+(z (k+1)).2.2 := by
    rw [prefixElapsed_eq_jumpElapsed]
    unfold jumpElapsed
    rw [Finset.sum_range_succ]
  simp_rw [hs]
  rw [history_reward_absolute_occupation next rate hr ht initial w hw k (prefixElapsed k)
    (prefixElapsed_measurable k) _ (windowPrefixWeight_joint guard a b k)]
  apply lintegral_mono
  intro t
  dsimp only
  by_cases hwin : a < t ∧ t ≤ b
  · rw [if_pos hwin,← lowAt_density next rate hr ht initial guard count l k t,
      ← lintegral_const_mul _ (low_density_measurable rate ht guard count l k t)]
    apply lintegral_mono
    intro h
    have hh := crossing_prefix_density_le rate w guard count l k C a b t hbound h
    rw [if_pos hwin] at hh
    simpa only [mul_assoc] using mul_le_mul_left hh
      (activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)
        (t-prefixElapsed k h))
  · simp only [windowPrefixWeight,hwin,and_false,if_false,zero_mul,lintegral_zero,le_refl]

end
end StartupCount
