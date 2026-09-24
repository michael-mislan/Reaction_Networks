import proofs.FiniteCopyReactor.KilledChronology

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

theorem killed_observable_mono_region {α β : Type*} (D E : Set α) (hDE : D ⊆ E)
    (f : α → ℝ≥0∞) (T : ℝ) (z : ℕ → JumpState α β) :
    killedEndpointObservable D f T z ≤ killedEndpointObservable E f T z := by
  apply ENNReal.tsum_le_tsum
  intro k
  dsimp only
  by_cases h : (jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) ∧ prefixAlive D k z
  · have hE : (jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) ∧ prefixAlive E k z :=
      ⟨h.1,fun i hi => hDE (h.2 i hi)⟩
    simp only [if_pos h,if_pos hE,le_refl]
  · simp only [if_neg h,zero_le]

theorem killed_observable_at {α β : Type*} (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) (hw : ∀ k,0 ≤ (z (k+1)).2.2) (k : ℕ)
    (hk : jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) (hD : prefixAlive D k z) :
    killedEndpointObservable D f T z=f (z k).1 := by
  unfold killedEndpointObservable
  rw [tsum_eq_single k]
  · exact if_pos ⟨hk,hD⟩
  · intro j hj
    exact if_neg (fun h => hj (endpoint_interval_unique z hw T j k h.1 hk))

theorem killed_observable_exhaustion {α β : Type*} (height : α → ℕ) (f : α → ℝ≥0∞)
    (T : ℝ) (z : ℕ → JumpState α β) (hw : ∀ k,0 ≤ (z (k+1)).2.2) :
    (⨆ n : ℕ,killedEndpointObservable {x | height x ≤ n} f T z)=endpointObservable f T z := by
  apply le_antisymm
  · exact iSup_le (fun n => killed_observable_le _ f T z)
  · by_cases h : ∃ k,jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)
    · obtain ⟨k,hk⟩ := h
      let n := (Finset.range (k+1)).sup (fun i => height (z i).1)
      have hD : prefixAlive {x | height x ≤ n} k z := by
        intro i hi
        exact Finset.le_sup (f := fun j => height (z j).1) (Finset.mem_range.mpr (by omega))
      rw [endpoint_observable_at f T z hw k hk]
      exact (killed_observable_at _ f T z hw k hk hD).symm.le.trans
        (le_iSup (fun m : ℕ => killedEndpointObservable {x | height x ≤ m} f T z) n)
    · have hz : endpointObservable f T z=0 := by
        have he (k) : ¬(jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) := fun hk => h ⟨k,hk⟩
        simp only [endpointObservable,if_neg (he _),tsum_zero]
      rw [hz]
      exact bot_le

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Increasing local regions recover the unrestricted endpoint, without a rate bound at infinity. -/
theorem killed_chronological_exhaustion (height : α → ℕ) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) :
    (⨆ n : ℕ,killedChronologicalEndpoint {y | height y ≤ n} next rate hr ht f x T)=
      chronologicalEndpoint next rate hr ht f x T := by
  have hm (n : ℕ) : Measurable (killedEndpointObservable (β := β) {y | height y ≤ n} f T) :=
    (killed_observable_measurable _ f).comp (measurable_const.prodMk measurable_id)
  have hmono : Monotone (fun n : ℕ => killedEndpointObservable (β := β) {y | height y ≤ n} f T) := by
    intro n m hnm z
    exact killed_observable_mono_region _ _ (fun _ hy => hy.trans hnm) f T z
  unfold killedChronologicalEndpoint chronologicalEndpoint
  rw [← lintegral_iSup hm hmono]
  apply lintegral_congr_ae
  filter_upwards [jumpTrajectory_wait_nonneg x next rate hr ht] with z hz
  exact killed_observable_exhaustion height f T z hz

end
end FiniteCopyReactor
